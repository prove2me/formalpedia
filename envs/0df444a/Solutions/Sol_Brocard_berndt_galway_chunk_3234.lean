-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3234
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:03:52.08369+00:00
-- url     : https://prove2.me/submissions/d60502e3-e31a-42ab-b78e-0394470f1586

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 581474820 ≤ n < 581654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 581476070 1250 581474820 581474827
    0xc0d1a09060f070c03181806050411090603071809060905070206010f0b0702010216080a02010207230405090a060c05040f0f1202010507020d15020702100e22090b101712 74
    0x1001601c160360390745020340402031b9800090f03041c204240c0301e2000401150345000e01c2200c1206950084811903000726210b01d06000e22814402d25403000c0d5500b82a048071261350342d8843e407038281c810303011707011741940b070700807100c00000d01883c1550000d0200c0d45031240c1031280c0d542e1404200d844090074090140602c4808600340148100c0034013510740701d403040c0122607161446140d1703036035100307503d5102d100da590107540d111086590600c40c4c003004007901c8812111101428584070715485260003e41d0003203a41c0e5001079255102000081d0506030080800c1180c4c40030700703d00512302e9009008400d41c6007c610c03000140105c0e04000441120215000e0380c118142e02d078011a0194000082030f03900001303540140c004030351014950745d00e002d68070780c005035210303042c0c41804540210010440103002c3c100c480c10203c0e4680b0309140c100403004040d03030980850b12140c55001083d24090150445801004001c0001844048442550600c224a80010b0b25a0780c84956a030101207a03c60400e0003070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 581477320 1250 581476070 581476081
    0x504020a1401021c050c0604050a0c05180c0a030204030209100e01150c14010b030304081b010302090f01030905030c0a0501050f010506030c040e0915070f1107060c030507050c0d1a09060f 82
    0x2601c40464204c1d0361811034501035925080c1c528019095600381d070660041060f0208002088804000415054910003501e0142080480b881070004041d007221031000200c1e044158031a0f81150013455004042e60341900b0483d00c1c00b80c10210b64010b42040c0c1c2405400860034424500e003810610429035035079121300707001d0f542d11030701c2c002e8514103050159201c4c240d00c07100f5901800600043e01103640104043c40c410f04c0030810007400c0c03d000714185441048501c0040c1c56820500070700c10703420701300801c0241d018038285155104840481c0500d0056810f0703002040410f402c5540900050402c1c0c1c011a42c94504000c80c912050f07500144a000070042000a130100c01d140c0d41d030000990060700c00420036400a5655440d0488540c0000b0b4400c46441c0c3d00190810103801a200401c00109102d07420018003500c16080303264041c06012011035080100b050402000c03c1c1c01d00003500c0600810303411324042059175900d1000d00342420401d0001601c00d4000240b29100d141c0c0701e80c000c0f107652100d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 581478570 1250 581477320 581477353
    0xd09120809180403020f1b0d060b180a06050109051c0b0702160e0a0c0309030207050609040612060e060c070b0c09030a0b0f09070602030304170f04080f010504020a140102 75
    0x48401c0da080121940150220401c0300c042e58400c0c1c0c00ba130050421500088411402d20010b10003102101e20700843c1121103444480c00c2072501c03503105d140010303203441a60005a1650440b140c603151206540304010a5529540094044903005e0300c50401d020384550400c480d07401305180c21340c079918501c12050086140303a6402900900a40141d030705140d4481603c407004411074119000108021061110240d10b5214a006084161804006410380c40d41d00940300e01c5280b043c1d500c103a40c0820580401e503215032018000b41414402810900c130907180c0000134040e080b402031a1030080d000060014800d880440303506031342c000c441090036910401c0960854021980058052040c820307004d000414170b08409010b80c3d402d05111100e4a4002411840c000040d04414215001070003800009a103e1042c4103208441405244d01c4006102001c10b4900450b400021f00380302d030031a5005050810340c00030780194001e8503100500c035120f0401141c900c44000f68140103034482c40988800000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 581479820 1250 581478570 581478577
    0x605011403060645090708090604080a030e100b0f0d0809150d0c180f0609050f06070b150a150f080907090614030105070809190503070b0103030309050d091208 70
    0x58035820110314a00c22000c5038206402e13032849803201c1040c800d540c03001d440c1c00c0d41c80d26445040717803034111074034501140e10a80310000900010080303813000c82d02c242884d000e90003614a8402000031190300094031260580680380840f0b03002d0150010042da0481c904028908049075900801e04a1078082b800050040d50440c0382d10f80c01164100f88416401081c16020705000c0f01e010341d4a42440742c0b150f072148100006c19901246004040340c0742000500d0300a40040d00700c80c0d048800400803000c0c1c8000c5880e41c4200c400c01080c000221080007030980c05205038900010090b103400440a03111268114200001084000810711141201003401d209403262a0302c02c14400aa83e4400c0d40c0758a080143c3d0801e800544201190502044042c02e0911485912006c0c900d003224170383c200382e9010382d150501d4403540c00c04980000140c0c000d00400b04215143c141e0310004421241d81e4078100200201882c041c100c0d014003071005d19046040c40307803240d00259500e032910103041010076950854140d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 581481070 1250 581479820 581479867
    0x100504120215040312090603020c0d08462d0f1e0b0409020a060c060e07060518030d090504150e0406020901020d030e030702100201021b0106050114030606 68
    0x80003001c618000d040001c3d10085100d01070505404414440203400c101064100c0c1c0308240c810b10001d42d500c140022200c1c41c141c440e0820a04030b469246881603080d2095001010203d43c940081080000002c1c1d08401a004034200300d020030844103440b002e8801601c0c030078001403000300d221501361a151046804c10a5640c00000303c03900b6070328010081c0d820f005a80703008640d983d102c035800030381240a03800228500321003c1100783c0c42503000800b4605070b4061601000a040c41000411038198000d0f8a070b1610700b000c0b54400c59440c1001011603000d0b20f2101c164000c880e80e20109401d002a80304004c2003140c40c2c1c02022824203041c0070061005c8a000003503000466400181500305244c100d02440c040d41c00580e84101d4607002a02d4941c0c9450043c042600e40001a01c84203004002e85040030f80c11a807025021190300c4080303002e40501d102c008c80000051105e00c0300c9000560140046800c00e8031001000c102e9445255000d000803250107030410801c1112540e200d9024400b009440c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 581482320 1250 581481070 581481079
    0x1a0c0d08041a0c0a1d120d030f020403080301091e021204020a06170109020307050d02040305010c181a1605011404170408060c0c19030305011a0307022a13090605061005041202 77
    0x40717400000290040d0345499501499401900580c44004e0b81030151aa2800001d081589068510754a00e04248014030801c5800d90f5114000c11001c01810b0030444141c001c0f200079034490100d00074040c401c0c502610f04a111301d14007000020640e01440c040c0700440c24034209003100c0d0303203020b4440000c0d6200401c18000c0120030800425424014030242c400341d40103600000d000f8081d041d029001d030420256080d5541c0d03c030003041000000c0c80503545880c00c10581d440d61a4540007245c0119141904401401542030400c000c1c600c1c1e010200e824400c0303008904803007040c405204100c480388902c2c02034441d140c205a000a5a90070440001c0008100100031102958464603500c0050b00c0703003d030102d00082e20f82c0c004101200c001c050310026100c00c2510189075080c202000b82d601c01c1000c8650043c4030159005c0010400900303a0401c41203405000c90001c0341d44045e00314002d100a0702c04446542c0f030000824103e003066210f203800003020380c40303136480d0034280035108030403041e5003200b00e911 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 581483570 1250 581482320 581482367
    0x170109080309010e071719020a0b0c0f0d02070e0c0706090c060c031e0f1b08030709030606050a120311010b030607030b010314040b0402091f030303090308090a08041a0c0d08041a0c0a 80
    0x2b0646a8802008220441009003615840230b180c1d40d400e04c1c5001040c582194414030382030040c3c5403840707215a004640a42615070310410b07441c008000c1e0402c0000030b003041640d15000501075401140d8114000c0c4039903104d040c055843c48045507880b20341d00c507040018002f07074600c5180901401000182c1049640e080c4901511540c0303005850b40115183d40015461000420400c04e0500454019000403100704028a05003100708190900000014040280005400c070b0000d03829448101c9182c000340a0301c100e0300c3c001501401a0480940e2070b80041d01e0820040e03c414420100700c5c0c0155404018182151125000c1183c0310f00003414208000610002c002e5034400b0b02141c400084d41720b0384001c50040d00344d05019240f141d004044149503082030022000290226003203500388e400090080043c03422402c1020494001c40c01c2824031481070175400f02c40d1540169041e44514861028640740c0c000e80040191709040035541030401a80622882925078092410907498142d00a601c00c030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 581484820 1250 581483570 581483579
    0xa02010e060a09030f05040b0d020306010c02090403200c060405040504050f070303021c030b01021f09021504141203031306090203100603061a0a170109080309010e071719020a 77
    0x82001c25146101c2d0940e0b00c0314100d08241e006050005400150305203581040d250034038112141c400e10b954242540d42c00000100340d680550400021950003500000c0e19160515014000940c28000b51051a080034001030940390300080030710081b40094005070030301b803030300c8140006800042c01c00c844030b004103030340107100d5401080700c5c0c001180a54000c0c40700c400b207841c0a16141c540001c0b000101402d1540080c201c0e40c00082c030425601c000700e10828880c0c5018111401007800003002548803040c2c042010050380c542015009440f080300c600c08508208000f0402d80c04103c02130581190000d100103403042e200d0200d60251580110b20128030100994000382c00d0412900c10580070558609040c801e02085201d40300c92031781d174034800c1d08002c0c03100d000042d11040d041c41240140c240020700d09400c00000c0d0000814180d01203140350712400d20001690190413041d0050f0424400d03154006000041181d02c604246100c50241800300038030b99804050b4680004141d13044240d5020029 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 581486070 1250 581484820 581484823
    0xd29220e0307050615040606020a0b0421030b1804150908130605070c05040606023309030c1603030e1003111602030606060f22080a0b0f1b0f0a02010e 66
    0x80c0c00ca100c0ca002d00005e142c0548403e07a018600c0c0d180c40d0069103801f800380005034002485410881d00404441c007a0768682c50825040704c500b1139000b51015150600001d0680c0581000980140c100ca2401c4206030304522900d507207408480c0500940070348403004040e120303039078024102603000305d41c040d2134200d011f88881240e0025030b1284002440000f000b1061100c5140018090301d030445051001c9850018020f544d59800c40d08060004c0030240d0829040c3c90002020300d005010804010311441e0a10500b6200d42140348080c09070b0103000e54850001800000c0303802900da042c1c8491005030500d0003070001000c80e4007014420306980d40700800b500ea07550f030082d1116a4251504402844151060600b086009000e290180c0e4080c000643c400740000c05840052042502168190400d01041008a41d1540c401e0655002e102400302c01d000c1c6801040348612074000392100d56841e80c080106100c0d801c50b0f042840c0c16001d11502218140c85030003015114024400403c1c203100300d00310503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 581487320 1250 581486070 581486077
    0xc0d031e0e1005042108040b0f07062c0106060504141207170c01021b0103090c0b07080a03060b27060f0f0301050103110a0206011412030d29220e03 65
    0x14040383d00420200001842030a03051581042040c0c0f5000c3c9110b10340d61300c00c00340210f02400808103404100200d080040034141d4600580118050004440090440000d13001c0c0d0042120380c07800101c926900c01805001e160225925662401d00d0686000c0d2510341c00c01c41080040d5101d1031034014030082c81c0d020090b030b0f4007405a41182c0450380380d4030382c941480e249044042ca415504404041120b503406450090450307007007800c01080c07204042c50b2559556000d40c101105000001c0740d60340074460702c600940a84050351314100203440e22501d82c10054012020610010300d10f00505400c00901112070201005001d800281880009107004d0a030303401441e031074920000f003c4010003c5680c107000c0e42000010794402e541c50040920b00c02500e0300780c14014030340040e0a54003110242d403681c5018170110640b45041da601c3e096442d01c010060807020b16103880c0001e035180f0508200c007000d24024080f2000418030f6100c0c11011100701203860b0406002c2d0f50f465501c0b240c0031001001031005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 581488570 1250 581487320 581487349
    0x103020c0d02010516090f140a030b0a0506130e030304060f110a0c110607080d18060c0c02040b030f0d110c0303040803030a05130c03082b0e0c0d031e0e 67
    0xf00d0a45804801c100d290f00c40d4805c21010494034410400414084004d5881600c000c42900131480307100c1804203107090b00c150b100a00840c0e140c01040442c03030140e401640212021661340c08150880f0285400f45d4200080c0d82603941c0007000801c0c000340d9150b10256101c0c01342c81011894112202d0903005940060f81c0b80004660481c3c6403104204501001000002c402c45500d0305042070b54455a5450107039402e221490781e50341c80420000c1c03180324006010198081d105200c001700c51f040c010480d86020100724003036403c000c200c14482c03a0106425200d164024010f0004102113001101c1e0300d18040d250340c0c4640641c04600e4021744051005002401000c00210340da1300700300b84039800300c500c0102094108801101440d00280761003000e101120740001c0c0c12611000c0328802707624640f4007498100c40c0d45002218520004103a50411502410903000741e80d5040a200140182c62002140083c0014000f1108120410b10a80c010900e0354151805071210310040001c900f216950110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 581489820 1250 581488570 581488573
    0x1810020705030601091505150c01060609090c03092109030f03050301261b04020d090c0f0b1305100c1514090c100503150303040e04060b0607030206150103020c0d02 72
    0x18001e50804000141c0140724408040000c11805001c81c0800a0f840c01518881c1d609080d038102c0001201040c2d83d900c1840c036008005040e500e450140400d5928400c2d00758503810102c190f2003085c028031134aa101d54100308410351030f43c8000c0d40c88100364500c0c0e42c40418041a0140070001c03c00d940011150548241c441c281d495040c41030901c1600040700c00c014490002c24001542d00740007041c1c04030300781c400e100c120900c0361100f40002c000e805902c02d4080100e140c040c4030f8083c000700c21801c400302c0d0661071408003a640c40d503100002c64803514013a10b44034540000100500d00300f8400010700c2c00014035045160041c1d5541d542c51b800050074078044010303122071007e00e162001964642d00042c01000a00c480140400442c4407240314142c408248200400021541c3c03100602990038410b00500b5a5030f5107880c2c90070700e90208425102540e60070f10704000c00d1840e0030400e08850310190140c0040c4010780e1002103902e80030000b42c2d02d01c2c0c10150248001840078004000000080350140c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 581491070 1250 581489820 581489833
    0x304080312100f030804090f02160c0306050604110f070303021612020c010e0102100c0e06073507060c14161104061503020c030f070c09180b010b181002 67
    0x41c1c2c8404200980d400c10441c0e1500031100700001a072141c2242c1c222860794070049150480e01604000174021031540d10401030f00300301031504000841c0ca030303141943c6c4590b00c200000c0c0c5072802031104680c0344000b03a4841742001c00c43c520350009084050a4110310234134000d4580818020301801c1111000f000300c680f80a40b0307615130001901440359204420b020b207480c50318007201000003036030348070f82d8081120101d98982134a09080d204002404240001905807070ba983c01910742045048035803401802c1e50122480194117054082d50000040ca0603030015134141402a1241c600625517200704c0d60601c07070182c01d000217556682018040b0750341861000002c142c0d550908001000701c00601c0c5100e14074010b420b008190010702d07140b107400791624006858140c1041d4682c83c502c901808410381802c0421417000b0014012034103070980c0c0305004107200c2442000060781c80504901e20007030411221800503c9107001d46c002421200007070002e2203c4450b131000200781c0e108990209180140c0294 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 581492320 1250 581491070 581491081
    0x10504054c0302030c07022103031612090330110910020109260702120309010207081609051e0108030d0c1b0803070512010905010f0603020315060c0304080312 70
    0x101e8032600380002800d0561031032501003249a151310070600d0082c803c1d89403895030307110000c1ca404980c3c464111101103035500d05100d41e920035680035103c4003000040c1c4003115000b140c2000d0207030b07074501d80d4140c42e0129807412036489041d00c4011008040d000800368000340c011025140145101c00f41210b40c02551000300e601130101c1c00345000500e1095a06004031000040d50f109010b208a058030110001a06245403043c00070384500c02029500ca64000340741c9038003220100c000d004c000c400341c080300c000d255510321454036000c2c02c0c0c107040004451050104842c21858100b2039109210300071051101e400c1c583c080384030000030303046000c0035030002c50b07031140f0090740d40700f188a0180301d03060100307125450040c0c203081020300000c000c01851001c404103d00c640aa0243c0301110160740b40c005007903031510020380007080f00b48a1100d441d0700b05030000440320300070301c02c50740201900005000000700304004c2c009140e0001c802c2c2a41c03803004000000d090541803014042c00d03100c1d070310410b0707107030400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 581493570 1250 581492320 581492449
    0xc03050f1809010522020a020f01020f04050a15080c1e1303020405070518100c050d1e030204030302060633130504021c0e011404050f0708010b01050405 67
    0x51308800d000d4074101924414022140d4200340c2c03100384030f20000d6035461400400700c1c01c0c900c100d47e0500103503001258403100124880040c0c41038610540e03400c00c0b0180c1d90101c4a450040a40040d008501005c000c80d40000c500001810490201101000703081c0c840c0d0703103131f0b00d140e40124071701c40d03006c0442c4a041c0110b103400d010b17050704803c180c0350882c10500700d00c041d80b206000d0340b803140340f00766503000d80341990324014500104a00d030020241c460724070b05803101070103058050110708012400c640c506100c5a00910940d000d4a405500915082d07450006114142c050001d0303803140800500c50004119803105501414010950b0340c11361254032521841c09540011340200d441940140502d100c140703403406c401c860b40700f4013a030041384451820f80824018404400d128420720407203030400040c0000001c1042907016032000b00d030f0101d0355030307020582200c094086850010307100f08010051450703c819080030b0200c82100c0f1250704200004503c43d035108407400c3d03400c00b9440d030781d0240c00c0496 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 581494820 1250 581493570 581493589
    0x2502060d0507080a0501052805150415080f1f080f0106080f070503030f0703031407030603051c02061803040b19021011040e130c090213050a03050a030c03050f18 71
    0x9201001d0026504010004480c100300d01d03c14a0102900203d80d0210324031321007148020301d404ac24000c0100f400f406c9108465000d4000c04220200c60502850036600c59003c00d8070441185101c05140e071500900c805000c10580603490b0b1101c1c00b0307200811540002c0c040001016952400000c0817072500c2e41c1103040455980760051640c120b00801c0086440c04001c41c1d000c820004c0c4043c1d904c080918050340180f504080481b1b020800300c0410100348d416074061402d50b4016001c854600c0300c07400e00344007240d00d144240340050b00054086140030b41c019031150711040701c9600f52810161100c400811980261584a50405411182c42c2e00740740c040c46980995030024500b0301c102c14140c5400103052146224020441c108240000c0c0d10300704040307000741080e82c0000903903241c0b0790f1540d142000c2d4110391703500640c0460f80752000485244c480c00c0101200e038884081c0140300c8080e103095413140074184054060000030407012026010040007441d0322001009138960144d840c1d0103200c3c0d00750 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 581496070 1250 581494820 581494831
    0x15030c120709232103070606030309030c0b09030a1203021b0705010f05070b06010e0a03080316031a0d080d02042112050c0303180102040519090b0402030c2502060d050708 75
    0x401c03c031056403143d2226440c01d40500c3c03100d0464024205403401c1d96146200744403000d00500d01d803000200401d0b91141c0341000b101e0103044800610b0703440740410703ca0380c030800d11125031581c8851455030004169860f410362001c00d50500600740b003082480d200c0848c401041030105c580060401b80002e6800003524020488103241590a095095555812071000030380f0f460305105005010300042c0d46e0b5800e80300c02031030380012204e0b102c2c20b004c0c145500ca004000c030a4004039040c142400d0032122034000f0031004240003401c2c3e6008900d191211740d11648030101c65000c90b6000c010100c5d40102a80f00c3d1100c1403580c5a015011810340d04001704c0130b4100000b88020001e0810502c800c0c3c0c0c00000981c0c1c5c1021002d03460303400004000c0d40305402845254042c5d600000302c01d0742c100141050421020450b007180ba000d001c0750180784200022448103c5217500c0780d49007400307080d01c50481c07000ca060789421810035100715286190000340c40d80e00010140c20155846101f0071080c40d42c48003140c0d8110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 581497320 1250 581496070 581496119
    0x2091501050403140709110d0506030c0312070f1a0a0515090402010e04091b05120a030917101b0e0a0b0f18060409090b10030215030c120709 62
    0x1090140009101c2e02c282d10025100700c0c2410701307026500b00140310b5400144007480c000c01441e09840c20142c03403600190310642c0207918190004a4608011401c100e8440c2c00502822000014805460f5203800c0440281c95a012048903000050f5400000103074400804000050303a00d44100124144c4200403c0c40440400c921280952502c51411a640150b82402e1030780400d49408003160040103c0131b8090f0441032104c0c0350072007060401120000f52031040d90300090800c800c045050b070b6941072020080c0044d5810004100c501e801c001d0a646042c0b441e4150313804010340f40d0541c0c09603500c520401e059008421540c10240350450040000d40030241c6126121905c1c00c0783c0b00c015070040d52120750340400005030b4000501c01c1040301a4407103000401403030307d840e140ca00000050000b414126250041c0c20085804258154440000c413540242001460a040c2440040039000542603d2104030140181f068444415070440e200b00c5241e82c41ca80b40a01c1c28001c580f00d00c80c20780419920 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 581498570 1250 581497320 581497351
    0x1501060e06270301090605060a060504081207140d03050a06210b0703020d1404060e070f05060d06030f42090314030a0c030501050f011b03020c040f0203040209 70
    0x454452506880344500342d0400307003041da80c00c904421881188240c1d00d5034154138080030b1608025166201a001d0032055625101190302c034581594144602d014960300d503480340c2c03400031504810500030070030b252007030410421101d4076404003850032030000c550300c000c80e860b2030802c410b41c51a4442c1030000c0c05202c0ca02d091b032500294500d0000c1c049100080c0070340642200049000d400b0f6011600c072060000020405a600c1001c028206001030701c04403885800c0484807e01c049d000641102600c2180282070320b000d1501d4100413165210313459411210f51200000070118003116245480140240e0210411b40309a00302c03108a540091040752070b580b1142590759280c8000481d140e140d01e070044001071861414241924112881c1c003002ea0f4226001040019412540e00076620100e06a02d042c400703a602d5100300f02c0c074100d4003114030f400250060700c80407000700c00070581c144850107030060302d40303203c030600200e03041d100c04240350b00f4aa034000080c0700840c285a15041d42c40341d0000e410209 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 581499820 1250 581498570 581498597
    0x8060d110103150f090207051e0d08060415060309110915060c030f0a0215220b0403030b0a080f10060f0513020d0f050105030c0a0810110912150106 65
    0x29480c403280c04103030400d83e80c1c00c0d07640002000f0985840151041825a020395580c41da6210003940c4101812101130040482d403501c1244a0000c201e0000e104c200500200071403040201e501c4c1c400105039950150b210b29111600d80c45101201e0f02511840d03402085142840c2410390001400d0804c40c2d001b104a1000c0042c5c9088401001e03106541c11940e41c0d943d036401500341480c501031002e4440c00038000241c0350691540015003206e44407d0803401c050195205918000b814105000c013841e404100c81102000641d081140c4d03500c10302c2400c002442c100030102061203110740760090347c06d03580811042680c1c2c3c0020007207005c2201d4664401c1c03007880e06220514103005620b1186c0340c050035012505001d0001180c0640c1d4002004c00d604000a0901c1c40d0910040c260a1007590f02902501c000590030b030404c0700d88102902d008400803c440f4500c0071f90b410042900000b0000c08e02760a0100140c030f5542c0c005121805c01c4020004c1c20034a01030092030a603007a042c2e05c40c0c0144084010040d9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 581501070 1250 581499820 581499833
    0x1f0605030d0c11100c05060a020301030c0806060d061e09120908031305120a15380111010b06120f0108030c0c06092806080901090201020601030209060f100306050108060d 75
    0x82000136900c0001c004000e100c2528903808503000107129001e110104022401c96501071412240141c40e400400340d0768240e03898840342c040d00d0060b04030a220070000c02054464120701c1c8030b40a8220b00714100c116240101b4111018110115100c80010f8511140e0070b40c42a04c91015280c0c220185190590342e168111444109110f0280150740382c00d01030042600620100308c1c0e080d0000039017452680e4801d060001040e07051100380981c41080103545013125440314041e01000b890b00000a0000c1c0f0000540e100c1d8006a4262015901c2d905002c000e529032901600050118104401140c01d250311030b80f5100c80705070452202d6138820f01c416071703d4007400251199503580540d1429500c451540200d40d07480c10030380361091319088544050400c044090b08910484125598221407610b40ca4501801e030b65152030047d006030300420051000d403400b2404180c002c04d00502c071105200c0d074000401d00b032454042c0c1d0311000c260350b000100429608004050781c406021101903898046955440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 581502320 1250 581501070 581501093
    0x30504061b170a140903030105011b030203090108040512180a0e060d08180406081b04020a0c110307030609030f020c0a0e0f06191205150f0103141f0605030d0c 70
    0x15440c4824641c0410760034203884d400f04046040200c00b807980d40c0b604440d0380340d803a8000e21803540000c110000780e100000c0c00901c02c01c1d000c2d80c0343c0d01841c9000761010045580410280040c0d440d809845050340c1818880300080503426184522543d030040701d0410840c8290156200c4030480710020100b0500b13543e0300e43c4001c9880d510071055511102d400500a0007440900d0301d4a03041817801c8004510a40c0009030442000e0b43d03c0ea61008000300d400911047e40a02807002000c141014070850000b04903c4c110070400324003400b03d44507a40d49488800641e04c4103c07042c0c010880d20800313900c0c1950b0502420852010075914000303c64501b81315020903070b0004283d211916610700101c0c0c40f0f17070b03110040000b01c0c1824018603d03c05840360b030100d20503c1c1070002100d6510038560368002c4204008240751103a0200c8a0b20038842e840c0d83c0712488005050806655240a8031000340c2101d000c1640184c0100c00c0854000b45072410101418640541200e2a40c01d014402131440700042c0d104c1c054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 581503570 1250 581502320 581502347
    0x5010b0d02360f030c0d0f0606030c0e04050607030c05031515070804030506070906080f041e150c11030f090105070605010807050405090309030705011805030307060c020c0d0804050904140d030504061b 88
    0x400c1f09003201400c000d401013407980c200600c007035040350b07000903440c54520907140554026000d85e00e040d12200e1056040f05c02c0f1070342c0800810320a2002544403500e001d60b446c40701c1005007080b14850621341401605a000c0c410807a58800041024030038000d0804c10107070711049a05150703a003a420b025003e4503024009140c020b1510704580000d0400610441c6e00c00b001595010a2031807894a290902d1015500c1d124000203a01c2c00510708241446500282c1400740b07414041c0d403409001c001c244c00307a5800300a1450600004010401c0040d04910589000300300700400b03802d10900707120400c4142c0b44c000d40b90b110294002c0c003a2403041d90340491204100c03202420280c074000c1320004024820300180c0d002c00e500d03001c042248428000c6035000700301d1000559007510416411901040280b01c02d03003101800180c0288824020b40c105104400d400c54042c4c6821200c00b50b40859103441c0c15181d40080380082c1d181c00c00d0004000c03c44c06032500000720800c91002c01000350400038000000b14a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 581504820 1250 581503570 581503583
    0x1101081833280b090405010c0e030a020f120304051c0302070923090c0d030e09010501090f0608190c030b0102011119080a020d090f120305010b0d02360f030c0d 70
    0x20b510001165500c4082036801c042c058a68502e05410903074000d120005006003c01c036078100240c00c51402189a4420650062200a0030844542840301c90310503400b1828462000300004619655120304288003445203801604401c0c50703610b0004c0c1030090581c08040424100088031018030000b5500b40c0340c099917045805c50030f07603400c4443c1e841c0c0b41a5017003440d000b0b00d801c1d40c5a0149a48041054200c07802524980c100d0b0b41d8a10045441003103d10629801000c41181400310500c46c1c046641c10141940030b02681c40c48040d550412501402e04100202e0396901480815580a000328031145c0f01c61554039042000e1440907104a90071150250104103005000a05907800faa045e1a4400140c1340d0410010800341350410455580c824252202c50b00556400301c5184a401a541038828034440c55040c041d240142c2c10107504a803680c184621007000c07106006121250440700c4003464400020000c00d086018850b040000c3c10884c4d0081e0001c911444e260b07200c030b010703d40c1d00316800071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 581506070 1250 581504820 581504881
    0x30a06090b0d080703030f0203010f08070803040b031f1a0c0f060403020d030c14041d15130e150702030d06090b061818070f0e06071101081833 63
    0x14041b4010200410343c051000d00c0440082034aa4400d00c03440180c03684601114191600d0710100f95407400b8610840c1e858240410000b46e000c0c83c6103000c02502c0d500c0041c800001521002140c0320003e0501c040b04001c2c50204512104503030401012070100d00102c090115401d190310000d4031101018029000d00d034980c03010384082032084c02124000f0921404039a00d954a0304512049640d5891210600703844a0000c43c4031048012050f5868610007050b1885800041d200d00b005048040c02c0c0d00d1032402041201c1c2d0142c0045859a44241401d60140d651071a2083c0c0072802c440341c0b90810202c803031800c0c118003901c2d15030008842c1244c011282030b070707546c1240c800020301259500d0300b94540c0055802c148035003160130210402c10824951200c20b800081c1e80b06001043c000d00c00040c1000100d0f4000b81d0055000364402c0d40c000d2600c8107180f078891012003c0314581900b060800071403043c0c002d60300f04e5600e6400710a00c1d449030280360940300750400350b04194003490041c80031380a441c0d991 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 581507320 1250 581506070 581506073
    0x60a02180a0311030c15120c160308010314030a020a2d050106050123160201030e030c0a1e0308010605090109050d050606150a0512060420030a06090b0d0807 69
    0x58124191110041c1120489a01c0b46400c05604290101e40c82c040d1203041941d905601e0404481801c900c61900c42d1400c2147c50310403059051006046803403220340411544480452041d5501001402500ca0518551662a00404007091364080d034803d41c00c103001024669078041000740c4607a030000b065140c60161190a241043c0c1d90103001c1081c0044038071400200403064000b01e045031402d803144880706200b041613140702050704128860404080042443c03100e1090511032030503006140029280c4d0300505090714551050085041c07941c41a0380200402c194030f02c041801e145410071844040c1c0301d65038040c0070028180a613506000d00801c0c0025540d00c00c1c4e02400042c1350040c851507050b056170424503250402629070b1801078090080141d0003038401c5048595100099a82900e40441c203c00c413650050050b000340d80c80758a80046812400340c40701c54400b014501020150390b8100012510100c91050b0b001070045030030000002030070b43e0ba48140b123450a4100b104203a40e002103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 581508570 1250 581507320 581507347
    0xd0e0303390d080603010501260703151505040b01022a040203070906020d140a0e0f0603010303050306010f02071202010804051e03180402040e070c0c090228030509060a02 75
    0x802041c003000d59910389408040e6000000c42054204071501d81c900325031100c5041c10300ba16802d0207661144218948030040c1d0500001c0c020154000d07880640f01c902e52aa41c58004200c1407800e14880d031602c2d0b0040a445d01001c07a442c100920f800c0310200042003051001075124640c6000902010601010003031418a40c10b1190f500c00340c00520440d52460720620280c200c102c41d0154600511426207a03984c114040d50715010034001c03842400c0d00300380d0525001c64540d0f142d004010b070446107070b06a0701001c1d215080618043e40c0300c1d465403a02e80c81c0141c001480c80811043d000c0031517201083c2000420b4103009504201c680a02c1c0c0b00410740c3d02e03401c0040c90301004400c0d0072504102c0c2c540c19810031102001804200602c41464150380c0140c00400c41640114058500c5001d004804229842e002e002011402e510500040d5122582c9816503c12a0407000d0b8829009030005090742c00c82e6407003c403c0b0305802650504011509103207a40c1ca43d6894010715003100b5940c002b510f445004c28 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 581509820 1250 581508570 581508637
    0x20030708030a0203031605090a0902030c07020a0e0406110f0f07080f0304030804030e18150301060e01080d080c270111120706050c030c0d090317180d0e0303 69
    0x10030400c0302d60b01c2142d0a0000e569610403107101c1c014200d5a084110014170034800c075030008000610a55140c0d04205503c0025030001e07240140307440d4100003050040c1c5a05400c00001d20200071a6440c41c0780c0390500c4016200b4040f24001a100e007000410300c0040c025003502c80714061a03c0280d00d40c031784c1d40b030030040510824507107078240c40300442048101a40411064415031107562004051442c120510580f98460308c0c0d0415000311400001d010001914040340c041c0c3d40050003c038a0580c0e400440701c050301d00303030000e140076080f9501c1c010100d50048015034000b4120050b0f103240c0500c2c0100c100989484054101440c07a10780e0380e050007a845000040842454101036070941080c000407505507922242e4211141400c090005550740036240a9070312a00c100c5060300d180801a038094402400d00c0701c411004c0c410380001d280d50301c0b81c0c0c40e00024070500b050130780003600c2c40101c807c1500e0001c0c4040d5940070403c11141941482d1008400c1d80e6140d80e000040c2403040360203800c1400d4070700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 581511070 1250 581509820 581509829
    0x9031205040b07080c0708030a02070311030a0605010e0f06060a080105010c020f0405090f0c03030918090708150421020d0509040902091f06030501050f0907030f0e030903070603020304200307 84
    0x20004110f65080c094010000c18030414044111082e81c2e03a00c80007107860b8044d140500015800640041001c1000144003509950008050390080c01081ea03e15007120401e030400480003c9132010001c0c003080c43c00845801280480702542402030700f1030014030380d8005005245c1001484180303541151130f58400040309960084c0f0903c1a854803444051b0384000c210180e10031889a800c1b88255410b002c0200c80c1440c034040d044413841d01c00c2420881e840c081c06040807031188181b02c000240e00505100c0e2540100e00c1032402e00302814981445950461001c942516400c2c100d14401000e035000a842014149542400e50300d651601001030014840124043d40190703440303042200740b00a01200710341c08518000405c41d4652a00307021070403220240034180d000200d000354025940b52440300264456001d20300800c000d850795505c00d050f11010381050050f54000704419440d4a400c4c0403110190505282c21030070b5182c1616000e805102054104d1480301d84c41c2240e401c1031301e0a1105402a1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 581512320 1250 581511070 581511089
    0x1008060103020a0311040e010e0c010e040e0c0d02130504050a0c060f09060e010c08030405010f0e030c030301030201050f09190f080f031c15061707080412030e190606080c0301020a0903120504 84
    0x9c910400120313100c14880c02c60030b00150804510040c0c03072a10f80720740c0c81c24101c108001c240326541031060003600e91400d2070076a030012041940880200341c034065179100f284a000035190100440c036200142c0501754001000744041c0c240580001ca5101d0581001c4502a1900c2c01800303151200691398010900c40c05414680004200011b00c041500721fa00b480b08118030400c5107220350100d4030340b40d0080c800480003540041004002540c4105c01401c02d503244582030a1821642500048030700e10702e03102e104249480c0d0030003005503010701c0300fa1000420260007c2d0500200c100c1106440744103502c86212000d0b402d1000305174400381030303025822960702c806e0202c03c1180c5a030400741800540d901c1c004030308082d9800180c1303218442c04c0200d000795031146920890325032094040e00544200d4030b00710704074800d05a01159140e0442c08010346c2c42d01031040019000d003010107141c01d140d40c4500701406a8010000c0e1507006620144113011079030420700c101030030005803900300d81c40c1c400c81d07000e00c002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 581513570 1250 581512320 581512331
    0x504020706021306020708060f0619080c010e0f0d02061b060c0d06080109020901090504060f0612051606051c0216121b0209010b1803060a051008060103020a0311040e01 74
    0x104040350b401024034400c0003000315041d50f9a040d089035201141d0042d0300381c540081020511400b41c0072456070701301c01d0051003c0b9a00564802d041054007a603440076403d6403110344507005550308445011030242c416540d800f40300c044a8082a030000b02420005d0141400003001e0740014420528044064040010781c4c1d06820601420b03009500146900c051461501d440021060b00501c500c01c20381740d0107401da107800d03071034214420010407000700107a86c0d81d41c9444890a900c1700500c10380010b0442d1044141c0b406196081051505110305860040481144410301a190300300c0e0540d811710054060b2401781c0c0c511051120081d005200c00f410f080300d10000c101d010400007030200f10340c640841c1d4500c0542201201d2010420711810800303504210002c0040c00500320040c01089840300301980c951800f8580b4000c0b9280820440d804105559a04e00b8807250280840c4040000c080a50081c0503950450b00000c0003110244002420010700003101003040d120f40c0c219503954200702000f00315 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 581514820 1250 581513570 581513573
    0x30c010507020105180604122703030801061115010b0f0408010507080103021f0806011d13151502030306060901031b0903050f1b0603090a02061b0615030c091005040207 74
    0x80c0109035011030305d076002e94520403030410303000441d10301c40c5070001c0f4138a501001d01078058443c1d219054656482c045070200710b0030700f109859030001c01140300340c1d91410700e0345c0b510f90000c08403405220864007a0b001101681925980d0b803150a05440701c2548695880c8580607880a15114943c4119400c0d4281030030400103903013012440381200c0c007c4d01d504280d150103c200c004140518080c0601017000c9001060855203d109441c55483d41f004248218000742400100c03a0031740100d0000d6403d44038113039008080c46c840c0301c0e14024440b0081a81440400e08800f03522400014041030088502040605140e8404e40010501c7e80000720365441c450b004c5240181a1a8a0b0005071038511890407401002200080d01d244e00c07040f2604010106180341e42000000d5101404020345841000c82c814003580e6440d0041c42840d20303004d06400300300039842080b403c001b401080c0e25002d41c001c6000d0505a24046100c5000036812101d04030a50b441c0b0280b504c003d0744681141d60042d1001c9180300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 581516070 1250 581514820 581514823
    0x7030602130f0810110918070327021311030106050c011803110607090803042904230d08090907022e2708031504020a05120f0108120903030c01050702 66
    0x9041c2103910001d1048040011003445c00784100340295420036a070b41c80c42d03076100d014050710ba5003003e200c2ca000714034000e0300e9000040d461800d00c9070440c411101c900301811880c058098138841d46882c00207110006000b100d0880c207000510880082c001c00007000e8403003d00c01c0d0b10800c41413000c440c4505583c4028200200707080341c2540104410700c60100800c2c0824003480c0440c0c111000e4000440c6030a0074004202d0410720550030840c15107542d00c00c0c0e05803040c64440500301030034040c12030042c201d4a034820780c900f0b482caa8803154010007460000f580454450421071702c07124000e491f000550f40b1036890892501070f42031100a00072030742a4201d40c40391104100500d5001c5001000d008030443e55614055004410b40415901a41c010704170b80010032801c06140e01c049000d403002104200d81c00402c003607134050b55801c00000c4002505100090f45141510303005401002100030560503c3c8010383da51c111140002c81c440b1f00410070f043c855a0420860340c54806402c02803001d802c0c00c10002c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 581517320 1250 581516070 581516083
    0x507090504050a0b15180405070e01090b0a022802030111030a14011211150304060213060f02100f0213080c040501060c0b06011407020612010513020c07030602130f08 73
    0x681c801d50404000c64400c410034041c0c0308065900424524024005000700d564640c00040508201d510b1601a0902d035a030f24450b01780700c3c401d547c072600029800b48000400d41030554001103510f250500c6a40c038965400101c03601c000d1443d4581d070700380c1c0c0c0000160342800749160754001e5156007805d0245c4c0c100281000030394014104000140701c0322551440c0c0c840a22024050910722440190001000c50803e40052071151000f400942a521150040c20304a92046405480154000400740100d00c58013840e00c008108a24014000800c0181d00940380e1540c1c01c400c2800c3c44e1034110307003041d5155a0b0304035500201040c2c0c503402a05d9031528016100d90f81c1c0b0340402c0c4154904000041c42c20701420061280580c0311807074104550310030740152030350100e500c8034a038000c0c003d01c00580141c40d00f500a00c40c44000000c031005c10741c134080800c0800d121340403003c1d50103030040c803100440580018403402a00e501803405a100c000340520306440e05415440718204260008000600c4240030514 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 581518570 1250 581517320 581517329
    0x503061225060c050a02040917070f0c0504060b030f070306080f100612031b2105071205130e06030a08040e070810050d140a0b0709081e0727050709 65
    0x4407021140d82e840203481a090101000c0c04581116440c0c500510701980000c02c0c0714481c403000c46030355250341c01034401d581100508444941c4015a11024000781c00540c0e401820221000d1000f2400e00301c41004900010381b143c040c404104005c1007040c1d000742c000c035000d001345000700c6403075220444603583e840b050044060801031402d080803440d81c5121509440a582544031090300004204507480c04440c009416103003603200a210b00d10071030780c2c05c0c20303141000d0705940c031643c0301c5200d4201520385c04001d130003940a0150411481008651106c0ea135030841e61805050725055403003101013800c0400c5240001c000310700000e00417079180c0c81103815274020032150307a80480541d40c1040c00e144007182c82c0070b02d6603c00d81d00c4a8840000d05026911005208080142c0e461001256074040302e4020503201074012680c025000d001030700041103c0c0300c80302d00d0400c40d85044400e1112054482c04580070742c1002a6984150302010741e62522104030400c3c1500c8208220301c0c2c090300080620b038440c0039 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 581519820 1250 581518570 581518633
    0x1e02150403150c0801120f020303030a0f1415010e040608030307020708150103050a060506190315111317030408060f16030b0a0905060d0c0909140d0f05030612 70
    0x700542031521600c12020304060039120201140d080040e46003d00d5101b170b1040350004943d440100041c2c13001e10141d40075a949820100344442200309031320035144c0841d554101511828108114101075100d1080050002c0c00c0c429000011174010402038401c40d004824544000010300600e1540025804101c44994050310084004444403154200d0203110145c1658003c24266010031420b42c0700d0303a0045030003000d03404c218400d078005840e0300005034016208846000240244c0c090380740140c0481880f41c8010500e091801c8500d01d80941ca180100c104c0e4605040b41000218030030002c9070003030850082100c1c080e10309210042251b00c0e00300c1d0b496403540000c141c00d42c02140240500c1c1380402d40105101121414112180c00401c8018482c60b44110388000d000d010078044059000640440300000c07a846041d41464031451000650b103d01960010540c211400e510070a1060000001d1421540e00e48803500002c1c81500002402c60880c0200840940c80c2c0c510404040020000d159 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 581521070 1250 581519820 581519843
    0x18050c030a03090306150915030209160903060c0e03030315100504063f05060a06180e0618070f14030721021b0703110301181e02150403 60
    0x201415140c529560004001c41c044600034000564142c00600340c03c003da04c0701c0301e8803503550f500c06001e482440c2e45004104000303007824420360518014441d4846034045265118910044e40241842d01911003d0310769a6141d030f03006e42c0c00b40304101440e5070b04401001c4988070f0400c011004d00801c49003154500c0350740000400502c50b406402900c3c01c803001340c0c6808407050b03070444042c003e196540c40907515a81908c201c00350b081c01c414a83c0d07001410b150303100098500d00002408103c2d0030310740054050007181054840710810442980041e07030208404001152610004a40304c5907079810402d1100c1e01050801603c00d42c0702c0aa002c0510740390740e034807842c1c602681e049041444141d4800e0001a0f2101c492620385100580b183d62986494100519088040310a42c1c035003a90895910341c0e80d009100704000348060a140310b00942011002005602c003404d11004000b001550010f1503c0200c06082c12221404800415a503030094881c1080076030f00020180c00ea8041e0208403440d22169 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 581522320 1250 581521070 581521093
    0xc150209091f0807050609060a091e090612050d320901260a0905070f080115170a060908090a090506030d0302070c030f0203101503020a05030f06010620011805 70
    0x14007403048172406402540351002001c00d0103000e13404040b442040c006145000144000004a03040d80c1c908600d80c1149030505040d51031041e10015132211600c16401151030000c07480108403410492074600700050307800386100700440400c1e220300380e0402100e80500d002802c4152400103000f1480e099882c0d050b408000000c00000740c011078503d029044c800d40000da110a03080e400181041d014200300e801040d92880d843d4007440e1141c203d40c540d651070342014007241d240b1032002070141c0329028000c06400004409650f449050341d00c042d14194840c0015000c0c4440c54088610b03462000e0329249401c0e44a084000140c10b0070744419010344150303c091608180f2a20940f006140e102d41c04500c031030b256440d200f00d040c0b413191003030b40d15000312812900c09100754410904400d0860024072140c600d140104082c0c200145d22050184e0803c4030840300410f804a01d80b410741d1010f0400102902a008411082c1c684401200e22650301e00480300042c01c40a58030310a40074443d404859885114 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 581523570 1250 581522320 581522323
    0x50f07080d0f0c17130504110a030e0601030807060209040609020c0601081908340b06090a0905030910020c100309150c080403050f070c03030f020d0f0c150209091f08 73
    0x501805085661021005000700080b403000300310030b05148001074503141d02e0b400003800321032400c8c800032810f040000d00d011002341c160280190380707054980640384541c5191505441842030403030042c841c03035000503400300e1581e680c2d0001000d0500750500319150380121060300c0d91944203029010092280c83c4e445018600018440003c00707034840e0b8842d007440300c100c801108203204581703100c95588840384074040c007400380300101c803445001d4440382da16820002d0038825048000b9040e005000c0c2040301071b1001c030714004101c44d4841000d40701c41111000703207007040307080c0030306000420b501040560500c0c2e09540d240d080303249098001e44850a04400743c5c1c2d080340031149c2000340c100100d01c2480008010902420103441010802070060385421000da0b6085a040c84507002200454070b1300e0359892110b070f41004814090a40c070b08000c4180300c088100038010340a000b00c01000c5280808090350241100d03015110a02c0d00a010044941492920141ca05441451400848801a40016100c0700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 581524820 1250 581523570 581523587
    0x20c01110408030715020f03100612092001020f010f1401090209011e170705031f0302010801050f12030a05071b0e06040f02120a1a0a030c050409050f07080d0f 70
    0x38140300841ca0501e0355a5035004003105e40c0030f4513181075401d018000c0340e49608001503100c1d00807000c50088c09806d00402629614050401d003203244d1030b010300d290000300346942d40780c8294000202d0b40030900c41140100d00d092105c1e01081d10030750802d080720b01c030880b02d0340041d210740c00b000107000c110340c4e00c3c0c0445000724014a6240c1d800a000d010708600d1010000245201084861411092002e180b501030680080c081e111000000d1001040108460101c0500004202d010401c85c1c0300c02d2550b00001c00c8100103005081c8108071650040207107039101e5000404900c1d6440035251919a4180302800b00d40208005403801c00c0380101042408808410020550303290864022a0340c8910003070100600c0000316100c500ca50800c41810100c0d018071106200d508003410124614040500c0d12004010703501265015070350f40001030000995a620b903000340d980a41d00000e01c5841d5017060381c0380c94170a0340508410701404101094003100401c00c2c00e46081d51b9101e4407502032075180304445041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 581526070 1250 581524820 581524829
    0xe0109050a0318060e0d030e03070f03080301030606090203091e010b0a030b0106170f150f180417071e030e0d030507030201060e160f0e031002120601020a02281206020c011104 77
    0x129011b0b0620001c6d004902805a440c0701030119000b064a86c04911a008120340040e01c403050080b004004105c0140107000241c1158032080d81035042952546540303440045400310302e05660441c0c11454402540310002a000c002c0c0700a6a007a582d05004041c07002c207016010010300c2c1440c0702e40c0400702108d40c0d10b0184242c0050929150340703039120100b0704030340341d8145903118040110307440660f0350341071031039410500e04110309485d070411785818002140e20720758a681c0312609001c00404075503000c0c00c0c01c1c801902004c03044904019032804460724400c0d1a0b102e54819843c41c511002e040d40a4050484148030390001c0224a44030070312402c4503d0100c0b440b8010307212000784941c04502c203178082c075100c0c1c1550500c18000001440001c2c14540420380c0c0500d8682c2c040785041c1c0c0c401080030050f070040800c1c00909005500754000c1002c40d82200e885005440d011030358075080110000e05e200040c03200005051081040e458000040c2d404078074003440d19801c14041c1e40d000104d010440e400c45 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 581527320 1250 581526070 581526079
    0x7200f040c120f0515030c01021504030207050d080306191508040606030b010803120a0b1f0207080708210304020d031d06030a0e0c090c19090803070609050f031c0e0109050a0318060e 80
    0x804001546031400d42b0001c20450440c0600c101c00100e80e10391201d000702d42441801c80b5502d0346800c00a12482c84a00810b21003000c00c130350310410003402c6070003003414814020b10f45180c0580d42ea04010025004941c0000d0030170341102d00001e0140c00110280c4040c480d408014501a03e0f03012441041d01d0903994415482000319602170941605001003415140e0345005407465503681e5882103040020a41c0002e079107402001d240c0075040c86517144400c0900710300040e10700b1802d0507000b0581503002c1c0e040c002c090100980c02c10801c1a1600310301502040024100780e40e0b4a480382050300a1324142101403290701c00c090368510079143c44040d0a20803050000e1081c1483d82007005040070038031032590703030303040c0116a08049001001800103060490041001003048505440d04074944881581714501d103810038000c1140c8001580c0c2c0c0740b01990302030500400c5540c4c0c0c080ca214010054008018118882d500d0134004047d085064045424058000741111a65401058031400118502c10350300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 581528570 1250 581527320 581527333
    0x11e0209061209010f061e05030a0c060f1206080c09060904150f06050405130506071707140904140a0f09080f03040519030507200f040c120f0515030c0102 68
    0x2802216002d00d0744907100700008504600000c030342e0811102d81da008103031118059071030100058581c1e20094010901070f0014030a0001549400c400f69038180030b07040c10804015480904c2500c1102803809100588004015a503034800c2c0c07165403440604c403103c1c01180b58500103200362a0000104d845282c000341c00c091003901d02180e1038014280001509103080d0340307010200781a02c45200d047d00c625812081c4402260040c144507140c01001403440080061a00c001c0112041d2048030640007929410104c1d80c83c03000f001d04605c00d000390074410360414680b0010500c88001e4010550040091031010802e00030002c00d41d40c02c0e98500d0720050441c040420241c0c100d00043d00c000c43d482401201607030315403030241c00d00c1c500b0612014010b40c0012804070310b000030b00a020100d0041c5407040d003003041c59001100b02043c50103003280e5500e0f11866480c0942074100740113425451070000078820411800c1c803000030200c01000242c51600c0305a0b41e1103121100b5046c00918101003c4e0143c00500341c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 581529820 1250 581528570 581528587
    0x9140111031e13060e150c1903020a060f09060605010e060f0304020a080a05030c19030c080d1d01020a030b0414061309051005071806050d021305030708011e020906 72
    0x960703502d14540503846800801809a0380c843c0e0f00000005440c0c0390b503410640200c07210030000c60060210742e641900c442081030300b261400004800060149641c01d481d010201400c069081c410781e84406494203007803c15203003281c0102e90080c800d151007035100700f1035161140c004480c6040713200c80940d04404204090072503441d04201469206100074100b907403561311800d9643c100006900304903555400420040c000c0c284c1400101d02003003034900e00c40b10a800b00c1e20300030611452900c02901103a400a000034016000b0b800a0051002c281c611009000980706254000d503c0b03480014006890000c18128a1505015414044410f0094a00c480c0ca6070420803134011078002050000c980d903028032000042c03050200e100303180c0d400c031000107030b03450b1040024001480350744001520100d100410b01280e40c10400b940d1407144e15607001a1100c1e55a00c409034051442d41003243d062042c400001170551741500124080004070210b005503008280340f00b0140c0c0a4440542c2e40701609100c82003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 581531070 1250 581529820 581529847
    0x14070f17150406050406090204050a0801020c03090907020c121e07082d0703060212011d04060f0e060c03161d040f0908160203061b07120216060914011103 68
    0x1440c2100050000400f0350f42c450024040794010392055580d15004130b810801403a041184400411001c002980f0b041000050161a40b01c0c04050f140b040500c0000700390228400c1000e40e07405480a080c2c0c84003241103074030165407a410b414680d02401d40e94508001202004100c000460f401400201140b50f1014010007640f810f07421401600c0c0314040050404000070004100218003440e4010f1790344d40e0310111186803803c140c01c00614023050110342410313500d100740150b51140c0c0003140004d81e14030401c0290050440358a611440744214800c3c411a00201c40c01180a08903200b40e00203222020b01080d2080342e50402c4009841141c4602800e180c20203030001c22840c0c030698000140040d080d130711000682c00c912403094508107031484040031030808002d0150003903410801c070055640401d400c072810f4422100c000b410301081c1032144e40300c0e6000304284c410307801d0019900302501d5240c40d0024003451091043d04a0f2180502c45202594000c5184411500ca2000a1031130b0507903580412 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 581532320 1250 581531070 581531101
    0xb09060d0b0117031c1a0108010311010806060f0a2106050a09050a0212040614091603060f0617100606090e04030f02210405031513020904030c0614070f17 68
    0x250064001041281a40141c1450b11028080544000200ca04499031003000f1132120351b85960510507100c0051002c0f0710b4040d0240b0070303d18246803c001c15070310a40400e0180c000c040e80031140040104841541a0b001088211b03000d100820101000800d03500d10002d407445446229040300c00d0810510219495402442d0702651902000d49480d40300001c408080f94215410344015680747c803031108030304040d0884c80e00a05d005d03004100f0550324000325504010135200003818152ba44e40d500d00c2210b450b41110006001c440c1035003801c45182600507440300b5003d4400c040c410329014020820900a1040300140d440c0030311003001656561764291106012000120190b01c1600701040140c1c0d200080c480d42d001c54401c03132503200d0340b424040c146464a050000c0f40900030100c00c101d1a003851880c0c2c4014a03030102c42100d1180c90310f0605903035481002e44082d04190a0440540d402c0e00780c804581c2c042c0c1042e41c0c54080400918a088a1404c40d45491008100c00b040100300c0c1c0300a4050b08 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 581533570 1250 581532320 581532359
    0x40b06060703020312070906120e060a090c05090f06032107120e1f020d1e0503061c08070308090a03080a11090d15051303080112060209130b09060d0b01 67
    0x11a0700d0405481d1031008500750486e68040014800b140c1406038942c0300e18811a805046d41043c0151000d01c0c100c551160401407003255500c0d650380004007072001030260103009080290180e0790320700301940050ba0b0071908459060183c4288062240b8030905500070f60b01011048900c036003000150380c4c40e4070392008014110b03810800d03041e2a9920300c2c1d607098809644c0f064121409006e07021038103030203418840d4411082d41888405032072103414402c608070a071001e4032949000340e0713603594800008000002000700c61407018101c901510800c00a0743c028203085020752104030307503540c41900d520703a82c4070200b000400281c0c5400102d0405807494000b22003040344101c1413402c002c0040c4c04240c8400b05184141d81100c00305140042d551100d1060942042e00d00340e80c0d0b0a81d52540d00c0161281506114585e1441d01c2c494440c0c080c044107a0503038205410060002c002d910514092101811a58100074030401a09002c14994900003050302101940705814400c2c50780307040101c2c0d4408060441 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 581534820 1250 581533570 581533573
    0x3050702090a0e060901050402010210061d1f030807060b0a051c051212040606050105120c09010c060f0f1a0a120f080c0d0f090e06040905210a030e0105040b0606070302 74
    0x41803c08407424400a441482d4841c0009078618040c00024a04a1101d030903504d0070b0301c2c282090240140c81040209242034581c01160262291000030001890041c00e0b0000c442d9070b55408020003070010020500b00d4001c003020300c20076403ca801c000700c503081c03032050740c0e0f00c184100003072041d16503182300c3c010000d03000b5030a47d88601c41d00406194298070003d09613000e0b04a020801040112070b2250170007401007803a02c0b40c104812000e05440c01e59024003d0810380744003052444683c2c2c4200a10032000d54172130403d0003140c412510910180040200300400c00f82455118461410440c4450f461104014042c1407250300d40007020060400c415030541d2512151401d25010038000d40080c20364500100c014581c500c0030700c10040c01025041d00c00e10802021070b0003084100702180913140c00503422200010741c60b8043c5042440d000c042c00400102c2e035005c050200943c10715402500c0030a429031001e000388421040c0e224206c0310100e50040002d40d0020109440d410840302915a0601c84d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 581536070 1250 581534820 581534831
    0xf150909091511090301050a02031e13020a03060609050906153d2d030b180f09071a19120921050313080a03090602030a0e0d020303010303050702090a 66
    0x24200030075102000c1000f610003500042160300d0b802e00340308950303005486050443c1141010468091000c94100e089209510000081241650011070041040e0f074010902904590b5030318151014100921448072210702e071800140c05030002040045c82020b05184542d030307a0f0084410880b810300e0000c01d000440c0c00104030440c1c07410035102c00700d0314250701001c165802c504501e40100412556000ca10402288003a100714401c00291440c200d001c280c240421101c0750040850032105506280e490321202c49014800750041d1a03003100d0154210304203682c07103261100640902c030b92455010403e5000100001d8488100c2d0300d28110000c0c0840c070300100c0040d0309102c1841603400c41501516038802040403e100f442e000c0c00700703c00201c081c0c00c00341d00303515102580150b044036660f00600200c100040d50018241301341d10410b46294482c000b19164200180300b44003c158a59002c940c0d4072035402041030305030000007aa81225030540d01c0901c0c020040e82400b51200f030140482103440e8840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 581537320 1250 581536070 581536103
    0x6010f20010e0c0f03030f07060b040209040203161e0207141c030201142212030b0307030b010302030705030307051902030c040c0302071106031605070203030d09030503010f15090909 80
    0xa0042c1071140c48020010811080c03a401086040881c89100a1180d8000c004018010803628241c529194000c0c05c0020802a6440410081d1052059441d84203100104100503001c00e034201000020b03c3d560760340303241e2070f10800c082100d200c821040c60250384030000c2000544500860304400100203040c01c0c5d450700d5500031440091080700d0301140581d44a0401014201c84010256441001800c4075408504803040481c0b00c0c9090a0020782091854000a143c140c0070381c102e01e0034039201500310380d51320ba81e03801c051800882c01e0004038443d02408100090038a80041070300c4000ea041005004685440c1e5500c1e02c411000c604101d0705401034140281240d80c03948545082a03400340c50140e62074455203001e4180c0d12009507100c6c0701c0c02e0140180502e5801e00388480f0a51100e500344182d6625041c000686180541e100460322103081807020020564000d019504a504a0442c1410325440c0d01ca80c0c000600c1c21502c00d000036201410800510319143c1100c14520700551020b451007030390 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 581538570 1250 581537320 581537323
    0x2190f12080f070513120c1703090109080102030907230303030f011e06080601050703033c0203011a030c070614072a0f021f0c060605040506010f20 65
    0x10300c5200300c0858040340030000055000801c0a80c0407490345000c0d8a009039451001401c5181d0740036030041c0804079034442040025240300c40020b0110081640c034050000007410f540c80e8030082800b0300087d0040b00c006901c0d5814000d6902a00d410f4019020550a260101442003c0000c200300c842c0480405c4645507102400198002c800c1d51105041d55030500e48103054580d00320503030743c916104113513080142992040c401c0d500f0560902c3c1080d600c04c240d0408502403e580d608000700c600003081048460044040240c12400000700c00e10310306265010a80200d0209114111502640950701098042c007000110b0b8040000d1100e64240307140354540b4000c891441000180500076001484107158020000920340124028805da959614414071015041d00d140300030403003002c0c40d40315011940c4009051349c1c0c00c6051000c51051006656006082e02400001170f0340d01c170300d0f05102141a0600f0b01900e4483c202c180c44610540d0150007013107515850310002079222007002c8464500701d800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 581539820 1250 581538570 581538593
    0xa0803040f0c120c170a080c030408070501090f051017090705030f0a150f02120702100b150702011116031a01080f0d031515270602190f 60
    0x10341d1207440103110714038001c028290039070000200c48400c40920030005000c3e0381c2d904141c9860309250700552200f0b0403190700d892000c00000b04441c8020035110050340001000c0c00850b841e00c812100015030390310065801e8000ea004030181b10101041c144654202008600302c01c4003540b901040340c01c2403e20034207650005640d854080e0704652020041c502c4c040103416000c41c080c10143c81c3c10f900d00c1c0c0c0c0306082e61030040101280a5100e80b85149001080d505580c2555112240c8900d14504114000d440303881482c2d080600c185000482c003040d040001e010b4a80400c1001c1c01c928140f515001581d69080001d8260050301c5008440106261090500c8004500c600b0042103159006141c05006101c16044082c00d07501140700c214540000080342d980500d0302e42400124022205c0071300030030b0701c0c1d070b50401200b101043e411283c2c000d61001d4030390101780f04000450050200d5507a40008036243e44103250040e8402400000c0724065100c01078a204d10840070311103008560707503581c505600e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 581541070 1250 581539820 581539823
    0x10909020d0507020c0f060a0c020a08030316120603080f03040c0b0c0c13021201060c080c060f06010f0c0b0a0e070801061401110d0f050c0f01060b0c0106080c1e01020a080304 77
    0xb5110018804001d030104251003540ca0210340c44840e48150f02e000c5840781c003c25100d8000c010034144408195210100d8071405401a01d043e2551b070315020b1918032041a4169500002615030303042000300461a1080c41c1c2a2070b40041e0b05441d00100d004100c54641000d4001e655032807002c50000395000106000304000fa4450000e031044080481c1000800018a40302d4950a80100508884034039480401419140b66080c2800805847c0c1482c0ca12805001035140f910b20800081c06101c8441a002d24410042660750714070340140792070b0865851044031402000313180c008010501030003040c2c00100702400040c040320086541c48041c80d0a4440503446a13044a0314003080c00350a513484082401c2c100042c000402c280401d0600080c8102e00044c81c000404c100030580041a000602041060307281403402481600d40355070000c2699403164060310080d40c07900c000007035612408624004824801442c080841c211145124500c1040a8500f8114018840303c040080c10b42c03400b541c0a20b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 581542320 1250 581541070 581541097
    0x2011805010f0b060301080601060302280e090c0a021b2b11190b0304030507121e02010608060c07060e03220e0f04060e0f0f06100e01030804090b01090902 68
    0x1c1c500c030b894001259214002c039401341c401000103202d11900010401c1c11107040b40b8005030303a84041c3d484036001030078104044840e01c004d0306c0340b032040325031103100752500c0d4808642a00032910340021100841c461165a9009600000b040d0010008a81038202c07242501920030408550280c2e240b02c29600496040d441c41d1044004010134402010f842d030042260540b240d00300314000c1100c0c0c2010030818402c6080865000000070100352140d0252030002d03501c044480030711420701c01c0c00307003000c00170140aa034444240108148000c1c03050141c0300843d22a80058900c1d82c95440d001c0c10964820107080c0d8646490b040d012107010710810080c03404080c0403901250f1400c00c0314800b100c04040d5440001458a800103120400019000186e080b80e44200005080c0e040044841d044c110800f1540a4900540c1c031150055040881c02c64498200300400d40702c056102c0c2120405d5500038027002d008008148014450320f1219032002c160340031305060000d000e595480f980001d03a4004100890b28 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 581543570 1250 581542320 581542331
    0x14161d060c01020c06070c0203070e0a0213060201050f0919080313081306030e010515091008070801020909180304050114040b0409060806060312030c0a09080609010203071713120201180501 83
    0x1c003e0203001886d0444040d103400c9408000a1300003903618031450041041d0300080e0707404a002000079504035002c0466120110304420756915000e4024001107480a208111490018078030301408074200352101c41034040c1c40da040416031034210190f08001d085e580d08500040e003200100322108040c3c2031100c00c5d100d22621140c01d064008041d1200b44160042c01e80c10103051091f002c01285039508a0300040c0d81d00b0241d0794880100d0030b00643c007a400340c4250f001d070080105c2d8038941074005100000c01521500b1590310740c9152800c444900b240c9416607908180820700466118585110b50303c2024034000c0c0c01c1640b1140c195a031607215901095100366200c50410254005008865000c0340440151000086d8072000040c6440b00500d05a803e1400041c102d0700603004410800c0a4080f080c2112003924000c05514001c0d481a203900c00450508000c0c001d09010f06042e2a110b2a41c41201024002d040c1d03640329120401200c5020035552500155101c8440c00404a940c0d64002c10000c1031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 581544820 1250 581543570 581543587
    0x1645091b0203070b06060702130e010501141f031104080f0a02040c03021204030509060c03070c030203060c030115030b04180309090c0e0307030b07020114040602040914161d060c0102 80
    0x103001a6038840c500a40d0030601c84003001c2800d40c106240d000d00c4c241c0b010f40c1c0c0c0308414400512000e10000051003507074582203140b109054150301c200d050b100e8811906141400720b204001d8414655030000c090810340701c12110385075109812515003c1d0164149a0a190725482c0040c1803031030ba0005004a5404030701060254546805465000c070030b01d040071403500035103118001001c00300600c0941800800201c40788151210404c48800310710080650340c480b0036620700f200701e0620511059210384039190202e1081020742007100d040381c0c0b110b034006242d84114002540a8020143c0a03a807041d915040b6405c2e113080e91540e4007100b8429a1a1001d280c184024201160100c0b0842c2c02007103000b5100d0349141d14000b03060001d8075007085900b003c5541c1d070002207003d8001c650412038641c0c0782006100c10810213401400a9070300c1c0e40c4041c4030b00c1c140b148d0245040c200440c3c45241d0b805400030035008050083c5104111002c540d45070800c48049400812425881400e40510320380d03000070000d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 581546070 1250 581544820 581544851
    0x21303120c02030c090906060d0219060c050c0a050d170d0914010e071208070507150c05061b16170c0307031806230405030a0803164509 60
    0x4c03584401103401074501c0c04d041c14000c0e5108001040750307000740030890031801995504049803941d481c002c0c40d00a80f594407074000070320201006401701d840d807240219000340d5180a0300d60005482c030290400da40c0b0312647e1200e906245044d038100e2070600c0200401400750b40d160190903004c0c0c0c0251a240c01d200e06400e541821640307403052002080c0c2001c2003d0000148210071415601e8000000b00c0d150340e0340d030826038200401e0b81d22052015011a0390301c43c41c0c5801c440d00316a814061001e5801580d2440c443c09215135800c41940400201006203a0b411100c070501c4010f07541c007800c48011000c0108003800c00540c01500c02d80c0c0c440e4008100107040642c0700180e000c1c46110303598000f00c180d1408801038003014028070360740300c040da401410740d61b0050b10800307540080c00006c0032110381ca0b40d5400c2022655105a44190b84986040143c0c03050500a20076400002d0840c0303040442c194030b40c10b22000411100b1203900700c0c4442c60702e6454914044945144c05405040000a40658841e90a1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 581547320 1250 581546070 581546083
    0x8030c16080f18030c0105180f0d050d0215011a071e1419021005032d072a060213030b10080c090f0403080c070b0405010506032401030204021303120c0203 68
    0x6038032035400030384980f9180e6070210948000038a0307a0223808020501d180000c01c03c0902c071181540000e505a030b16400e00a00080100507035036207400f61a07402000d1a00d0568040d003d00800105e075034044950b2503660020350091035a10300805040100700c600b620b080100481080003a900380c01803030300c00c4c40c0d55030041c0f04d20410a410074038100030722015a80441d020aa0444014050113404400074110414040c0c07000000300c00171043d46a032640c2030711140d008400a0300da81c3c0004043d10030942c0e90380385480128031400d0018020060000c0560b4230140a9408118590814500c2c1540000052281042d5034041c0001c0780c1605030107801c110a8529150341c1d011030a20a010070814030402041008841c0e030456054903102003642da9946400049104e116401024850101d0822051044c19440140914412015614044501c4104000c171685882003024a252804010001858564024580c40e0800400b02c02d0a9a0741d4442860711003400030210702140700003e041c0211301c1e0a02c041c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 581548570 1250 581547320 581547367
    0x904170313060b0f0f120c030709050a06090c081f080f0a11030313092708090f0619120f0915060b0f030a02030403181401080a050408030c16080f 64
    0x8004c410703c26000084c40800000501c103000710080071440014000c20720a00d00781e0301c400303400c65105590b41e01c5034a0007410100c8800301c449203810390115850302c03907002d0004141c00e9039039020441d8603103c901070f85450709500789403603103003a0300340000b0000c0040c801c400c0700d1591000034040403c45428024000d41003488018400d401c10885010390321300b80d03201c00080d074100e90000201018601c80c0d60400227640040c004000000200650400500f00d006011400043e034070540baa035a150144003c0b401400c02d80c01c4010090800d502285200e400e4005069080c140d000c0b488411401c2084101c0e001150140c4024804d0707030700124442c8840c0103080040035100081482c00100d10414440c5020252804100d550000041018148900b110b05808a644003000400da45c0d61901e421003c500c41245901081c2c1c5880003888641680c13185031711950700080704610b96036601c0c0c2403585c1540242040700700b40201a8211020905a4006e040c0110402d862130356645140340440e268504210768 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 581549820 1250 581548570 581548579
    0x302150901080c0f210108100b010f0f03090f030521060a270609060f080307080403141029030109030909052706011a0403030206060904170313060b 65
    0x14215441c0d81c0024078030382c0038018540a90b12100040c00707988941c425500c06402981580382d85c0d070340c0e803807080c0440c038100d9a0a01c02c90b802042410b11340400d0311101d0345000c1c00304490711048031940d03000e96001b4048129602d0001202c80759903440340b44403007090308103400181c000300d4052540302440081e80e10305000700b501c0c95903a00d450780c00125030003130b41c3c015009842011420340e800f05c43c0d029499048500390503c18001d003501c0d110040300610051080703002940c18040005401c1d040403088800140d00315503810b01e860308640390510000c1e1410341001741441664800900704130311384078400e01a0031104910110124070082020f40102d0030140c03511a904d8064444002138000d00c1c804c00f21502058080750319950726000f80c191361484014841003134000ca0b5180c0b4020400f003240ca050703038000c9030314070b60808885040340c4481c02540002009a40040042415494107845403644588035801c003c031185412800200d02d43c205850070450002c40000820401000740140d40c0c2c0740009a5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 581551070 1250 581549820 581549827
    0x206030114092224091406130201140a090b0307020a02030105070503060d030f02010209120601080105151c020d0804080c3606030f06040f17162405090304030215 71
    0x28506148254020801130001040308000c03d90b00c42c940c1800c0d184005143e4082040c01c40500300035880c0c2031103041b09041130180c00002a650b5100c4220300000380c0e01a503034114000490400300c0610340c04040980c0500c2034000c000610802000001c602c14030f09a4044c19011081c1e00c189401d407a80945508140b1130180108042c50f1540c041e151000ea400d8230f03210f8205400e12600b40c1c0280710f800702d20f5400404c0820300003440080040d00c0b41c100c400d440d008005980c1e940b81c007500101814189164899030303844214a22042c40080d1410180c002801c180104551751b882006503403040e4400ba80f1500940070700095454500038080400d00519403c40c100803c10401480c2c903a00c010041c0c0c03110008001062407910200a2000154421802c40d581401c140c01c01100150361040222241c0d004082510008003000c4241c41062259404410342da92041c0d4580d00a4000d0407042e4402c3c0080c134259a100200d140600760061581c3c50184d9921421801800302d04c03000005149448102007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 581552320 1250 581551070 581551111
    0x9090f200f1e030d1d0306040201020c0d11060d09110103110306041d0102122a071514040305040501030b011b080304020102070306060f0906080c13050a0207020603011409 75
    0x100115148110304480c40341504091030100d41d02c418401e00416007600c01c40024140454100c007407619200d02c010702c55242032814004041d40c8640450f0001d0043c2c01c2448a42640d05000d043e40c0c500c4c0b1700c10301810360100042408100c007902300802c540100c94070f6220180074407100d05420310a030700083c40c0c284250540c40041303003094071000d0909400707a40e8a42d00200c401183d82000400302e40c0b160000d66445800900c005001c400c141c90b050384030002d42a0400550750002c03625150100d03054038060410040340c03100d07020b0303080318030020721426181c012040701000c802e80c515104510035101e0179103441c1806c2c0018100c0303501113011070501002c50690140302c106150991160350f40082d5541e6640ea072403004038149041c42d40700810140c1055004101400001d1598040e42c0d01c0c001c041000326034420304d0070741d100c4156540e103410074903c0e0081101c5030b0f060f40009911440c540c4000d0311b0f18805902092140c0c1c003d91203030b810011242d43d0401a850501c038030030f0300704164000f26032184510303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 581553570 1250 581552320 581552329
    0x905090a090c030803060f0409060b01031b020a12090305100e100e03030a0e1204031a071d0f150a200106030503031603060e0117060703110d02070c09090f20 69
    0xb54000a08581030200000d4182e6031a030030001e02070800900244841c1c074613407410700f01901c903000f001400300c2e06000d03180b0303041c4204c1410b40007448450707402007250320405c2e283d0b0a0a020a90b030b0007020030001c4c00340440804c0003000403103d20511460001a441c02d810711980c100601c18110810703403420240d105089560000035660480c14001d0006a030380300500d0102c1c50510f101580451402022800109100130005148900c0c0c14102055006640710001141c0d208a42c6160000b90011902c907440740d07041400e40091107a102907d54002c41051008200c460303048508100e00003903005800001d90680004014600c56111000380011403e540c0da958690000400c90155240e40380000175005100b90044001084400001842c6584030324040a0b0f0000b24262035203035100d41070110302000e20a00c80c500c02030721117100c01400e0500d9880d00c0d4006c0d5201400946d690000e00a021913200810f204821406110b940844165452450820442d454801204008403030901c1482c105448 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 581554820 1250 581553570 581553593
    0xa050f07150305101e03060b0d080a0305060d051e01180503090907121503141b0111010f020a02030901120606080f0604020d1409151009020304210905090a09 69
    0x480c02c01041542e94582c030381030441c5540d4008141000080045244003110982410984c3d020720000c5c000c0666403024030408030154030000340090000c11180034098401e0380202d4111300d009085200d00702068481c1703464440f611b4180350995020941e00c2e80d00480c01d1180e00b882c00120008024501003030780311140c503806101c1c0c4142c000d0400b6400600c00c540706a881c06090340b04440c0400ca403511140c072070340f403006541c003081341c5c0840042208600c01000080c54900170300b032400d07560000010740e40119040c5454031940604e542d00c540c42a40b0003440790000d40302c6c112855004580f2006110001001e500d400340800d40061302d429070034000700c0c0d40641c44551004614031040f00c1a11541c000c28024481c4040b07000104c2d141850400354051070501d401c0c05070143e002200d12040361000109000d0409450703440300714a034207504115021841e005168403600076042400b01da0588450f201404140300d08140014100e1007080c400d03490f04580c002c0c0c002d90100420440b5420607550082c2040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 581556070 1250 581554820 581554859
    0x3021b0d0209040b1308041211040504110111010216051c0503010617220f030e03011404060c092103030c0e0f0d0c0515030f01080a0503030403110a080c0a050f07 71
    0x403030603000030525492800078a000c1c1c1c2e4450300302e544c1c0345e5443d000c282e045448c05400319090310400302900410710b010700a02d8007894200c020020300780c4445005481c821241107600752195000d100503900e5620170040c0500c001d0045015140712006241e121034031041c50300085d000d00c5014001481a241d0000d2a03090503100000d83c032280c1d4030b544402d00c854041030f06031007030003044022a4a0130000c040f40d029001900c03075100d000041c280b00040609940d9150013003241000c00000007030124003203400c03074010840b4a0600d50450b0762900c0d006000c120030480713048070026034541100d0415505114500a4901d245000101d4101005c005111030300001c1c0700300d21581116030500288504104050300401006141c43c070b40c81400209500b140e0411121410014440800000d00720004610446c078258400c000d10b140d0354a43d42e0540b4054410020418035114408500c80000c0d001002086000c410300020051480603180051400b00581d450700010380040e241080520701c003000000400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 581557320 1250 581556070 581556083
    0x5010501110d08130c061d12104701030b010e0603071e031e0912050c0a0804030605041506030506180f01090809090106050a05040506030702010905010903021b0d020904 74
    0x244c552440c0d83e0f0440c1d0000c1d4000d40800c01001c00000c400342c010040c0c6039101c042c2c06002117620a581c080107c21954008000c0b500d41103100c11b4501800a0750003c1040d501c01620780c00d040e280c0501c2010400b050f081c0c4081040d55140b01c0c2071071403031507580316121014246000d20006d511440020035000c01c5219160040c0e6001c000b10721301c80d001d240c0644181485801400000d038003100018007410303c43d0a40c440c141c03a004c410901e9130410380180d41c10560440e90b41501c50740000300071503055020310030040a9014a442100016940b04028001103000360804105401c007420140095002c0c4d01c4d1010b080d074507012041000400c0070560030340c85611020750f8005200041031150406c0181014081d00354641100c2d00d080200403c080c00340600d080d60000500c2e03880e4841030300c01e40704000d110000310790700f0b001c20021031801600440c2c0c0521a8400482c000301ea968a20b401c0d5450500f003280981c110305d0707000c0c1d06035204048904440b0021642c080200000d9008600d40b2a005031014281 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 581558570 1250 581557320 581557337
    0x7352e061802071406042a260a1a012d0302010e030a0501091a010b0c07030f030909150923040204020306010c0203071706061e010804170d0603050105010501110d 71
    0x24403950039544c3c1c004030703004070a0314014a02840d000c010400fa1060b0800c104107201c03429010f003507002e0074100540c0c030360b4100010150101400701203d0380c0c2308902202c00e40708a8008000060b000d0087c4644189000030355181035042000032000b0074510703402c6504500d103403541400400403882c01c004c00c40c0c2d02803c282d003041590101190174400c4041010f401c56080ca01c10102b044010300481500e2079014818810990b2038050881c01445011010810381c2d10510050000c5a200060f04011920a0a000d160140d858902c04182c60707000e8000c0c500c0900044007009404094044c1c2034002c9411501d000c03540510100c3d00c0542c2c0300140019005640c08000904135034005e48048001a800504032040d5581d03c0c10045c075480403003444c405084c041c0d41c0c04101541031a50503401d01128952090030741c0d018071401180d100701c0060003503410055441c842c0c0d1800308000700924441c801248040307030a07419402c0160a46006900141c1048284080d400c540308000c24043c40d0170a0902c2c1c51b404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 581559820 1250 581558570 581558573
    0x3070f031206030503270904150212010b030a0b0108101205150f0403120b090703020d14010f061416240f0e06070207352e06180207 58
    0x1003500480d0000e0703410514000c00030040c0b0034004064805200710b0f810840d45100c0746500c0f0317a10071700860781c010340040c0b14401040000342c42014440d00e010903000700500746401004401441c240c03c1e445426151000020b00046425034050b0403d14002800d003040141089040c2d08034000541c86181228003104010004010041c0b1059140540007038440d081424410144101d9030303420b80e403c401043e0140f21040e0010507500440000e960014080c001c990743e1090700b80c0c042d62281081800f10b90f40c1c2c40d4030310081000810f0b1030780600000000c0700305060420794040c012600390390741c40701484402d029540a4040c000481803020790300c0703102c040640709510700c41c140340c0150481c100c07100e80c181441485100c80c69030041e101c0340b0040e801ca0303640e5240c5c0c00c1d00ba0b0315100305c2c3c041c4e158102140c1441588064404511038007550009500350351f1010703010f04443c10900003100c00d00e03880446600c035010034140b0222402519074414003c01ca0356140504640401560410a45c8000e801068080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 581561070 1250 581559820 581559827
    0x601210203012912060f0a091b0b2a0307030c0c1206021903020c060c031f0b0307023702011407050106242705030a060e010c0c0503070f03 61
    0x8401c2c1c0d9281c8024840c05400e180f10300341c501d00341c401c100c3c02030b413218500420351070000480760b01400542100900c20384814481c0d00180c01c42c00019541d19515162002d6101c0000c481c1100600d0f03041145034407003920010403c0e0b500c000c2d1100c075510007002d000010400c4d4010044482142d4141070204084415103480350300822030b81d01c40c402c00c10041c10401c0502507240c00404503806220f8648101c021024002c4c0e040740201c5180e0116640310340009018a1628001190070480c42c400341800a0000419848550601e8201e4562400e0201c244180b554040001c0c0b609602c610183c07043e10746c402c044541c1041d0607100fa013402841f044880e0015a4003d042c07a40881c500151115560800340c00d015010300803a105000201607400a00952800032400b0401c030383c8040e907034001d0b240c4012038508800302c2c0307080c5c0d500f5051042d4510009043d0303800c01c40c1c0c075182c0d40b14043c0403c491600030305c030341d00711035060f507030305090000c180504000280d0200032a140c1036804507841c03210207103030306044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 581562320 1250 581561070 581561081
    0x30302071e08060a05190e0a03120b0402160b07030b010512100e090a0203060a05150d020402040b070b180a030f083304060b090a0b0a050c032a060121020301 69
    0xd4030303079001e050700303000e000b543d2038001764440c0f0a007080040c181e9138804a6030044801c50b050480390358000c00c0d00500000e1140f502ca141484201a000c54602080c2001400303c1c3d10150b2200d5603182929880800c1010011045910115504042110001000020b0820700c5068071803840b08485d00300041c00009412030f15400741040d408148101c1c64007200300f80c1e540445403000d922074428100001c6604045000f064481c0c0005483d600000d941c1c5010305c02022800b580c2240d000d41c0a0101290b42035502000d0f1002500510000c07030f01e810b100040380c0303424000745c03010401030b001403400d440401d030000700d00c20151521346030407202952000c040d004101c00000648a405010807102011350700d803c80107040c072040403034080110315070701c000380a950701c00da203800c4d0f40014200c0410449400c0c0e40d400307002803070401d09099140c0011a0f202c00c1c1503510030701000f007544c00c400c2c0896040f1181c031002c844c5402c0b0501d00400d00c650401000c071115440c0c00d00f46490100422044400b1503d0070b4021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 581563570 1250 581562320 581562329
    0xd05031c060f0b04320f150a0509120c060f160b01080105070207080609121608030c1207020a02010c060b010c08040e070e0a0e0109090c260c0a030302071e 68
    0x60071416142c041c1c1d440103a1040c4500d0180140380da078040e07007880d028204080c030781e005130801501700c034401d80500c000115503c00081d4091b000d6400410722070580002860b904032079540b0160364003041010080f8a034034048403882241e00c203000c210341648503070088070900c2d04101801603c034180541c0070ce5a0701000c001c02400609000000100b000054003d28007034040d503029200140d4841021640e111001c0310080c1c8240e1046810811402003200100b021035114003481c00034620940310001c5542c021749600c14104000203100d02841403164085070460b18a00c0905100c1c8090b8000803d011450300000c2d000e990b072544400f03520f030301480701000074a6200d00c100d070326a0b64030031a413104494100c035004040b8801c4c0007034003182d01e041c850f888280c130308009441c5116401c0685200c0280040001101e041d540114041001c9a441042032403649024480480c002030415810b428114000810380c000c00b21403400b80f00181e008101c1c002511250101211882e64404402003d400e45030f10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 581564820 1250 581563570 581563589
    0x70612020d140901061d160201060b040b07060b04020f030f06131d0105070c0201090e0c1303060b01020c01091a1c0e150105100e0405180115030b060d05031c06 70
    0x1042c0000b000b100d03511078412a00600200074080c0e50385100440307250340d000580c0b40d6400400010f000c20401c400e02d940080e4003403000094507a242c8500c0300171603000c2c1d0400c0c0560302010030308104100c5da90080301a0b294090b41e081d410440030000300000d07404042c00f025452214580062490b4581d4003100c50000c03105c40c0240700c034141501c054441030940d16881100d6500300750010341120b006250080d8211790680d2014002c51601014011080001d001c5681e00081004200e40d40180e03054208040d40c0100c0c0001481074540c4000392904024039a490305000c405501003060000400c50b603a40c0e00d000c9070507107548907141610b64180c0210600d1440340c10b45011096110048001032813501e5022510385005166200e808114500640c003042c07400060420700c02c1c400504254028075001200391100d0b5154042070000c15083d80c1136408030f1f42e940c218189041050026500c2030940109090b1281e1b01b0340c00b115203034243c072031080c0c0700460200180320061208121003544014000c15034a10f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 581566070 1250 581564820 581564831
    0x3130203100f0608060f011202090a1103042003060912091909020c1b03060103110f130e010b06090604030615080102030a0504060f05090a12090b0f04030201020d11070612020d 77
    0x45440c0028601c3d401011201d01c00c100000740702c003109865190607159840501c0c0300d41c49040d400c2000b0707210020159002d080e00c601c0041001c0340340700041c1d4081e134404c00781c405000d141002665018014600344038480d40c001002d0200718800801c507655042d5954100c0c60740c0d648000d000c103541544600d50b00d844002e00444c00900300c01954041c0c2204a00c03001942d170024400305100c250081c502c48441c0d81a0440801000010714100460294a00140010804111b03c100183c50100c4d507800d01c1c0d16051322810040c45040c828070800110328002c072403550912400c0c81c0895401e00540c00020b11075aa250f003d000031588001c0c0030b00040c05240300039992450301c03841c078001034038050f681100c80c5070501a00200842042c0605480b41c0058802400c013007803241c40b10f40c444c015100c801c03428043c4030b0001254401c0301c0001440e40711840c126144d500d601c1c43c80024034080c4a00210020420b030325401000380000400c141086a1591401900280d0401400d100038403444011138076040c500b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 581567320 1250 581566070 581566091
    0x9070201140109060905071d0f0a090c08070906050c06010312030b060a0513050108040f110105090a0806011a0703050a080702030d050906040303061505070b0414010608100c030b060313020310 84
    0x5130070202c1916490441800300341c85100081d980000c1c0d100c00001c84510104150740c13507080c2842010809100201440c1c0e400d582d80c50b414044850120a0400050703144080000c1c4913000001d10005015a18009181c015000c020644440040c00000c02c4800c0c0346039942201c521942103240c0241c4000c0c1025641c80105501601562090003114000103450800290700d600441249119542090204048407c10f6407580c0d080010301584605021042c8034440301d80d00c1b0803100390b024046440041c00554106000000360710111074030380c101121704010290000307038480c09607540e25005061900d03050303d83d800140e0560203000c007805551868002001108140050381d20301950103914104a560b8440442402d1641c0e02c01c85d003800b1a034204190000aa4101c07070b2558054040d14442c000c0508500402e400c3d110a50700c00c00b05d582c8100f81e0f00b4400ea18600c12049400e00c24102000f8002c05400882c03400d00008103032081021070503600205540b0306001c803650306000e50700c0401100000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 581568570 1250 581567320 581567339
    0xa08030411060301182d0c030915020a03180201091509030501020d140907081b12060907060210050103021e0d12081807050a0302060c03040e0a02071e020d02090702011401 75
    0xc02285e042e05070900346203002c000c0c181c0720010610f040645184610208403580d54002d00300710b13041da4041591300c403240e6002c6840221449000510200c2c05a0b88010903c4000c090301c590b00000340003008181c5220300180c0e04512507074201c6040108003900034002d403000ba190700c1c0044c0e20160955000103403004034800294841045c40c0c60064400c0490340b2141d2865075240028040e8450f00da0044c071904144921402d05641032150080140a264049041c1c3d2404c102c81500c046030b195000304000d01c50306405000c03803079264404800c200065131468002500100165a44140406499444200544410180341180c82e005920041c9014050000030705100c0111b950000109030741e04038080d281d0300030410000b225401042c0300314450454080211603842503000180a1100b008000380c0550f076500c3c407a20401c20202c1c0183c0f500c00904003108086456545c440d426510749054800580e01e00c280c600401c0d030140c0e4118410b5803681802ea004110200c6401c10302d01c20b403400003402c1ca54 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 581569820 1250 581568570 581568599
    0x309030301030b0c2b0603140d02011404110405070e0d0b07080901020408060a0b0303070209090a0b010b0a080a09060b030a0b0a14060102060103110105040b03040809180106020a08030411060301 85
    0x820300f240030302683d4507860448039008258500f21084119604030740540a813450f0390041e42106000020383c1d40d40c0782c0c0c8082d03049201c4086040301c4d40014a450030038a0f028400c001414050030082201440c0a1352507003814180b1001581c415a030b02c034007007a40c003486001d800c031008034081e08010a1400b141000b4010850498017640043c9189000540020045c026142281c207000014241a00c502040d500a000d8010724150184414003c603805651440714490250301c08001406025515051881003104140c0001c034420004100c22010903a20010b690380c00201d580000403000300d2882d0070005000310b004030b6035041c8604206d400500200c4e00e240b50244007808000c1051a22069001c41100802c44203140960840001040407804a80b89049001c005142c0140351507107604011001b900180c0e4140e8000c5004510300600703090500c1c40e103040d140c000d69009560b61604074001d69682510714018000c1e0700200c0420204100030405003d4400d00500d07140d225030f12410213070046103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 581571070 1250 581569820 581569823
    0x30a0f02040b2a0330100e0105270a0906020d29030c0d14030313060e0c090112080d020a0f170903090d150509030406121802091b030903030103 63
    0x114504402c52040d943e80100c034858201d49400b46080078148400614030f024a140c81042c0c2c8800301030030095004003800d805214801c07507030b00c19002906091002e044010143c010034020590180002c448042d18403a08044080103907210050341d4680440002500184400404550001c50340c9184c8405640102100c0c0222900142d0058400c0f00488014024088034540580000da882071031401c2040300900303490b010b1174103881201d1415007201c0c5035900c111024503441d8080710b00c94003000011300544078011011401890310210352000550b545006114038a010509280d142c01003105403001c2c2c03020102050401c649401d404007000e82801c5402d84003e00260300c40350b1003050840d0308a440380c05140e1440096060020b00c40600841056211003a14250071000100705000000d0041620440c0c0782e0001c2c50322246020400382c00511444164a00103040000f0210f484907203602a8a0341a0129620519030b25000703586000040c8004421121800c00010401143d5001000714100d0303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 581572320 1250 581571070 581571097
    0x906020c100b0616030203130801050615030403210902040608010603031713030318051b010f0302041404020f0c060420040908030601031a1201140a06030512030a0f02040b 75
    0x4011101c00c002100c5007070080b558001410303c4016002407589501c1c0c04d0076403090044900e01400d0a8520201240c1c0da032204c5c50f2a9110b008108642c1404198428491080e28015003982016a0064030070880c91a051015400c0b0b030391040003500304d90300429030454003e0700410440b171b1200f0100b0b010b80220f0100b640403540a01c146041d034010f00c10100e02c166600003420180000c1580d045014100e80d00300182c05900c0341401c0e20101d00c090110745912161a1425070413501d02d040007505c04018209a0820705105020402140e0b05052085e00480003c850060fa84e20f1a030302e201c05213000303481103038090f071140038100300801c584120f002070f102010305145d510341e03250300c402c00081d2900304800070701005003800441c900d13501a40005104810402c070980c8039441020126501030031007001103c41c3e0791100d038941c100c0c604c00c48040341c2040402c41c0070701a00d411501c5081e500c0b02079152980501200100140e070f2003000d1b5006001004055409550b2140c0e240400f0f03a10303410241942452 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 581573570 1250 581572320 581572333
    0x5070909140f0a0321150e04020112060f03080c07090204180b0603010627050603070c030809151b09032d15130507031a011502030901080f06040905010906020c 70
    0xb91440003d658907207540c15178928210420f1160b80a405c01d4900900c1040075850388503020714011113158500c0a0485844c06006030b25241c000104581010400309035902d14040c03081c4000750300700c140b9005607500f00ba401c503614040300403d245044a80d500440001c1c1c40030801040001c03000004100c007041c6050180700d803040d1441080058802071084402040c614138202c0a42d51660b00e10321880d079800e981d030a204543d0f69010034002d90044880d040002c03004d0075050105600820300b0382c1c0000c5400014440400c2d14020412006000f5101c030b100790703228040965494000300d042360203144026081d80c00000b150300501d0103107030031031034000000d0039010055440200009250b1018aaa0382000503694444240d4048050451070007a200d502800401001040f07010b5652030b40c441c0814410800c41d1b00d0001d002d820b01080f0a542c47c115002080f1004039030b80d004108682081c40b608841c03e207074480c00c6c0050014110315000a00b039508100d040300c2886043d602504034a005c01c0e041d1170300c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 581574820 1250 581573570 581573593
    0x3090f0d301806080601030f0501141311030601030509030c0706080f0c03090d030209040207020d0b010f170a0b060d02101d060715180c080f1b0612040507090914 71
    0x1041c0e41e00c0d1420780501d2140b0142000458031a4400507041036042c1000500c074404120300c00141c031400d030480004414840c4082d41c0740d0800c229103a010f2880040c007000080da4400381144503100140c540d40c101915200800c0d181c201c18400c541d40e4402c030404440b0a10765409001d052110119110b450301c2e583d07400017884c1240705004a07031207000e81401070305080d103aa2200f40d000390401c80959400a07820b12030900180c036807440956089000f50880c16043d03148c948040d4004081e41c100c02100c410244070752000390000244801515403124030a21a6561700011444419007108080c0d80102c03c016001125604540c4200c4001680da0306200c80210740b109200c581e2040c00030041c440300725041c0b030401200a90340010549031250342c2d0105500c039943c5900d5a0010103030425040c0750080c05000f001a601007200310800040d049007001e0a8409200094940c0200a8440500f2800e00001002c100050090602500c2c000340c04005a58a45c00d0240074094015950b0b505481413003040d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 581576070 1250 581574820 581574827
    0x610030203060f130f11040314031c090512030112021008010501020a0308180a121b0218090705191403070b0a050a02031e0d050a0e03090f0d30 63
    0x2485050090803a100b0320f000301d814003480401014035408400d544110407916035026000e09102c50094400c41a140d50441c200038034509200c0e111200d095000b00000400c0c944001c64201158240301c0c000603111025080050404810504241100c01d001001041d0090408100c1c18500c0c000d03145164030a90209060380c90b42001e0040d05e0240c1e000d04d40c02030000344079800745644000650300c50b01200f006224000d10300860351404585030590302d0b4803401540d03406810001d01441c0741c4081e80180c0e8954001c965000e50340380d80f22101002560014145003420001d00c8000c05d00074044610091700d200752019070071841c1c028a465290000940445440c0004041c401d0301c04141501e450460307040d0094031a54030003801902580014000070300d00ad24183d03801c02905041500407640e03190300c0c0314404203c41c2c00030444800c0ba850107001d035038090390000a4800d03181060700c220280d80003c00002d510f1a40c90180100101238000038110301140c503402c51450034121184881c0d07400c0d281c14054 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 581577320 1250 581576070 581576077
    0x6090c060c200a0b0c0c04060605040812030f060103020a02150a061404020c06130201140a020a21090303140f071101020601061e0309140a200102011e0f021605010506100302 76
    0x7241c3c40214654140503804400d00140b4800100e8002c03992000d0316140842e00b03072210b0768048000f1407804241044070400c1804010541d80a2024662440c0b50288046140c200081c1100d07041590214030055124001c01c070004042081416000076841c020740356401400050040e204046c0350419045034030700f0b050007560f848580b12000346c290341e96409a41541100000f80a03810010310816070210300301c940005064140c82c503030140001150a003818015110303909052400362140030380310b401d902e50000498003589d5052802c04055105103140f1880c41c01030380c016040c0d240000071501b040011700015030400000a800741c406980e42c44c1000c2d82c2104120101c844a199070030340b0043c5042c400d40c000c0f05c1e0303648a040d2068152030240e5940f03107001003003c000c44104030782980b4071105007074000354424409400d01c000e00ca0302400c0c0c0303100b40030b0242c044400c010703580d01c5e0006e60301c1c504800d07019160300e2800100011091b0070a810814064101500c1145c0107000300c03500e14209900c00d0085 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 581578570 1250 581577320 581577383
    0x3020903030706050a0b060a17011d1803220f05030127060f02030406050f0f09030d15030f080d05010902090607110102120c0c1513050d06090c060c 65
    0x107141000d00c035403511400b13008000e20310003d265951003a2002580ea600140c00c02e44907070303900c0c0b08581100f0703030380038100c4441a0464054500340c200da1248500c4400d14265200710290302a210b400c661160441c61741c016205101e07051484c5680641c0c4c1600f400c554070084511030b0709000c0c04143e82d80141400c0b5201c207451000e2100700c4c5035040c902c07880c80006102955105d020700041000c0c03030b0300d14102203030819282100da6070340f202c0c140314800c01d0032030247c0c2c0c000c9014401a40c0500b04120782ca0359030300c03801d0498001e45441d188105203800c00c042c1c0901c0107507003042c02d6000101e01c0d8680300700298410451008031a14240010950510030f2090310141c0720007070112482c081203522199040e178000d8158504511400350000400345104020305030100d4840c000700540071101042040d420b419803c9500c1601040c040210170130b80c0040da40c0d017100c00950349141941020300306038000d45142e00380504400341c56503001814503880440c81c484603009461029405d140f1140d91f04811440c0501c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 581579820 1250 581578570 581578573
    0x80a03140906040303270e0a1b050d0903090e01120327090209040b040e1b0d0f02010c05240106030605031506010e01030b03070e040519050a0305130e1005010f03020903 74
    0x3440003c0c09046c50040040754280c0e10301440140044071014a041034100c4404207142c0c5e1305110380310400e07008a480242901d01130103060344036040700410324061400110100340c2c9a011110906000302d0034000a030103000c417000c18560310398002c150322500d500821800519259a40c0e004440382c804030b100007813102e0052580d203e252103442d46c0603410044945601550356501d40d26250f5851003449545002e01d03014000140b81c07020040c0c0c507008100320702400f0700341c40071442000807000b03000c0000c401d609081500c900821750400c10b00d405003111100c2d000c0f81c10748503894104204a03420300d040311000d90f802d01515481e44145500c403092004070256411401c000300d9103941c01481c0c03a24103140180741c00642e401d202c40000740f0b00038665101c8441244c440c2c3c140001d001082c003944074801c622107101642c580481d80c0e0f103580c884003660040d0410030080b5038540c2d10880d800700140200f40800c1000b00310300b03100342288070b12034035840b8881c0440c908654507040f0318024000c1d100c00302c1c4000e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 581581070 1250 581579820 581579827
    0x80a0c0302040908040909050a030212091c0611130306180f1221091101090308030a0b041b021615120509030403080712080f060a12051006080a03140906 67
    0x1070070b000c0a0401c0e10021541d800702404003040150342441860810740c054801044012114200603040904032034a203001f02d4001c06c4a440c8a80710341c0e0220130042c401402072704481455080a2005091100c6403000c080000120204111003415000c4241d0340200020080100810b6400d2007000d0700c00d500900e00340c07000b00070a01103005092a4250b070b900d1400c100040540002c21801196803101c02486400c0d6180502800c1c8500001424152a8207082400b18103080d5165415035010040030098070325201c00c0071030410b854a07000745400f000c80d927100182c0c201c8142c0010b5110f807000d8001d42004005c010001514845c00c42c004440c00081d900d0ba46c1c090000e81c4809030103007500501988051004100000c002600d51006200340350003003c0480910405010041ca040400381c02031680414071820701c01c1590f901803805044441a0001405403074552601e40c0c00c2c032440411641d0114a4124001120b010100d40b01c0c1c0e82611030754030500f1a051042c22401d06025003141c9581216091 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 581582320 1250 581581070 581581073
    0xf02040b0d0b010609090b1203070b04110414070e150a0f0513030b0906100806010918050f01050a0b09010e010e180d030c031a1020012301080a0c03 65
    0x40c0e0112102910207010001d0256081e2a58590b416003a840180080c466280c200554909481006904101243c03182005401201c25a58034011888064240d80c448000701c0d08004031aa42c0b044407000150003886031241d1a1091a1404004c807007140114020350324a40700e070b20b03000d41e01f080107590303403042301d4146000d03114200c0d0480c016040e00030620004008980581d5020954031000b14410b03c10343d0b47c8d45c076000d240e183c03c00c1c070081c00600c11515a05014402d0a101054850548601480c0010521113004030b20071078088844c8040d01c113025102c28242e406e0b1042d00070784e200c0d4030b96050030303c50750300c1420601403007140034415a0442e24004005018025408013185e404c030300000342454060f0300860199091101030b011180c00b1a5a903074170810342507054050b00d15242101c1114a419a00040100348800126840c034801c00c01105117069613110984a4149591903000c001c01c0440c0c540c586240e641399004d61300b000c0a080b001c0000800d1500000c1c0d00d60702c1030748100440001c0c0d146 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 581583570 1250 581582320 581582329
    0x6090203040b0a0f0e0a14010b011107180912020c03010605120604142404030e0109060e010c0201031e020304062d0f020d050f041401020a090b0f0f070309031403070f02 74
    0x5108804c104152564100038550a0070400410024019510000070001030301c055400c4522050280381030188080180089100214410080b40d04080c003213078a42c02c000700003600174002160002c1810a420b40d412084039800901582a14400d4000304002c50700c0303c0822102c40d0203009104210390040d000600000d000f810342c4c2c41d0501e4500100d80807041c81110003480d0840583c6458101d4a40d041040b081c16032002e2800d01640c020f08002070018103000c401045900c48540b1107040c440d0b50b810b0309045900c03a40c00080f21301c4003030142101c1d60307030b00316001c90282d402900c0595030f050510041c00c004080c00e09101079840004840520420342e0b25641902070240d4080c8101066401d200600c2015014080c080c0305240c0c0c00b42c14a02490b252404160f0520380b480320350490380c4144540102140c00c640104280c03045140c80a84801202100403490f1040003040d481c06000814040d003016004426003007030764810140080100341c5070503516034902602001406103070411803000c025040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 581584820 1250 581583570 581583581
    0x1204030f02040902062b0218090402010e0402180114040e0601081f06050d0507030b1e210a031706030303130204090605010602030a020706020a0507171e0304060306090203040b0a 78
    0x4060300204010f001a00000d986030480514020b46060054000324124003604101c00c4a0307803024011801d0414100740085002c0200c0712160203500607038007240c03d40e0b00503030001a031440c000704151340d80c41c0e84051821222a10150b110b011a40041200055482e400c0c203a9083e9124101010003954034040111110307140988554080b1941c41c003180801c00c88800a0070252403180c49095517000e4940d0760804680c0001c007503600b0946084011807060340d80d10244001c644041c0c440992009003080010906984124055945540705c98601c44c0348902150710465203000340c41310100116801c199060203d0201c5405502da0003c00c0051100700709410513002640c00030300b0029644085076992011201c080e001a0301690000c1b82c284e4101d64100280d002900c00c80c4094050403032266030301030742e03030400340200d8a0542060303c80c010a07000810030b810128080403134000b80742e20b5251502d41c80f84c0c020300402001900f0443c004c140c41086008030b134003442d0f009030640250b0303440306030503030040a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 581586070 1250 581584820 581584823
    0xe0411010c061505010f17010302040203091504050d0f020a0b0a0231050901050f01080f07052701080f061f0e0406060302030105030c0a0b07030507020103180515091204030f 76
    0x203000c080c085409481144000f146010481d07000a0800b40050710011041c0c40010400001c407000d500c40030914440581102d0381507401580b81d03110035130388900f000c83c50000411525600300820090000014000c212801d40d92100c00700e8602c010301c01c9231221140c03400501030504442c00708610b00e01d664014800c0c20350082c54113031140413100e06000c03122211818182c80b8640b1180c140040c1c9880c3c1100b900406007101d202c50010900000a08005070081602070360403440c80000b130015004d9021901002c02041d02c550030200300701401c40125030200c00d00c2d0300051648000404402c001c141c00760240c20001d015030504c4850304009610ba80114440380c003002481852184691554042c8d00c02409140c1c1b005620b03036040c681030614210a28000511400002004004504043c03040b69141130705441d000307540394181d00041e001f4120104840080300420120310080c003070b01188200c0500382c07504840d5200e40311030320340c9a907503c82503031102000d80d002c00c020400070383c1d242840203105 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 581587320 1250 581586070 581586077
    0x1204050304030204050a0f05090f0a0204020706110426162d322404080d031b030e07090c14130e091906050903090409080d0b06040e041101 61
    0x1d03183d0f808503007519400ea8a81440580361421501d28950601074030380d004481d80010030490442e19040d0745d031500440c501034095a40007500a05001c01ea07003000b548d00244d07120095649a40d01050300229402d081440e0040108880801d2007980102c0c40d03003482ca02640c0410442414107084414030050900b01c00600c1400780c0f220840000c200041074002c200340c05d0003141d03510303414091003911403540861450800c4500c1e06820940e840005040742006260740c1c012144001c1000b02d03d082c807803a042001280f003454401300b021980764010384000c050700100c1c08e0b403190700003505030192001074004081e642c120070b6092200c5605503102014070f40c072904c0c024043d110071140c00e04090344842490128001c40080c14085003040c0001c203074110741c2840050a140d285004c0840030800600d100402458a4502003807240d04108103035014504018000c00102c20280b030211159405100d080901d281070810040c0315281a80a80d4111004000341140381d540303944d46c08854034035440701c09051 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 581588570 1250 581587320 581587327
    0x30c0e041406011103120c07151e0b04150e0705090406030b0115110304050d0c21060f0b031b01020a150519020a052d12040b010e0c12040503 62
    0xa58403802000c002581c41640d5003031a0510100041c80707010312511051303880d8406c010440c101060401031607800020029141e80301c2c2218a0004130642540c40c03508605400c107008850b00e095071004130446180382800421104a4120601c001c0e00d001c1440801541d8000804200744a45c0c1440b42c0c3d44210f036450114601842100010121076064005032000c000820052040c0d01d4050b00c0c00c900c48107035042003c4034a944030511079682c4914061240203c020040010800400d000000090504440781e00d040c04020300244c4841035911405071840c1e0b0a00b074803c0820b05641c4a440511a8050701400d402c414a030a20b051b1180b4458a050442c456044044082240c02000c2100700c004820007141c141041c982d607031034a0402c1d42c2c00d050028810030050a60f145c00004460b0310000112065510000000c640178184440c03e554520030a80040d81c020640d0410007400d110f03521a5551340e0542c1d88541484201c3d110482d03001350039607010000c011503200b5a800007944907204908070707480d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 581589820 1250 581588570 581588597
    0x150703020c010e060103150501050d110112060602010b0f010908071a09040507050c060f0c030403260907030605010b1812190f020907020a05070902090402040902130f0b0f030403030c 80
    0x2110301e08140900f25800400042c000c000070013001c864040d400740001c0c00300d941028009607600840e13032001003c0d00000d01003000e080c0d0180e40c010034a04440b20080041d540e8500020340a450184001c5100303103402e000311703c0650f0040c00e1080c141c81e003c1c001414a00d082c10f007140811800200812601c0b10103000c07900c0142c0c0d540c0522845290306a40312500e0310fa60210140c64040f0181ca08602e108a0500f004807400c0d009094a900ca03170185868404a140110312a03200c0c00403110f0342c410030981c0002c1101c617410000381e10084030b00c28101040b0aa07a9544400447d000760034039814508000e8065103140c0c6071030b02c03089680080c0031084c1e841c0240381d80f01c0c4401070304181800310380c0d00810020020551820290f02c0c1c1d0300401c14000303015540369554401d0703250b030854001c581f446a80451854038036102d80d030646000d000c030008110b50352411500315100c0002c9074030a00e0380500b1800000304410425000303071a1010500481c3ca410358036503643c164003030102040100d04114180d1203015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 581591070 1250 581589820 581589823
    0x615040b060408011e05090c010813023303010f05010f050c07061706010816050d060302090103050a050d1b03030207020f130e100e0a060c09081f150503150703020c 72
    0xc001c000c00001c1c54540c01e0350340050302005c25003514102c501c0e08040103590540842c4100701d190f803d20b001c1d505551078444003d0104440000a074201c10b0440c11320076007115070400c0e001070504548504900542240d910b50161000b40141c036a103c0401104200c0765005901c4510400c21508140c4c0c1000c03280760704035240c140d0715407100f0005500d4400e860041280003804907040b05007841c04103181d1822140d0500784540c1e02d030020301000301c000741c5843c00940b02d03071140300510390080c010042940d40b81840c41c0c1d12010070f00213540d030f4001c041400c000d86000b20000e454404c2009401c802c280183d440544c02900f010400ba40c02110110698840e996540c41056502c0c52140002425411041d4840d02c0c045482140408141c0341c506486400d01c0000b500314000740d0310041c041032880300701c2c0c0d04440c10540c1c1d500c007110610a00c004142c8240c01d91038143e001d290034210410181c01c58130201030f030503110b9100b15a01a00002449242000004502d0f603004031141005450049420b1109 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 581592320 1250 581591070 581591077
    0x5030c060703090e13110f0f09100503010e010b03060f0615030901060e0c1e030105010c29101a03010302010801090f0e0f030a1b1e050c06161e050615040b06 69
    0x4441170b10341505910410850001c0044420015070320050440956004100c0c0f42d50031124280c411b15914000502c0d10141a528002400c8007034002e10846120b80102c034045c0c4a2000d44510a00610002940d0030b051401054800c43e0b0044c14150313140090f26129000e0351001c1c103965400d5403900c0c4041030440c01d41c00500d00072041c541c41c1541c0d600f405040401240c50460203d13026040800041016a038044034460805030884010484140c0b9480702185040b0b8903000003c940200c1c0007000b80c40c5030084c42d031004031480e005090490443e1100e028200e031200740030081c0818034041c018410854194821003030302c1d01c00000081c0c40103048085629000039941c40c50010744c40012500070b0340d0b0f803082c01024a1800905000030041480d40e950030081c0e46440344151030b8103505560400c1c4001004105945600608074503690020444ca1046030384003400240d40040e00048151821220040c0059071a0780003006404262240000244045118042c440c1c3c41516098603804e0340ea5884000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 581593570 1250 581592320 581592331
    0x1116080910080105010810081b0d0605010b040e0a020a0c0f0201020f0709020a020c0406080d05070302150907050103050708040f17090634080724020d0606020606030705030c060703090e 81
    0x24082c1c0b66142800040004030f000b003400442444034079040040540002d0141c221134001012100581c0e0084086104034800c2e010141240d801c0c0000025541040e800400a603200c4034519401d41d9101c8048105a1003640a070000082c800754400b0007082a4a100b690428414416940c40c080d04410191929000c1d41040c10038643c00910392074095010050408043d50a41e02844190b18160640b51500307100c80744541440000207241c01018401d11100545141d00352041c001070604030401d650b00d4445000d1a40400d290401050710035006084180c41142d104490320309108681d5903243e1002c1844403c018140414003c0180f907588d5607000d00030901d000700140e070030315000d088802c9240416444140405260980c0380010544510844a485401460011031005116115581c3e00850400da0094034804a51560aa01a500040300701c0b8501d5003101c4442d01c030f00c0101505c40f0324034412140e0540c0700c1c07500c00700d9500745540541045800384c2417107040030395540d84c00400010110381 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 581594820 1250 581593570 581593577
    0x20d06020412051507090602121318060e0f060904020415120b09010c050c0a030f0513030f0201120b06041202030c03060438010b130f0f181116080910 66
    0x204130300341001282441e406081480d10110251606401940b40c2240746a0000403000010f40c400042c411070020f040100180041c11580b4501012080003c0c1558000c40c1520014000468100c00356940107034000c0c1c0004000d01c145455030340c00c020041c0740b01c520f40c104c10708450900041c16848054a03801d503500441801c265468101c4040f404c49003080841024060244842580d030500007429074909507150034501c901511550003507440e0302072500703000e10070750403290040b00304030765a080d07500c095100780c0341d4000d84641c1c01002c070250303081800c0e2950085001d02c801c01610380401d200380c072181d0000d402d5805411448000c039052038421038044c1c0780c010740007142c804000c40b911070101d9801c11541048078203021482d40007083c100e040c4540e44120102040501818a400103c64004e20b085540003680300d507240321204d80c000b041d100385045405800789c130b15a16542400303000401117030302d0402c920345140481e071040b484404100c00d0b60348034420f1040d41c1e801d0701e4030180c40040791003689 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 581596070 1250 581594820 581594833
    0x20f040e0901110f1b2a01090305030d0c0311120609090c0a150e0a0602010506040b012a0c080d0923030c090c0d14090f030a0804020d0602041205 64
    0xc8203050303040300280284003160324184400d0411615030095a520412083d5219600e20103038080d41c00600c4801c03486105400f407400c00d8109020300000100d10b014020345a6110005c41c076006441fa00a280f002608a0b0001c0040301c4130b2500c15440305001c24200e04000469004903000a541034002401d9030740701031000400e105540c5880840d082d4010442d1004040d40003442001c5410309109210b14101505400303181c0800d82d00544480d0503070340d0054080b0540035a5042e00030b0103400d0640c0e0160066103411121303003055105818200d14030201c10081c100c004841c001001c0202c6420701d054408000400011440c28000d00009601c02280c0d42e5902c40c04e401c1080d40b6115152440d2180480b0700c2281c03c0c4000c40e01c000c80c901d03003500400c0b980550b1030341c0c0300030344203100c0d100704078040c1c40991910182c140321000d03d1640a004078400300848000c2a01c101e00e140d92441100b9080b00460360034400580149025958a00c6081c403484000d42003d503215036020008a2008084410360401c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 581597320 1250 581596070 581596079
    0xd020c041508071d010b0f0712050c010f1d0708060c0d0e070f0503060105090f15010e0a03030c12180905090703060906090240140c030f0a0b06030a0b010201060801020f04 75
    0x1134095000d8044154014a000e8080c00e1014071440f4000d80144620300c0039150415841c0114160750006004400030311800780c4500300400100081007800c00e207520752440403100c3d60310001d07484065500c442d000381481c1d01d070000e180d119a0010b83c5140300440d01c420201444000500c0b4200080c208190351603102800d0600305400c0202c1600000d020b580c401c1c041051100d421124150803040c01c41c081d038241e00c140b50040710b100c044111100c4c0c008140303d00000070076900450003c4020300940700c1c0340f0101075100d800c80e51000e8500c3c1111400000e90320030f1044400302c1e84041c0c1c0003c41c2e4400c681400d40d982c1d03a40c40c1503851401040c3c0303c056a40c0545025801c00c1104400301244500c001c82c0d03001c14140480083c0806161580030003141a148840c0e00702e225403000021283c40c03140c00c000d61420b2424068941c0c421540c0340301c15948440403402d8540389005400884500070f2038a03040d6070759450042c0040c402110028115902c640d00025a80001c0c80103250221150320f41694a42c00d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 581598570 1250 581597320 581597369
    0x3080403030c0302090d020603060f060415030e0309030a03110a060606030219031b0309030c06021207020d080105030706121b020304051206010518060604080f100e0d020c04150807 79
    0x50300307140c03d160041000101c103565030b2100c0113125604459181c0c880e1500c0010502d022a08800943c0000c000107011440140403280c84404a0103aa81849500c2c442000301d030b10f0713005003200305d41c1680c015a00c40300004d010300c0c501c2d00d054000c5004ca85c032610680d250b179400d07100c0c654403101c0425400070b180c3c00c00c2c4405602c1c02510380d01d5401c2c1880b80242040085c4e08118480900e5001c0590f5583d1101c1014814046064144c3d04020290344071000204486003005094426001500c5800c20148100c0c2c01010050b04840b00207020781451490403c0940354041d586c00c8000c1215a100220030760b1003032100900c1c0c8034011644c001c507292414401440351200c20b40d03040c0e2030070b540311000401062303944511a8640d25503810200480741c071000d02140040c069030300300241c9801604800700201c000040c16107031290755010240801e8403250419503d4004040b0000d0068200c00002d2009080c0782d00b180c0614001c0c3c091030588075a5074031100d402c10404d6005041000c802c41d0351220303007510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 581599820 1250 581598570 581598581
    0x1d031908031315061a21090118081207081605070809060307020708070611060a090503040e0a02030601090906030f0b07200f0d080108030414040b0405280203070f08180a0308040303 79
    0x103c0b01e032806e14041c00342a50094480d00445150b68030440000012003030ba100f13400821801c5102d040750050b2140f01c0c5044141d070342000c21951124001d401c00076008501c40d0501d44e0044108070141030f442c0c00c010740c08a030a5401750b0400d461010301001880842c2e1a0311004612030303489170340941040c504000b01181498425884102040021080740d0004100071489075003101c004540041c001c0e01d2440d01a0a5025030380c4000d680141103020044440c0081d002107120b414240c1c0c500c13408a0729014050100e409500010307111503455440b203000a14805072082e0482c186040c00150258401d50f43c3c0680540710b840c0a83c0d80e0000c010414840c507003041229012109410500060760400c3c1d9070700c6c0d6a02861141000b541e048031340c0d0041c241c45551010b80241000307071041c03181e840c0188515403404110002015405416080d9008a4070507100340d0b401181035aa6402005425038000c41d0544400b40210315801141d5030a1002c0301810044040040e203e074452480e140b801e400e01074211b03034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 581601070 1250 581599820 581599859
    0x21509010c0e03030c0d03091b0605040614190f090905010f170309010e060d0f020d020417012c0118030c14071404050403020c030604031d03190803131506 68
    0x24000c3c4044100c001c000306181101e005035190004002d411810139101400510f40c800408142780030001c18020307071040040054500c2030700c0d002110b0561805001c0b80744076001d54601d90108240988186520076810003164510f140b03401042c090f00d88125600710b070001e0384a032031842c03406142084000380507210214075400b0040a035080140c0000007802c10301690f005140b040303c0c0041c025004800944c080f500c880600c1c2c000b103441c1c81e0304000c948000d500900403410a00460301c1034100c8450140502c0101b900e00069621120640d1b900c2840e003140081e40c0c80c1d0f0300c2d54a4540411a06035024240900140070b40d68540e02c1c80f0300c42c1001d000140104203518140d4110560501140000c80e4020100c41d1007500e00241d140d0321820200d09005510501035410b00034981408141540602641c1100c0c0c0380d04815240c0b051f203042095610301040c00c070f1011004500c83c3e24008982401c01542d0310080744e003400c10290030a540e13100525151080480100b41c5d407440240440d06c0d00b0b00c22090140c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 581602320 1250 581601070 581601073
    0x30c120e0334030c151202030906060109081f02090d08220b07050d1209061b090b0c0601120606030f0c090b0103180f060e030703050d0506010201050105060a03020a021509010c0e03 79
    0x103a0454607405131140c40c500800d284c0303040f80300207041c41610401c400d4103a841440c0086403242400f092070350721804140c40040c00108032000106070003001141b2002115100c0304c1928a203400c5901801c0130750010901640e0104e200700303012000c100f01500130840c04100440000c3d0300c010441e440f00b0b440f40a03812101c48078000348a5440050350004807441c100c007441c1005000d04440200d51000303090844001440e56043c0704041c05030b2004000c013244d04012503118034010549401910000d40620214090f40e0b900610041003201c00c843c0603a501d1300d028840c0828003680b40d031181c074600b66947c00d0444188203201c078100302c052414410044070500034601800f113907050303400c10b4584101d1144080e0030300600030388070400c0022503440313020790944d040c0503291108604e040250494000712034499413a4104030000b1100d62042c86100d0590b00000c107014101a800c14044000b508032130007035001d61240c150703607089409035030142071310401700400085141c840f9400000c00700302c2500348140c001d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 581603570 1250 581602320 581602423
    0x316050406050d090c05060a0f02010b19050f0604090204241b08090a1517061206010b0a030b031b1c030921060e01090209070c030c120e03 61
    0x45600804030743c0c14120902c4041100c00180c140035030700f00840d500c41366008100041841c45c00c0d400145c2d249621141c0c1e00204278080d036180600007180140c200e00c100c0e00c07140310418801032501991440d610b08014121a050a4585004070b040b80d00607044a082e64540502504d007041c000703c56164034205034500072440e0b40d80e400010000b4100444010f041c4500071641b40240d07210801000300500350005450582580000042e006038440844480340148903400107156051411841c09101248401407240b0f0b1320308402e48815400c0301e01d5034000c058170341055111998042080c200707881c0302485040380701420303107040140d51114544c40c80501b1003a13011031404660440a080c040b9285550001140750404921246841d0180750040100707140c1040b081000005600c44040c45d482543e9000340d5443c0c00906480c0c40d14090170040c00101100b05d080002079800950710440741f01410081c9241c0d080030006070900217032030b642004150008081d1022104403041380303552030b140048030016 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 581604820 1250 581603570 581603579
    0x507030c0801150b0901180e060109080309090f100f03080306010906021c030c210222030b07030f0b0310050702101505090c040f030f1205030f0609071b050303160504 73
    0x100c0c03520348614800c401c4041081c4443d80d025060340e41c0031112401c64052134a8031512342c0e030288203081d2000c03800640d201c00003055040000044a05d00f15000b0590700a65a801322a1801808020b11403120076a0174040000c1c80704d007040006024502c5a0003150b1071789802d10005000c0c218030360050046500940e58503e8820300ca808070f014030a158500440c4004808500755004072103003040224052540c0a4200780d0a038980c09050718a41e01c8014122402c4bc41c00c030001400080d00000d800312450a0119001c20b000f50301c0f8918109107002d012074200c0c180781c0000d04103560f812080c072640340c5500400441c80d605000c00816036080b00c0c0e08102014040207083c1d10380005000c0c842c0662003c402040f1642d00b40e60940d001003001c95400440e050312494102901c005402e0200c40d07240608141880d8a8003d00582e0b20406119034504c204c1c0c2e4802c420002001e08c083c1180d410320111a098902003001160100d20b000d010300000e503901d0501328450050000340c007403030ba03003000710a020174403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 581606070 1250 581604820 581604851
    0x30f0303090c01081315060b0a090f0501170106030e0a0f03021b0405273408010c0c020f04060b032409060d0b0c09040216151b030207051204030507030c0801 69
    0x45006401039030085102030074004a50091020b600049225000072901b127a140e03a000078a40e0554100341c2071290419910401980e0075402032140c10003c48405e001804140c3c8242d200004264401d01100c814440d03544891601e180d1100b420750058008070020301180b5104951400880c605840400440c0303000b1882c80a032a441029961420b03908562032441540d081000000d03503042c1d0600301d818409075400a4105203421204000e035640e08180000d00030606204410364114661144107070f42489900308505000304c5550107a01035595600450b010701d00c80b000d5031051341c02c009041c0c8a0452940755580111244005a20400080341000100d4540c4c04c0080c0300503900450608907134840e01040d5006004420b849a045480490070180d8000345c90002c210840c001c41c510300e01406800c01d85015a550002a1681e140c0701d100081012031196001301407007070007141502c0c03180a00c0203044031540c1c4154000c5c2c890742d02400c000d00c02d120a032000c840040401c1c9000f0840c2410000228 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 581607320 1250 581606070 581606101
    0x8040306060e09060103120e03030c010606020a0201020f30160809041d031917071707020105091b19030c030204050601050c07051005040305010905060a0e0705061204020f030f0303090c0108 83
    0x240200301035048c4803c01603c0c1042940c0e02c522540d002400f1407500ea02009582d40b58005050f401032147c881d04c25480c0c4030200303000305020021190801c25004a20480300e11020b40300c1581e40d480340411817804039450a0100040b045d21031203200750344070b490808010680320400320948900d64a601c0244000c10008103c07092500042617580e14118045000e80d61084109480811000420100b01801d64800141d02000d44110b92000031512102400ca08944044503040d085610440300c2105034071380215000d40d5a50001c0c41d1001c0001041e0440c103001c420359004481d03101c3c4006080c011440d2600034154003c00038646036042046180d000c1d0f40d1400d04d4411280120515407040082c1351045044a0285030098000c1c0100c41311071401c1c982d41c100840b03440099030314021804280310404242c40f01100c50041490f802c10782025290b0155000191080b80e0241e02c3d01c00ca41503e8400340401c050300070052000c0d5031130f450322904003410449094403180c10000103508000a4a007440f160 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 581608570 1250 581607320 581607353
    0x171b0a12020f0c0f0a0314030729070809010216060b0301060801050402010503011202041112070f08092119020d03050c1315030f060f06110111040b0c03040308040306060e09060103 79
    0x1413040c1c0030904082414503c181c1c0014068403a401010080d0f15800801003c4851145018030110040f111810040c0c03000d401d00542509914000720350041e01c2010f820ba0407000820006103041d000c041e44da811911500d00442d0107940310381703500700d40c3d01d401e01c210f000a0128100a1003645400d80c0002c1103407105000e40c010a180d0341c20000c0c10354a69038004840340e0482c80300395603180c41c400b03402c1d49108401c032100c9000602d40c6001201080c85004000d00034030181c030040011905500009007403540c0c9844103130102c0018020035604804018420340c0315021a0042c2002940300d80703008040d6640104502c2c2030501c01c1000c00144481ca18584045880300981c00038a801d0481044010300344da490581501c41c01c029020901c0c0710040302c2081140c03d01e451b508414044c9003081400d840400b020940d136068140420411f4007041c0d0f009002103102c2000b0389281a031666120886d680154000340c0e28a07176140303001d100642030b40c40c00c142c004404000425107985199610011038215a04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 581609820 1250 581608570 581608579
    0x3007090b0603061c05070311040c03090213090201410403020112020a0c0b0c0408070503011806090f0b090d030605030307020a05010509130f020a0305070516171b0a12020f0c 76
    0x502c00c44d41111000141903143c0d00c00156269107641c0d0800400204a0340c500a21a525203c001c1610a002c2d2203401d501e1a4080c0c10400c6901482d1720484c028000d0030f0085e030504c051700300942c04a042c204100c28541094030b50400c03c040100c0241d00c07001003c8050207030014020082800903030303003204131110001c1e00000d015a0f40d84204034100c0b200b0391500c0780101140309030030512140300d1f1020050401d440020f4102cdc4e0080b55240105402d850104c211a079098803000e41d440013250054102c841124020030000f1160368495a0742e001224003194007030455001240740103c0964507001e21b00082c034080340154280483c4c0d030002550b86d4039912480b810f1040000e5070704002d4075055902005001c4900007001a1400e040034100694000f142040001c2d16040c00100d039280601d054070441c4d51300c0108458905c401d07940d0034294055543c1088038242c07080c8240820314161012044184c1c1d0710402504031010709c0d1030011500d1801003260760964006507420780411000151344c403c808000ca9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 581611070 1250 581609820 581609839
    0xf06061806130b0d03020f100213150509120606040c05030c0a030e0c0604090e0d030e071703070b0a090c29030a0e0102040f1a0a120203063007090b060306 68
    0x306440020301c07940310f84503008800c0e043c401091503004183c10070300368481d10550b0342103440040980c0407403043c80c40701c1d40d2210b240c030f100f070010784102c4007141c800705038070b0401525141803080041d040c2d0701c40910104095014070304200c03083c1018000c0f41c42c603803680d041c924110b05044030100395038014050b50408140d035810605040c1081007050014400c00138002a5a694a030040000681483c41b0020906c1c401d424100c40300d03500c0f03842138030401460700c4042e01342d15050480d1070840380d611072803020851006000c0740001ca10b102640d05d00903249881e00054101c514900a28882d0241e844515080441005d04400340856a00c142c1452040e00b03807290780e0b58601038400c0041c45245070b003008030740c030100e004144440110f6100f01070302c83d50300080300e03c0c0040c0c40c0300c8011071150780e00700c01c001141c2e50301e80c001c5005550055604100000d0403c45015400168003d084600c0d0a03440084044c08103070000944040c0040b170040d140d000014090100c000001c10202e01c03002c1c090394022048171 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 581612320 1250 581611070 581611099
    0x12040b0c1603152a050c0601080705060702090417030a020403140c0303040911070f23030a0e010305040305070209040c14060903190305040e0f0106030b0607050a02040203090307140f06061806 84
    0x144955002c0c18010011406080e152010042c50394201da005086c0c20b100b03407000400c20440000701c040031644000c2106241c064a6404c0c4411400e01910032941d08249084e001451000c00d0301851044006101c01602e882c55410f1581564010901c1045070303812411000040f41c502108480584410580202d89039003a2000c08080388507808000d4102d5400000a4041181c035400c0c215010a0302c07150701210b110017107000d40d1288204440f0700b01054032540d080c9000d500035000b19500c0790003420042d05181454004c01d440d001c2c1160220b420803074286090118602041c481d1602c6001610a43d09184044021a0752101519800081d000d18251040105403060b81141c0c0600010b0442200f10b090000d007030070000d1400c2c01500082418040b030705040341015030030360300140e4201008041020705502800000e5201900c4000380b40802c001100128170b130407002c90f50b0f0151003030040a80c8804190880c2c20070901070545481041200d60104802e015140010380020701180c03c0000b01240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 581613570 1250 581612320 581612351
    0x80309070801020d0e010608031201150e040c0809071d0f1b0a0c02010e0907021908041208090414281508030904200a1112040b0c160315 60
    0x115804400e10b50700000780b21030038007000e0b00400e034084082002403140f540c590b0921500d900900c2803940382c5005150041010f002150b01182c211042030602444c1542600080340540d88551a00f00100d00c000b0b0600c030b140c0a0801c00a0001c0619039000000c82c3d030000361003100e001c00078104990f9840346001141c0e1310140c5400c584451000940f450350750b1000c42c40b018054040c16035003079021820100401c01d43d414603090840c4100d040d0781c090000c042104108401c407a201c4070341900c081506100210340c58800d00310101d5050700906025031605141e0f000c1000360303000c40000ba0b000048800138400c040d1540300004011464240001010390f0000002400400315600e28a04801c81034900144131f801c080000e110015064605010404c08081c0742841c0c907440c00900803034418100031030083c0912800100003100d01e0031040d200b0b9502c040c1c031920181e4011707401c0491304038000241000c22220411100101c284401340540660780742d522031602882c054a410740005446803911000c0442 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 581614820 1250 581613570 581613583
    0x60112080d0209120a0515070f08150a060e030f070b25020301050109050114010e0918030d051602070807060507062304050c031005060a12150203010803090901061b080309 75
    0x2000b824612010380500301e080d51700c80c902001600d07036008065451540006210b1400d20034000e0f07807155907095038201000c070b900c0880200380c1c10748501d07807503a201000e5488010701c0c4001c0c6030f190f0325420342404103c00c01d410180d1100d80015241d2102c502000340540c80d40c1a84d00380d00d0300e020780822001c6112010501e0074488003000b581940b03050008202d045507644004d06035003600c2c24440074006c140c4015682c0c0010245410390001c540070010340c240102000041e404450f0350140c9090111424091003a00c000399401c4000440100f201600b03550b041003520010844140100412440c0c0f0101500c43c0c814050060a803c0e00c1d003102002c3c07071079a80c3c410040505080e0640009150030300f000c60312002c508003100c3c07190056000041d40c403046070240c90300540e8010410001285883d0281255000e0008101e500c904101e41040b000c0c445840a1802080f0540146940795803d1040102d40d6005812070360911880c0a40c24252925030011001d54682c00302e080c6549441d68814186400c8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 581616070 1250 581614820 581614837
    0x3040f031809140f060415090b0402090607050a020f0307030b0f15090a1415010203040b070501090c06020a050601060302030c0304170d020a09030b011a0d0218090103080714060112080d02 82
    0x20f080100045903a40701c02e41031841307010121310f03082da035465070020041074803145118010384003814801805000c60b140d000d500c407820b00a00061900e03400101140641c2c00c2500143d03030f03d0b000090108150304213200c42c0380c1c0100c01103002d1f000707941c1141d8a011100d000580340007224034205001820303480d082d00d80c4e8030300e00360300a103500460710386001d0845c080c02d00000c2070010600307410041500b440d1901603c40114074141c0155003410306090080c4070380e42100e081507645640760a6841e010814100c2c6090107000c81c4c0e80549000003260502510b850b074181d01c030341c08251040080000c9240740c00c0560b070b081940500e001d01c148510010300511070044000d10301c4414400500d030f00342d0503040385480c0c00300c074405c1a96100f2603030307200542605061550b01303401c0f01d14000c00c280b0001c0c0105038018412100e0111a07000441d40d0b18003c500c4035003091300300712182c0708002405410301c002030709203802e40d803106c5008000540c102850001380c070740c105c0d2004250400220b2003d00d040ea064042e5000382 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 581617320 1250 581616070 581616089
    0x1091205120304081306030612030311090402190809031204020613091815091a040f0f0605090114160c060f020c031b0111030c0a0c0f05010209120303040f0318 70
    0x7810282440181340c0d001c120425458110303900c00240c1a802409140122418000e07115620402030700c090b4003801e4450405908108104800c039080e598030302c00f42014050b0440c80d5010001d162801030505040030b0314101e0a81d10038000309040c0e0035111021a403259050340c5442d100c2c1e91900c01211048107581002075240e04201c1c003015103c04400103c65168050b0700810b1417140e25807100801c90301a600054100c00d0741004607540c1001d03180c842904148102d030343e8050314003541c035800002440d4031012240b458440e014840c06400034000ca140e4500e0188030941e90741030821450885441a002c800103100021038000140440b036405003900000c0302205541c0c944419246c20b45030752249035021060326928050002050051140303000f002c11000c500741c51a158030800e1500303600a00c0140c4108000c5c1c3c25554006080030042c00c03140c2c2d02c180c0000d07850380400c3c002c00c0b072001031010107202640c6c400c2c001c00000c503803508503030702a01e03805d0304100e00201707100310000c2e1810029400c400c1d0107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 581618570 1250 581617320 581617327
    0xb1b030c0a052523012010062c0603010207020a0308130f14010507020d0f060b0915030606060702031c050703080a0e1b22020310050f0109120512 64
    0x60040110b65421488a180304868203030842080703038407844803180110031300540d00424642d11200102800070b222070f8141840c0d20703890111444900d40710205a0f940509411200c50070303040d00281d00030310005c1e20503440c003018000d1756040210300b509454000c120425043c0750111b00719032400e504031071041c1c1d00907103203400c403603241e05260710030b1b90007a0002102c0a42e0400001218075240d041b0509841007660141c1040d0900c20044070942c202c83c90aaa120500241000000d0243c805250000344a0040418015595000c000d50b40d2402070080300165507041c0a21181c1d9008a055603008030122421a1500c01900109151800444100f803502144e000180b1100d604040a0410b003132003540c85101568030940308001342c0c1c0a8002078442d590101c134030050012500d440c4400c180d10090107040b400b0720100c5a84100003445d245a110480c2e002050004950110401201408003911150020000c100000f00310064901c91808072602d030075031140401030203101c00001c0c0110072001507103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 581619820 1250 581618570 581618573
    0x171906170109120507020307061101020d020a03091101080610031a0d140705040612020603191d0f0607141305190e06010f0818010e0106030b1605040b1b030c0a 70
    0x20100b442054490394101c0d05080e280a00c510202c941c5250b01070080c10301180b0b481c1090304c1d00d0ba045c1c83c681c20325540078401181c03460f101d403003d089480207660340030420300028100a85002d200685050401811004110854441070904000c202c510310b40000c440b00c90f41d07a6140741c24041d2543c1c59104281c080e88405001940d0304500305a26810b00395049a5590010403048407803d100340322607400059610030151803d100910790100c603800020805074080103c84c5c0490703034050001105513250621420320303e40c0130804410320202d0840200114200307200080c090b00d18800c06c542e940c41300043c1e2403902900210b42100101000340543c01c00050409484101403070b1402983d0780c82c00094005040c1d0341c030440a030305503154107071100d03281500c80c101c0c104640403a60f00401c1a540d00e8000d10504d640b000d201c0c000c01180600c1086850f42411b0811441041e00d441e4038804100c0107020501001048070219008205001801c44074101500f5503541180102c0303070200d6a9004201c581c60 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 581621070 1250 581619820 581619823
    0x6080720341202040b0310060303081021120507080409020d1b0804120c020a17120c0c040902010c060e010507020d02011109091f060e0901050117190617 67
    0x3000085a4540488907581c05864000740d403040d445074140c03000e1100b0708a0098201907003c3e04801c02e020303050b25960340b801100d2005440c5c540e4000c030005849a02044512140101d11b54003030400d074080165603c3d20204400442c5540c400050710040c500340e82c4101e014000e0301141c920590040b8010384903903450301c42100941007207040c00310b00d40c01c0c20541c504200800f46003103180822a00d410300140c0b52030301d400030b48081d150b03813039010300500120b0301026a803510a510000c1c850050480300d004107910300b241c140b130040a1402a4000c05000800c015180413504901c984015500003500c408030340012200c1804080d0041e00d114a009000d517540d0106403c0988100990b4080f6049452010012070032100400c09166070b2030030510501840b40b4002c402e0301d030029000000b034100700303e203141c8041c443c058941c03016021a07d10000385800381420143d00b80108000d007004042d20101002ca03006900300140115412219180d504040101960003007015218a0000a003540b500700b0406 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 581622320 1250 581621070 581621113
    0x904061d100e060d06050901060902070b04051506010f030c020c120a0204150f0315110a09030605010b040308190c24050f01030c030b040f1a0f0a0606080720 69
    0x8041d8820103032004124040c9100c00d15004800c040c140c66401c0840b621007000509018100819a540b00c0000140810030b50000d003043c2c43c0076800c00c04c2142824a052071405404016400055203c0d10812209a13004010f81003018032a040c081451600e1440403402c1918040a25510080860354100008000108201164801d035403c20280705440005402c160641c8242400c0c500c2d02e080910014000e88030300e40c202d180e18040030688090404031001d0540080200000240d0110010010322009000b0341d4018032440e0541e0349000c0c110344810240380324104050604200f203581c1c2e000070034030a007030807a0320319001220460040d81550645486d069500d108011107401c1c2000702c0c043d21303441c110343c038100e9038011034042e0054034594991810a80007801a1001603078410400046188100d1040c3c0045d66030407500031500e002c1d00550382c00c4201400030301d41c80303180202c00d00000e900080e0365900510306080901c1c00200340341408002d4851102d5000460040c0c0c0040603455102d511035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 581623570 1250 581622320 581622331
    0x1302120708070818100f090209040b04150501050306180f0708030a0e010801080c090c0d0f020403060c0329060702031e0706021207060b0604170a05100b01080c0904061d 74
    0x2250000d450720194a284540d039440e070004160040c0251781c641803520345c01405101d08004010509202d0780e00014000001180d00f0740d034403030240c0100f1040103203108000c5000690719500300015414000440d644030401003261103200364004d81010915403c119012041d0032150480d00c019848220558407600280c00c0b00000c40c1003034006100c03e60144c030751681038400da8030041c04c042c0b04035420030000d030300003070044218494108038001a111041c0035800103407c40c0c02c00542d50b40d2030352418600311001d030b02514003014601000c005d040c078055903081004040b81130120032102a5400090500d110f17580d80250f241c8240000c1d212642401e610441c12100101c1c00d440c03038680d40da50f00b6600c0b141c001c150815030000802015002811580c0048404607010f031155041c00e032220f503c04140c04100801c00305581c8024032000c20803004201008440380c41c42d100344030031492040003800548000c1c004400c00400410301101c980c48951204000740320030150321000203e01c4011400740b060642d01d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 581624820 1250 581623570 581623577
    0x609020a090b0d08130b0d090b0f13060b031212010f1a0f030702010b150910090f0621050106080906060919020d0b120309120604020f130212070807 65
    0x40006503240300b441401940d440280840c44005040d030385884042d030040044001c4032038410004240c0c002100c2c00741201a41038400007544003503a091000c0d6040c0c000748101c03001d03040c0000300600b080c00c0726905a002e6030300480224070503001d1000607042544010305a03010080c04101038102039007003200309040318070303207140c1d01c01a9481d0101440100d00000e50001502c0c0c3c10001486000c141c58000c40c3d11084610000444001040016a628001660640042c0d80124402c24645004c0c9001000082035040080010f031419912465009080c0300d41003c0c070400ac49034000d900c08440c022031007600040010030181da1540400340c401036040d14055010320030a000541e41c0c0c02c10711000f50042c24030080c008510080c498012000e50700011002c00081d4448802d40519207c1d00c803580f854100400c0594cc5500b000f00030f110506116001d0f01c10503512000620000d6107032a20460310b150002d0b9014060841e0109103080a4400c03040301403d001602400c10060f42d42c820506401200d080d80c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 581626070 1250 581624820 581624839
    0x50a2607080d0e1b150a0f0518222d020703030609180507081b0f0102100e0c13060e010603240902040302010e03062707091508010e06010b09041512060902 68
    0x40302100b0034010703d22020301007400c41c01c4284405009402400c0d42740400c0017496248402c4c400030480c641c01c2c80710036502402d103000301d41034034604900807803030380750307014030781b000358407000c528003c0c42400c003501d45a82e460383c00034801080c144640c12030400380820b4041070080c9103400c0403960300c4900810301a10b150141c0703080410a014003091900d201e003080503154240c500c101d001c1200c10030086459038194072540069805181080c01580c0648407200c01034a00d1606882c103001403407000b0000803c0091030030005011101154140700c2c195100c5103400500784622076044403203400420400e0705107074901000019040055001017007924404e82c2c4280c0c040e0082000d00d0350702c00301034905070382c101e007001d500741c40c154080200c3d1f0035041e03a60800c44505076504d888140c201d480610404c94114009030050003c03140900400c05618149001004c0303d6140110448042c054410300512071912000b0394518403d0b001026000b03000c6d860488540103000745800700061014560883c060b03803044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 581627320 1250 581626070 581626099
    0x30c130503030f0d02162307080a050604080c0a02150d06060c050c1519031505030307240207060507030f05061e120304030b04050a2607080d0e1b 64
    0x2c0305650300b90b90104041400c0100c01e018600183d0016002c12115091120107180405c800d140e450890320341d81034140c064821101d4125050442c990007424007940304200f0350001503c0000d05592107500001c0003030b16130558005903070030484450000f83d408284141c8a0440500c00d4004103000b0007000410410182e03545030139180501a014040e24540058081c109181440256009a800017101032840c00e01404420f5602801042200001940c1d90300c06180c1c01c100030b840c2c04082c0004030010740c2003810b80c0c0c3d5590f03203101901c103030780000d0080c4840034200721600b501507c41c444ea020100b40440c0ca08040014002c0a240c600001002e00b800007090460804078507000030001c0d00c090100c1020440401c0c85404c084d10208a05a84400c02000000c030310081003543c0200e1241024000343c207518101107804e880070010241004a40c0401c3c008001c5034401181c1c80c05a104140c1c4e0745800c5100b1142001f000c2c005420b034007500409041c20504213070b596500448110440d8107101c5451071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 581628570 1250 581627320 581627323
    0x71715040c0605030a0f050c130b1810021906020316030c05031b07080a09180204050306060d0609050105010626100611100e0102031602190b0709050303030c130503 72
    0x203680c040c00e007080904061116910500c0150340c01000004007040b0b402c40f06081c0c5c001c0710800c44c2c0f0920a41800b00e01c030310b501c00e40c0208140041c0402103141e400c1c910090042800f2101d8114002d1190754481d2a10103401e000780030400c0c2140e180c2090314924405805c04102a520807110464151291103403214824003d1042c5580c6452660318642142d642204503154200c007115100282c01050040c003001078080310003000002031517a9012021880e140103280b000044000b861901801840144915100081c1c1d45034403031000c03103559826407014100000207000503c0040c0c095400e042c0042849504080000e4035205001380c12844050a036501d400f03110000d803070b400004148101d0030040b032445800da41001c8903801c0e0a8948001c1019408022035480d04454043c6940200801601e2540010808051001400178200c000002c4440f0000c84a0119004000341c18031008a0000e52082c1080d0016103409030480e41e07241440c044c025465000356140d50b1004080d5040841c442c01c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 581629820 1250 581628570 581628613
    0x2161209030c0e25020a050a1214030f0f040201030b03011a03060a1a06070203010e0a0c0f05060a081b1303110a0f060c12120c0507060f11090108060d050717 69
    0x1000760b0102005080d48641c103050140410440843c82078107145004151f060200300350085c49100717900c54040412001404200047e10a1103581d0014000c1113440301802c001540c0c0502041c611410582c3e491005038001d000014210350990300e45000761951600903140080750000840c02c031a010354030f10241d841600c0400700c81c08000c0302d5a4820360000d0401101400c8860320090011a42020584419107425252041031710000d00c03080c003c21180e40c0c42c0c1c510703002905003a02c4062801405000140108501804118881c06980000030203c4020005d580712440c03101c4600302000d03038130309085008a841c080031030b102c4c00e150302c400a405d0071104070500440b0340700c0d168110003054a8803607031540844950700b0000c0c0102e0f00d52280c4c2500940c8a4025064001d4545944801d8682401b004a516045004000c64039100b110000c0c04080d0040e038542800034640300600c0d03501e1a000c0b504842009000070b00b140720790880803c00000c2a0502021490b841c011541e08580d04054040c1245 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 581631070 1250 581629820 581629831
    0x4020d0c1401080108121e0412081b1b010c030e060a02070e16020c060310090f06090b0906011b0204020702100f0f020a020f090406020c060703020418060f0902161209030c0e 76
    0x40c0208080a090404508004605281c24007c1800c040d0b44a8400e81c2d1214003150440e0140c10024006408865a844000341c0d07191010091440c213801c03816001000d400c182107181440f42000354082054401c0604040c9a500a40f0705901e40410900c040d6a0300c8090003a5840b54411100085411a80740d80ca4844487d40344c1c02401e00e420904180045a4006030010244500107200410f0310074a50040c001031405403000010304603c0c0c40042003c0746d1701c007000140303d05000c4041c417607280c0e030001240b00741c0116012b10400081c0720788005802882001d000941104500074045e0040b03401c031a4030b01c0e112400b0344810400080b0110103c0c1c0301c8080d400000c1d80100c44411480c45418140710b03c95000d840746c00c0040c54030400c001031602d843c40498030100000d030005401c0c80380d01c250000221200c0500301c01071001506049090141001e0fa0081c2e085280c0d01048854400842c403103010015a0025400380c400b45540b44002c0c482c00c0070780000d59055030503040c00203200418101c407a2150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 581632320 1250 581631070 581631103
    0x1b01320604020702180f06090901051b03090307150204030c1208030712021213021018290a0503060f1c020108041103030f0c07060504031a04020d0c1401080108 70
    0xda55890410009410001041c1d800110f96190500446103000d01e060140f40d01c4031920b206841d00f04104000c01000500c0c10707103039904040a11021100b030441d4081540082210f503030322603803100181861400785d140f001d0326040003441c801c50700d480c607503009005483c0100c04181e4469210030708080900d0380c00000504200041000988040c8904c3c0440310100d0484800b40c81e0202c840c502c0310024205540c410b5044824403074210840c034100c00000702500550070304000c41c20b441c144120b80401c0d14132910f01c6201034190042003007d42421910070071003e588200713484800f140c0000300f4070740003120762a009549203801901140303420050701d1812000005ea0700c003100c800d94011a03c00c00b025100b12031503040d680c0c0c2d2222503035090025207002c0300d040425a89075001c81d4042032400c00075174040e0060050030082880403450384040070668520f40600c400c00d54031513201090502c0e43d5501c002d001da007000e5030041007600f54900d0380008030200341d031009203d0f601e8500141e296041d83d030084012 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 581633570 1250 581632320 581632421
    0x1080d05070c0e040c0510050904050703050108190501020c030310290304061d100e100506011407080c011b0305060910090c05070f0c08070f05090106050309031b01 72
    0x900d06030703c400d0b40d203d449042d1509051b6030364008104400440301280e80803440104001c1034a08051165035403000e0a81b5081c0010351400c800c06890f166180011b081040405404100f44502501181c401c4242e0008413580ca10301080c2c03000003c00117004904440d08654500a69000046641c0266040308241c0c549580c48690b126001400d9005031240010210024207030310000500020414043c00e42c401300e155200c03201c020703003418480348200e070b80285040103010681e40d03c10940c4002ca03030181c203c181e440b0746500302104903001304207001c0e00a43c00c00003030104852524540304110701c02d9032000e0003103271a22010000da1a10840d490146402a05410041d52201c0d0704050010030309404c3c1585002c102d038407500c030403001211050314044401102040003447c1004000028421407090303882c07650500b0300150000e8010300c03c401c01c005000c80421003103c018801c0350f0320854014001102c0d802c240300940d000c0c0200d919032112034101000051341c03060b2080071700c83d020940340821108 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 581634820 1250 581633570 581633579
    0x4030b070806120a0b191a0f011101060f03032c061c0212011a0a0f120b061314011107051e131505010f020a03080405030f07080301080d05070c 63
    0x1034044004020590151800e201c0e40c000540070301c11541c085016a6071402a0710340031014507a00c10303d40381e009600c81d00d81411800c8003000c7d811074140b07440044800d4401100c61400403901804001003541e181d510703201c00025109050615a01101e1003600c0703441c0412505455400140c0400041515010020080c0111485c1c590014859900a0a51820480c90021003d812a002030070070042d001028001480040b0041082d0800c3c29a0100a40d207081e040b19401040c5503440040c490500400e0f541c042500b403080c3e00300c2503014102508058503a5106075400c0c40c02a210720600f0440301101c1100b00072540329460780d41e001c0324450010140a8030740f20910440c441d0040d25050401d6030515403543c10f9665101d0075204402604010408520031f82d008031220f11603a0000d4140058201c02031003654011500c3e0b01d81c0e075010706051105035600d0500d10704600c15001c81c0311120b000010318404000b0340310081c5050b1071460f41195803100b000c034001e540c103106503000a0881d040d038070020007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 581636070 1250 581634820 581634827
    0xf050103020f011808010608010204051513060c080d0c030f05060307050a0611030d050403020313150903060216141b0a050303071202030706020f03040605070c150207060908040f15020304030b07 85
    0x204401c6450084e4540f07996181e02041c01c50f08250494402030350001410046454420188070081c0c06a4910500d011255003540c03418021501c03400003400508450001800501d50994411b104914014000258441c1c0b00038002e100600765540c1e45494800414000c2c100007500c00181c030401340c0000003407030602c00c1c160b94581d14100050b14038401048800b003581c190740180c03402070b44250015629044095800142d51100f0b80004c4540c007100850b10314075503480b00c0204200c83d08042c1c0141e0b500e0046001f0582c190740004081c10580c072003000000380341000141841030561020011038000020030410070075030801e20505915130720511618003c15080c50802021500c0750040f2850242c2980e130340c90998100ca003414420681c080100b105000580c029950f00135580e161559003900107035031320303030020414188542c43c0c15808684582044000d600450312a60440d01107903c8980d500f81d892504101ea0040c00040700c0f084ea80e130b001c21b500000940302500e50000480c8050b545040046 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 581637320 1250 581636070 581636087
    0x4030f0c020f150301051005091c02130c050904151212110a03080103141f0b06040e010902130e160320070b010f0518010506070614090a03030f050103020f01 69
    0x40ea40802e00c207020100554540f0b0301d00501c2114480f40c00d8a81d0314101c01c0156240081121a092090030003445006591f20750803510440e04103003020248014a0010841592030403200115540c5004041682e02e6000340141801880403103082c40001500d1040c0c08500d941391190000e05072258640d080007030759424000301030b000e1516040402c003013503440061a1080021040d00460103400c01802801954021003030160b5882c0b0050000d445046048817000c50505800382c10280d9030f001043c484c0d44c640c01114010b0005400220303065031111800d200940c41084c05007100010b20500080e0322000300074541c800d40d0040c036002c004c0084210250013078082d200c0449000c0460f609072002c4211082c002e000468011040d079000d41d07040100051404075540c112500c1613201e4030074596030a43d022182810340d88250703038071034641e0140c2c90003502130074580400311407402c0b8110030400590300000e408244280280e60610001608001c0e41c000c58600f808082e4000c0c442440c880c40c65402103641 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 581638570 1250 581637320 581637323
    0x5040e010207021807120b1c060e01020c0f0f0d09030b040804051003150611030a120f0c02030d0f0519020c0a0803150a08010c1b110411030711010504030f0c 69
    0x242c906000340d80012484030548000c0d000028100080c0403a0651002140c500d250701010200140d0360380c5070000b2843c80b0780051071007843c00b14000d50810040725420840b01001041c00a549580e0301111081e1030b00304042c200b04407845036419200e0301c2103001403e1402d40900340c076984c059038115154000900d000070016140010b04010014250302c1d140419545464960b41c0003840c1d03001240e021509140a07401030007008424080300c1d8031220003000f103a90701d2a55090812034660070b0125034025104c00b800080d038451a0110103a0450340100c014180385981e29410880d842039004218111201070f20040fa02c042003402414a0031401e600038601c0c0c0541c0021200340d4026a900c03c113459000b1184181c5101119100c0801820900411000b50101c00001d00c04169091002000d102c1f5684255600210400c14402401030250b00c4c13140c40c00700a4800c1c41032040e224000706056000340c440710005a90b90b0783c0078121850604c140c5000e140e05503903103d55000910011070781c100c0401c40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 581639820 1250 581638570 581638573
    0xb0417031323030a060207020906030d0e040e010b100906140a0f0804030c1b080f0f1528050f0105180f0c040e01140f1008010b0a03021209100c030b030705040e 70
    0x2e5181c640c0d020000c00114130701c190400360380e8001710303c14005e4108000d004540603a2055010894494202080e141d0084044d140044d07000131808042c0d000d0b04c80020155003250003e0920000c8581c480402c4040d503920703440e0000020f011820b50300c05032141c104401e0005011920528080380b1404555811502034a80404000302c02d03100c2c95100c80c0c2010140c41c500880400402c44448280f02054840309060080c041c0c9824845041d84ca90031038880b014203042000c0000f440441d41d88000c210300c1e04141500c00d04040003007268000900c002e03181171a4200c41600001032a00d071081d441c018034030080080203445d40701c4612246010001400c1d541c961801800b001c110b580c54000c6290080905031402c0180e0101402405001420101920700640e00c205034135080c680c014001d103044554035100c02da41d80c0c1d09007008800174084c3c1524403809841c1441407100c4c03414005a00500740581e400108503c0002030000d400300e9400520154141d080200104081d00c3c1642c80341461a0f40341e030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 581641070 1250 581639820 581639879
    0x60c0f0409180b09010b060327031602010801122a12060902150313111c060b09180d110102070507120c0f0b04140f09010b04170313 58
    0x70000507601000d01580b02c2c2c0003194042030038045643c1c2020380041d00c24001700011100a80454944e200090a44004039410340d00b044086d0000340348a000b000048041c0d945410007400f1001c2c0341764201409a0001d80c070000041440d00001e811a800641d004400d41d8801d0038016141741c501801072a01c420b05111f000000030060b410030303072000039103114032000682c41d034082c030403c148940510039140c00000240304010200d448941a61203c03034104140e01580c0c0401c000040911942d0302034003e0700034464040d6030070800203400440707490000300c4140da81c40e6115070804222811410200d07205500c91074a0074a6140118424500401c1100c000b5141003101d440303c1e031038404030340d00c51942502c546004030180440380b050035021300705940c00094494500110420340c1e00882c0030f1a401e41111510050390303076580440000c8038031009440440d441da1b50780080b03600703074010307225a504260601048c5808410040100d80c41d100b221384089201604046e0302508220484280c40750014000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 581642320 1250 581641070 581641079
    0x3060601050a12090209090a0b0f040809131509020309010e010b01020304050d03090b190207060903030210050c130b1c0e071214010e100e0303040f02090924070801060f02060c0f04 79
    0x22040140701d681950024180080036260581c60184c9c020710900d4a202c1c40780500c000a81380c1d0f000c480090300c049400e601188038100c0108002d20103803c80c241e16074000b40d4001494109500654450b859203402003040300401c486003400d0741c0d11010740c1c50042e0010003041c4514980115800b40450103403400352081a2a1105402c1543c8007540c07062120300703403000d83c9a9083e81000400090a0545000982503103903990195480d803002409200c4180c5680c00100640c400405840002401c0c0a00d950516540d040b0b0f4040c9911179403500c80c004a03010b003015050b40c1c817405165000340c8800b0081020910340103032041504040c6001f01d60400c1014035112400e202401510b0b81020441c01030002c20500307070038810848580d40381602ca81d400c148200404560140181c0d12003680668a5082c05d98030b400c241c81c24442c00191401e001610804c0111306100481c09483c03281d5500c1d00c0700d840603600c03080c0c2610003e00000780c0000603405040045e48094002000d00903100940c03540500b065101c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 581643570 1250 581642320 581642329
    0xc13050a0f0e070527010320030a1203050c0403081b030f04081b0901150c08040f0603021c15181d0f1b0d080f070b1e0603060601050a120902 62
    0x20b20007410040d07880614103008a1800c0e00d00b072074125581400310400f401c20001440215581484090300704041804c5054401d0300b101760b21480034000800750f5000b10454a44419424600c00c61480081d00d480c00007014540c41100301d80030780ea0003401080c2030285d00400c2001c50031030700b0148942c600041c0540c508080741d0348060301c0905640f8010300903401e459401100d11080b07000280d44101c0d08640100418404031481c114241139501d007102c0d4004850a001c1c00910580d8405007848152240015641e83e043d03000d461486a02c04840301e43d01b4400c03201c881501e4440b40c0061030180000c1041080e0880d001840d445003440035070105500200036041241100c50700c42e00c0d0801e4001c56900342040c40f0610204d6910585d281c1c40710604100302004c60003200c03040714010300d06000020603d0203940e0500c1034400c2260301078038403142d078980010141c000c0582e030591512601e1090000c12414075011071414420681a03407624180003c40404170b8a660440900040b060750720ba2a51015803103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 581644820 1250 581643570 581643581
    0x1b16081c1e0c02060402060a03201c0e0705010e19090f0b010e180c0a03021b030910030203130b180a030e030c04051905091002160b090c13050a0f 64
    0x80d40070040403848454412001030350b070301d0081c80c011504441c08000050341d61109403010300300b0620300002c50306442d000300c0190852014080380b03c108003050411004680c40701e440c80110200c80140500d0718070354202075450300e003401031034042444101503d6090400b00384580928a103001035a40869443ca802c1d4200d800740c1d10850b2503d900d908444105580050009010903c1035403040705008901c0c0303e80501c0c02001d082184090000242640307498401c1e0140c1c3e40c10300481000c040c0398000d40d52425038a03800300030b105009004081e84150741500a1081d40d1003040600144003907010166a12450604002c001c0500c101c9550160901e003401084001c82d640e105e520741001e0070032084201480c060342441140d100f11f09182c02c0001c5851100c00b254002441c480d07012543d6295501052700b8000b06520800f0407034170104004440b99003101c6604041030107200d1040382602c40d03500b1141c035040750400040e0000c00004070312488000c1a406160b028880e010002240e001a0000005541 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 581646070 1250 581644820 581644841
    0xb070302030711012c010e03060a0e0706080907050d02040609050f060406141806030a0f12030510210219030f11060909070503070e181b16081c 63
    0xd1011a803601041080000184075039800d00302082c5110240c00c080c600c0704060300c180343c18079500017040710580e40180030000025a00805460b8035203002c007000c0b80142004003055105114100c070010707545000340d81c2c0398001c80001340540103260826003844403100b014203040760401e5a4a10000300002144541402090084651307401da007420f82c00c000545141c1d80000e8110844840c40c18031641e07580d01c03140e0054010201440b41c5541e401c0009040444004025001900088002c0c082004558051682c0f00d02c949040103140c4800e9003041784008640625a66941daa5038804208201742d0741c0048100d00c020003130450315410503201c1e030050381136a00440340404001d0202c030401c1642882401710401c25158682040688400141041805019081800400000b043c90a4800c802600c51010f0107000680640c18035004030300012400ca8060721302a60380c260b45092040d0400803200c16070754154000b00c422650f500c2d824070742d60003a40798100c0d9008000c440390010103a40550740c4480b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 581647320 1250 581646070 581646073
    0xd0c0c0b0a140a060b07110406051c03031401060804020d051002040b0a0e040207111207050a0e0603100c09052b05010b03060a141909060e0d200607080603070b070302 73
    0x2268244080c00382c0c100501141042400e0001c02d200710703070440d8160340b101c0da008a0b41d41c000e0038900001c00c0c02450a6001a60002d1050040d19814044c0200f4494404d1180e5010401070300d010340030a010302420300070000042d204402060161034020300f807001700e82c02030040e5010074600401803000c90381309520050714103101040004900340c2000d11442d011505803019803501c003103a62510191100345484c0e82c4150041480240040020409480075141c00b80100300c1d003030b0b152008201000d0080301c04502c00e00c501d54450398141e600f40543c00d035407a580d44480c1c0d4298205410880304180004c1d1200c443c241c0100700040000d540c040b103503201e6010341c000240c002c4070502031500700000240f120780b4081c20440858080e00c40058165841075090501c03000e280031800c0c01b5405400d1001003c2e24007400e004512005c0c2c040464203910710507040d00c40400c180101c0691b4101c0e0702c20b240e2900c0c07041c0c104a0004112602442c204ca620040080c20707100d4098a403012244207401c8400c05a005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 581648570 1250 581647320 581647331
    0xf090e060105131d1c03050c2208010908040f05120c01030f02120c280903120c021009051e21120406090806010605090d11030c1206040b07030903050d0c0c0b0a 70
    0x20344040600c205c601c2c200354941131110385401104c0c4403052140b10701280105007008040c59558101e020342201030321200000388555006402c008401d034100d40030b55040418896400136a1340340000d0005134506240020744855442d4000640080800c1c112402a05408006a04850841251007449214801e1007651a42c2178a6802100b0210000f03803440d00c030f018101c00182d110303004288107007101d5000c0c08401019802da41304640d003141605009400a06101a104e022500000007000b84e8409440c413884802e06003078614440040088400d802c1241d03008652210302035500880700300d0030304204480c02c0e06e08180c401940f91380a5440040001c103021030511010406100300d03401042c5a152140c100300c8942e00094801203212401426815524108907185c0c41c02c2c0581100d4010003410341d0403101c0750140ca580c40c0d86040b601203440b550701100080f4040c0c068483c0b6640e00d40c040c1d0b038650074200c1c1c400c0404c2c001d10100280000340440400441c0004103000341c2d1910032030b081c1c44003044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 581649820 1250 581648570 581648593
    0x5040c0305220b0c09031c05030411090106050d0203100503070618050406030b060d05100501180e0114010b0c070911090306090c0112020d06080703030305010f090e060105131d 77
    0x300d4646516100b02d40601c0d00400501086080c4250740e00030a042c8070140c0d89003200f40001e440d10900b1244101c4000b21313086402c81e910f030400c01640c80b41307004100401103060140c0400074040303070900424000c51020b2001e02c000c00c0c0940c2c042c40d8028180019010050f44840010b40b403d000c41d030001c40011400041121144604103401000b80401d440c00c2c030117242141d03104030100c0401005a4054125080d01c941441010059402c1800240710308011035619483c41d40d01e902c40824541000030300f010790030050290140300d98041c01007254807901d41a424650b80051a500c0190010307403138812404c010900620078030500b882c00801081056940400c00281401c11800402160098018411954150360800d440340201986883c0c0141e03200070704d1504100500c415000807025206000000c02099050b83c4900d05a544074004441d403295140041c4060740e150003545002d58000c4001040103081c41080c9420280c0004000f2801442d490140e0450b860048041c41060744450305018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 581651070 1250 581649820 581649841
    0xa150806090c1804050303040807030e10080709060219080903030d0c03020409060b0a1707020109140109030e0d08090607060204050d0501060f061403010e04050703050a11030c010525020a05040c0305 87
    0x1403104140000f580c5003440c041d180d0540340c0c000140090b12805000503074204043c81105c520351a0a00182012100d210082005010740741c101e0380140420156440032a54500008800c00e4a1031200c075400b060050036555035074a40c1013102c0340c0340c0500c02400794106c00b21032402050740e407041c541e80040c0c445152540c48002d80d1100d07840061030a504002203504e1560101007440345c0c0061503043d81842c0c58814080340185a60f201c054090103241d0004803a151042d045840300d28004d40e501c0070138451040401c42074449003140208208010000e1602608001010300b5041380158401400c0a40e0784022400c0310380d52080c1111565511801803040c0110008490050711151a0540c0050844018030328684010302403514001803100000301013100802203a400f842e4460240e81592000d850191401ca503009012442400b40c001070a945511450035210506611900500c1010000720428071083e0403100590b00200918804a007544841c09054242d4226a8001445161103030121 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 581652320 1250 581651070 581651089
    0xa03060501090b1b070807060c0203060906070f030c1b080702151e0d020c01021c0b01020d0914030f0102160c090e2107051e0c03070b030a150806090c 66
    0x58148000002c05120b4030183c40c05a840b80346a07090030391000314031003520600e026800d51008009101d0b1701d80100300541c0c4401d0904080340f090382101c2c410303224184000e4441c2411160200010b0469000603401e0b403090308401c404040074140500b40002d0110f050030717400d040a9003900c4520f00007501c801103041104060600c1407210b440d0f14280300021040c8905031100c00d496540421011405401d0003989074100c40c24000c49400031941e4a2103000201080450411400310349407810515000c0340d40040740403080c040303442d0303211000c0c14102a4203455a02005020b1130b018402d018408011010034401401d000404007406c2c0d14810031454101e46d60305094019140c000c4c20f0640c0c12520484c001440c04814100d000220483c99407403210300d40b203010b2000050000d01c9101400100840840c40d00c90040c8030304c8007644c0c1030395089410f1658640140c8201030603c03c2c2000010300c03100c080d030301c101c1ca803907581904d5000403955148840e10b0618140c0390580187c004486ca0025407404101d03d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 581653570 1250 581652320 581652329
    0x9030c030819030e061b1306080610020a02010c06181703010f0501090f06080417030a06051e010c02011d0405010f060f0c110f0f0d03020606091503060c090604080709020a0306 77
    0x14000071680c0c4200b20746401010b0410182010070b060001242481d20b802d481483c000401c18509282d0356101c02027504000359800d6004810b600241240b26101103142d0314001c8c0c040e1100c18030540140c4d00c030707001020104401c8028140b00c6500000280e10341501821400259154507165410910300b40c061403499031215040c418081001c22105050010705000c03a0310504248d00107a5031401c01000221003e89404000c100003c200210003102d540001b0603120706883c1d40640d90503410b0324003420000b03651010301242c03c07568400015032160114030300d000c40c40700300c017107400c0309650104066070707005c2c3c0101c4980c4524080501000d41d01ca0301c07003502403080b868104401d10031031b29402d181c0c1c05030458039070044102e030001012646030305807001c0e076414004e41030044100050034000c0d240c0d4411ba407403500c108040408210700213a6103028510044000340a000781e0b440d6a407499645501101030310390030003400c1c800014130507018060040140743d540c0700942e40c1d0b1984e120040803540b1741d400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 581654676 1106 581653570 581653577
    0xf03070302160e040f02040e0f010207030c0204050601050f0d050901061503050403030c1d040b03010b03070f1a0a0819091e1506030515040309030c030819 68
    0x40c18525055841ca00030102c0b600d603100c114048005841c094020108260b019000d07103001c5d8407140355001c10f2011140444000141c590a9811207401079003c280600c80403400c2d81081d02030981c0c420003d107000c610f0503420300c45440d21402010508080305554130001142c03002d0952013600a4841004445402406a01e00401918040301c04600180c24035615580b5540240001d0560000d16407584404d688540c043c80000e0801d1a4400c1c0d0541d201c5034101201c0d02c052100b00003901c0044132045400342001c00c0b80300c0b0304100c03407408100d5810070860204816030040c0315603007024440400f40343c29490340407d50050403503414003808904507410b20342410a074035491300b03840d1031040c040d200c3c9100c3c005e5074000032a480c611014240350044d080b20511748a0b00310004c2d0b0300505c6402c00c02c10ba0764590700c5610348500ca07904210341800c0c000458035a203a0445403004030407909440d = true := by decide +kernel

theorem cover : BRFrame.Cov 581474820 581654676 := by
  have h0 := BRFrame.cov_init 581474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 581474820 ≤ n) (h2 : n < 581654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
