-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2973
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:17:55.384721+00:00
-- url     : https://prove2.me/submissions/cc89c130-42f1-475a-8464-79e479a07886

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 534532374 ≤ n < 534712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 534533624 1250 534532374 534532391
    0x1b1c080301030b09030304030e190807090f05250f0c020415030b060409021804020612010b0d05100b191404060306080c0901060906080a060f090e010b12030414040b0301 74
    0x182540d6000340400c550b80001c030804100b0300040041580c1c42940c1c961260102040e5540800c909101a58210610301d80314001c0407075504c0040c0318040040107201404a45540344070000426500014840b4801665030b5214484480e426215034001c0c0685083c00740f1070651816080b16461035400019400c80d04190110b00d05250b051140800c6900410700c1000ca0385401c002c0105907115030b20040c0d8802e805540d921103210030200100c2d046880100300340e15140540c003041120b441c1c240d004074561000402c0e000e0401120340960f603400410340c148410201e06141461666006030440944108250040c0082d01c03400341c81d0300b8420954821009455559030303207004015011038060500d850042401d021541c0c1040d91015058401c1500c0700010b040c1407200441e43c411008150030030450f00d44000003942d076200000032010f001000c1012030350040725140c1d00c3c25100c003814070601a001a145054600c0404400c1c3c40a9031400c000e468550101040090064000503c500340c0c994a0300d40c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 534534874 1250 534533624 534533633
    0x1101021b100f0209060d050604020405030a0807121809020313050304080c130e030307080408160f0b06010c030e010c15020406080105090c040807170115080304061701081b1c 76
    0x7110400e18290300500c07580390a02c48640a90141110880d0040300a02c44015580a9a00266400440640f0050038182c0c4c950000e85803c1480e003051755152000901a000d212440c01c031000c0c14500ca05007040607107144440c088a100082c4078807006141d0200c04100ca29000304548001305400500300e91712543c44010311510b50307812110041c4100480b5071826a6243c50b4019a004401000042c509644e14410251032159000f0011940140100a0342d0135a1942c10511506603000300c4e60f0354102c6400c1e02c0d01800240c0c001e40401c5c1400102c00d0542e0000c2e90003035194450074803c0c600707071a03a101d503031911210340c0b41d082c2c142400311030001c1404900c155000030418121241180c0442080d215050b0400c40c03882140600401904492400e00c99680220b00030500350810400004410005404410791101f00303400c150390a40000404201c01a803041340e41840c401454503a0301c1d83d5251010b803070394800d4001c03401c2001d40b0030314081d01d2850751503000340e803120300d280b041000e01c0e080745141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 534536124 1250 534534874 534534883
    0x30305130f050123100b0903070308030a0516031503030e0d060e030909070c1121151f06020c100c050607080a0c030905030a030506130f0b0a05030a121101021b 70
    0x1451921a803410074503013240350111203821300801c0018051002d460402a00c0e0b4525801800d1840d010b01c0356400010000d5100070040d0b100b6001e5070030001d1242045040c42041d1030002e40e004080500301000900884440040801103039410700702108100070000200b20104500380300030f0000340c505034014030030030740c007200802e20003004440205090740c5003d0203940240c0041c00143c80785031150481c0d260b50800325485000d100031403510160644c1c035503c0407441d0042207441d0b0701d0113812400c01c0c003035016940350490012100d5040c2209199091440c001d642d030402c1500b140c4500007812151482c18000c1d0046c4a0345500401034481c076242004024007140320030380d8007841580c5040c10741c0c2c800070320904c580042254098044c5207080390061085002d01006040143d00070281d44d920091405a0b22030b5800002e0311074008180010034504000d917100b02c550001d402a081904000005200414030807075200d0f0500707044441700740e0040200e009010f654070a0205c88110028201428000113 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 534537374 1250 534536124 534536141
    0x52805010503070f08060708090c0a060c0605102907121701050102061501080403210902150304080714030712090503010c090f05060a0512040803100f12030305130f0501 74
    0x24211203c282c0d40e45816003198000d80b14503e4950032240100318158440d0600f00d4110400310101c0385030640000005d106c881e001d900500100702042c0f4a1403c1003d40e001e615030061100f0480540c0b01c0c0b900071000042222a90742001d01f41050728002150600b600c00d0365841500505090311200c0c00b1600a812111420f0b00f03803070048420000084e566100098052007407000c69050440c00c1185801941c0d69500540110280300030480303c501840c48241e40e101c46801000c0002c2494212401030040c044221491031404180400420001c01c001504440c0d0300c2c0d034481c3d108001440e0031034000303045020303220f00207102c106044000400558411010402e0701e00c124020021640c1c212000c5d2107425440c8503414004809907420400c0e0f2800c40c01501101d41c807030070424a000030703140c0340750100f0f0002c0310111070244000c070610000e64104041400a0824400340d400c0301d41c00d2124621056041e28402800c0607103400c0010746000750400c2889070240e102603071621070a19864079601034480b44 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 534538624 1250 534537374 534537379
    0x40623010801150219050a0203060c0406090b0f1602010c121205071b02090901020706240501080108060406200316031a0a050d21030c09140609040528050105 69
    0x10010889007041c0c0000306102d0f8958004203580300c0110080d4215003003182c0b0503a400d0043c182c0c10805601d0a100d640c0c81a00341c94050799070b603402e2481c080c14084c0755030803074441c070442802024101550141207551030366911140e103d60392824030049843c0ca4004100605400b007080e070200340386411040e01c0304182c0141c8400d100f40e5841c118101c03001990f903105421003440e600c181d0783c0907091001001383c015200e00c7c00036192400d280c58000940f8101c1c210240a01140100c0300702d04569004900c019010919011805516000440d039071201c024201514042d55104800e420400c800c0001c0d061a071568030700d980328984040c0302142c0d106404142e8011a04010100d9080c1f500c0f0f250350a1041d100400c248800750402061103107120160300c4c1140d403003c01e01441c020402c1b980001c45a208a01d40d0003140040718440020007000c1c40b940002030719038140005550a50b254415145850030581e40083c241e903580440075495154494000c0345800b40500b109001d000c1341c0c00a6045e900107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 534539874 1250 534538624 534538637
    0x15180606030201350a15030f050c0109081b03030913051806100e091912031407091e030b1801060806040506060618060a200606011d04062301 62
    0x203064000500c1212050548001c00c902001d60b01d80c4e00040811942000045200240c903c00c024090f20b0001d200b50400d4841402a80c00c4004000080180c0c1c42c1e041d00c2864110320082c54610316650f100560744801401d00008040e5030a251810819901402c400400001032019030581080042c04140c541903207215504032561070303100e4009051401b62210340d030202480c2c0e21f4501d05900442000e013010f80c2600031f000003504000710283c01c1d052803501414070240014800040a0300325552080b0401c81010038204000500c0d801a0300e00e8100c0301458045100c5400c00d140008900800c0c0d0001000900c480041c80041858000703840d50301000c0000803c00c0c1c5880382040c80c2c3da02011100180b007a400800050b0031030503c1d0340507080f03000000401c0089610f0980009010b81c002000b86800102154110200c50064900f15001c0c00100c0300038001c6404c00c0c0300001c01e1a140d0040760f01c1001d400c0c0007044d4650310b6982c0048010016440401c265541e046d03100070f00b00610420080c0028003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 534541124 1250 534539874 534539897
    0x70209070509060d0f2d0b180106020f061003120e0d15061d100b0f0403150c12050f0f090721030225050d0206041d010501030c1b15180606030201 64
    0x40344906c11090001e22125130700214800e00c0100c09000b2010120380c0250813100003452800391400068040c00300d54016040368071480c003000f8038010005100e142050340d50502040810b801035181c0000c0d21a9140c0240c2c80462040844d21008481d68020b00303c0d118101900c0294170b481c0e10074002d440045501d40c1114003001c44400040f0002d81d5028090340070a03000304a0700406800410f10021740b1803a085c10140d0300d0710780b01000c0f0054104910351070303107d030b00c56508542e00c44c0307141006010b001c400304054107010200941d240001041410703101300d0040031590700301c1308000d0f1000512034000c0d514200900358503608030001c544101100940b041856544000b2103003000030385078450403440d030b4440525003410018850307106101a0303042031040101044c808602c140c3e20300c4000c01d030980010207502d0240010100c0d60010a60750400c0200200800072189025400e51941e8101c024400da0b103c1e1141540000e02c0200c103440b6000b0900040340003084600d0b00301d00101d034000d032901c402050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 534542374 1250 534541124 534541151
    0x3030902062d0f1204060e070306150506270406080f070e0a02090d1b0308030403030b09010501081509150307030309030b07030209060712020a0c080703051b06070209070509060d0f 79
    0x400303e010f1074112042c040340d041051080c1d1580d0b0300a010b42000f00e80c65144100c02c0303040100542040c1c510603118032202c029007000f442c524000301020b40781e10b407420041030b482e0383c86480002c0c020340410902e000c0c8400640d846420100240c005402520801006080d0303e170340d507205912612100050380b00000b20544014420740d00344000142c105a058052aaa5403241d113500a04040c030744503914102002103131004000e90310481c46910000b03401c06040d000c1000f00001684040e04010510003084030f800a26071046800d0300d0245ea00540c0d1746c603402c01d4542140c403003d01c260b40510039614000185644840310800300d90040d5203001407612001c50480503480340502e01038000070200042c0d400140703100541c83c9010300300c0c070640d080101c203a13941d05603203c583c1d48500069400800c05100b400340c14040007601c82103c10302034403c048800301143d1300d4014880041c2c402e00c41400010f245034054000c680d040c003001495140e0b119200700b020b03401401004a0140214540b070a82d070020f2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 534543624 1250 534542374 534542377
    0xa090219080a0e210f1b0c030601030c0603020c0f0307110a06080403020727050405071a04120809010212030c030403080708070c1506030c0f051014090402030403030902062d 76
    0x8010f00501681100804150500721080440c0c82d07100d101044165840482d410241840800314503c041104a803601c800d894105801d0480d842900040b00401c0084d04440300401115042c2c14003503125092101c4680c10540e42c540c1d40d140c503010020315402006151090a1503140c1e00b2542c41341c103184c603074004030f0311200e0484006025034000304040c002c03010340c00c04c1c5e0f29501c0440704004010820900541c0e0079107406490445542c0e001080034401c0c0c1c1da140c480a0300040e0030325149418181713820030400c2d001c0b05100b00580314810001da0b102050b482488020b850780000b9881d5136070b905000f1010350f615401102d0940008401c140401c8209101d5203159008101541c0c800e6103a003469159410742c590901180c2e560642c1d1207800100241c40301d82518000d141605081c040c00d440c28060202e1b420070156030008000c040e110008141d007441c3e041e610340e40020ba400584950b00c40c40c0039002000c0030b040103540000003003500b4000407840c1c196805951070070f1200b4000c0131040e144a0440303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 534544874 1250 534543624 534543641
    0xd0503010e0c040306140a051f140604122f0108070305151c0c1406040e0a0213030503030702071a09010c050c210d170609060a090219080a 61
    0x10020401045121806228150050750a00300c0c40c3c40d240d543d40d1800101c034013410000f440000400304104481130503205e801d50002e48809112060ba010440c603002c4200680230780e66074082440a41e01d20342d1580b0003514003500d200011409141c82c64240b00505a91410050903002642e004100102c04031400380480f598040e1202d50350b0b526003070800d401030000140300389405004a0403420b4955510381d86640c1d0090140220b10041c0c4075030070030f000c2010712504040c0c0040e00c10145460b040c0c40d00b000310f60807900d544003902c04c1520b90b02442c401030b10841e0751100760114003050103c240b01001c8001c0d40140c074681c00701d071030040d40c940146600462500c0e03018070801c024007a405455000e10104047c191080703040d251142089000104180309400c9401316003000000a240d00d5070081181d8400011182441103011940072901000c466000782407500030319928010070040d85410b103081c4050f105100065484602584098241c0001c03445d0712000a422580424004030207441498003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 534546124 1250 534544874 534544877
    0x70c05030c10030207110907270509040305031005040f022d0415020a02040c0309030807111e0307020d08130911031501110601080a0c08060f0f070311040f05120d 71
    0x5010410b406030001e40107840155001c0c03000b804102000c0d910101158810324661300c44100218070300d00d2002e03541d54013585015943c03c0b842410702c900d42d106041c0301d44c4564940341c4142e403665200b0083c2c0b0000781c0d036030282360090304200c01d2440300318080c0c024001004102a0f06051445105040e04059881070781c884502c071000c12040c04204405c44040c078090955004444d0441440c2e400b0800b100c0682d03001c00b000070758450710281050740c01302c07806403c54000d2400c03030071054143d45c8650300c031805046d44403040c54004400d04201c49050098982558004100740381c03c41160400368807507884640c41143c1c00c9041200131501303918501c5040042422040814110f94812005844840404217164140403e51341606820b80c000c102e454080e20200b405005014040e04c0c01c500409140c0e00400c840b500000c08000c802c6140c10640790b488800040c247c5565150071300d040e070007043c2c02c03400c05c0c094100c0010003203100c10080c000001111030585201c00e8030b40c070a120507501d0b0360241c1c64220 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 534547374 1250 534546124 534546139
    0x13050d08011716060e0303070c1409090703030206151809160f030302031b011e1b08130204090201093503120c0a1803120f090503122d070c05030c 64
    0x84098030a00e208414941c001e8103c03441c040745515009e0881481d90702080084449001121190422240080d000051076004001d4a401d50307501079290303040200745580140d56000d0b4096103556054203d02000b081d4545c0c081982030a0700d00a4a58203001c05171030940d10b10040000d0307611922544201201c0e05540903500704202ca6800b6a00d000e055041681c00399200c41141c0210143c61059000807a00c0d0b45000a10007142555200c420b4400d010717020522461104000c4000141101c41d8803040c1d04840000d450301080c401646c00b03140d150000d48005551224009044685103030000094806100502d000d1442c98a8503079030344640c0c6030600000070b0080c007007010142040003501c01c3d0b0003581040e00501c075a150406148003d903510685480340c240110640c0c41d40c100241040f140440c0c602450002e0620020030380d2403a0702000600c54540014021a0105140c0040317004030f40124100d0a41c4003100700b00c1c002540001000340e40000452070002482c2c40d0018141e400c1e50006030125 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 534548624 1250 534547374 534547379
    0x100c080105030a0611090a06021c030209211203070909180203070b03090c03100c0314090d05180303070516090504030801051002030c0f07260a060513050d08011716 72
    0x11004d400e072089611840303001880700740100e5440a47c0c940203400c40d40d0003003845c08001c40303644586011400151044c188104094202c80d101ca880c10445146000290740022500e4094240b5002c0a80c182c92424400402800861361707100e00e010f0300301c8841c0c00c8103101d02c9024202e85201e5140c1140300950691091b00300301702c081c0c01c034000b4550100384102901c501c03912081c0802e06060503d8095921760396901066041c0300d80510592403082e62403c19100c41c0d18000b407044e40c1c0e52208680f2001401404114503031440025903080001036409030940e901c0c1c01c000c1c544070369030f48403101481c0c1210704485c0c0e01252240d4180708a5200320741651b94000c05074030b003601780b00c00410088442c10860004201440030b440b0700b04110050b104030040108001854203161b240032185c1e40000c08616566480213284e54440000c1e40020320703030480700014003526113201e4401020a1140c000f0042c1c083c4451411029400036000c50407034600340070b414004402c1c03041060f100c00407000048603810413080306 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 534549874 1250 534548624 534548633
    0x111030d0506150d0f06120515090a0602070f0b0115080417041e06080105152a06010602030a0e1008041101031e020d0f051605030603150702100c080105030a 69
    0x2160898005040100c1c0b5840c403500f8a0016486040d940440e1611440809646940c40c8a28401010301c81a04824400d00e6174031a81c81c0d601e04101c0c1450071340980c1c041520480244140700d815540140e04540d29051171030182c61300581c1140980340f0680020000a040260030f4001100b082a55511200c035925592010154240802c0790708a140c000d2001044030310380d103001400d5140050300e44403010ac0c5001801404540c058109a02542d01c01c0759900f00c6440090555000c407003074400720740740c4007418080d0308034400000240d50f8481c415000001000364010005010320002a0340307007000d5010301d10900c1a05007000801c840001e103068001404031302c00000c0100b82440514001c500f160441d115104050000380740c001000f03a00186040c1c150b041c610520103049501c110174000351520a10000e0a1351a45d0307528024054000005250303544c0c1404040c070390000b85e600c40422800c0c48071000f9a1144000704001c0601d04d0820741d510268001d0791014101d550080050400e00d02c01d60301d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 534551124 1250 534549874 534549881
    0x105040c0905070507060915151a0c01020906040b040602010605040219050904111318060308030601110c0901230409020f060721020c090a0203010e070c140a03030b0307050111030d 79
    0x103d4080110030710a000001d84540078078401c40e03002d00894410180324512100865008101200d0058000c040030017810040f1500241e07400540c441d2203480c3e01020f07030814064403c110ba0140c4c09000010301040d900e02240190098616a5000300521a203c9007404102d02c40c0b002c2c4084504a400100946d05216100034031068070050004260380d01d180800740460781100c0c2e016002c4201c0510240100340355060200f240201480042c8005442c42c1c640700c2c0c80344009011744d8100446517000c002e418404120b000302420000d0410f6061b9a580c40011200d4541108002c00170324858400b10400d10b4940030701800141c0041c11030180180e40c004100c82640940c20448230b61660b891590321041402031206c0c0c032100550040c0c601391441b28100003004500402d034040c19071043c80103002c0b54141c0241c140c0e0016080c2003085d280300e0b40342030030903140c17118002d1450644078100181c420103906800c518803504040d4110384019407210010340c0e90a00c03c4000e03080540c01840044c60300d01c4140c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 534552374 1250 534551124 534551131
    0x9050d14090f0301020d0f06140105161119140406080f0606042f0306040513031403061203031305011a01080a050a180503120618041407050a0609050a06020105040c0905 74
    0x800052400e001e2003030000680b000f01c0d61f442440c80d034844080025803000891501a00c100340307089450410303d9240070b0030b6400c1d2100302614920211208000d6a11182070807200701c049441d120700c0990380c828460204d82c1c0301010841c0254140900014101000601c9800f0500e10b44007820081d95140c050000038020840c0201c801140c06125510100b5040c100e020f111003440001640c03813a04900b070100b030390405031000b1920800c4401c0c1102280c0e00c03e841e640caa04514509650340e40305d15000511000d550212600c03d40000801d03c10480302000000f06540d00c00d8000f0b2040741020704078100240800072041c2e002c59500310009002040c03980c4000d5008404000000342602b500091052a0401c083c4c1152240d200080d0780010503403442ca50b50340a0000c441c0f041040c8844441150b20203c0030b00000d01101240e2501554000180280303005000d0291980e00d100c0d2b55040e0007881a81c541c850396018441c00d880102c0c0c07103841070282c04e01c91078110080424035450440d00c0e40080c60b008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 534553624 1250 534552374 534552379
    0xe01030b0a0602010203102c070e090108010915060b0a03020c0307170a08010503010903120504030207090513021306151d1306080609011b030b03010605030f0109050d14090f 76
    0x1502146441d65490811002811155000607140d01d08030180d92481c450725007103102880008c801c9480107180d1005440e6003120000881e80c01c686404805403288200a000305030700c1450500040f4107120150b00c400c00660042e10007036100c2306214100c4007224204c1c01400d16000003001403001c89030090700100401ca0a10045a19002241d00ca00c81802c055240c080c52481002810070f90f10390384107048501500d8110000c200407089a43c025000f10002c240e0500744030746950004c0c040c14003d004c00f5009203060324043c0300c103140400343c80d0f04c00d28108404a104d41005c0d40b800c14003601c0c6200d02c1043d500c0e66810007032800c0310020199490400e803003614a42c1c4e28550441c2c42d6940700c1c094070b0021400d8807800031070641d00f4014120b0130050000c2505240d1380c0740a0020703200140240c404a200050390030300280d2a81c1290102e80901038542081d0b07054400c2002100c1049070550042d0701b03a600980a540c420240d00c04200d42c01007142008012154040c4050420f9142001d5402c0795000700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 534554874 1250 534553624 534553631
    0xa090c0e030f0d0801090c0c060504030519030209040c0206011401050903120c0a12020312011701141e01080a032309040e0106030b0a020a08040602181e15090607030e0103 75
    0x340000a20303085800003150690f4014460110074241c2140420303015208100080c0010024110010000c9845981c00b500706a201c90216082c10f0062080385c112502299552249001c0040040d010b54040245640542d00e458145400c0c7d600c00304055060340c01c0404031420050f9680e00451f100e4120b81078140e40340c043c251103104926040d0008006000400c405880c0840b550f00b00350480c00c4660035407009641080043c05258641c022800d81541c0d0407084801002c3c280e50912801800300010a0715410110b0041c8640d4940c00043c4041d04083d03030703650760802c1e0f072075002c401d8540d81103020090100b541e0400c20441580c2c8209100d59416000d87c0d0035050952032400141035030324046021210b65512081441804084080300e588010700305c400358644442548000e100101c0103002030700e215408950301e600c0d140c44400c0c501c2540001460030f00c03442c011060310345641c8600d00c020f034880c42964038145062100705080e00e036060030082c101c5051103a00d4400355030340158244440d04040c0d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 534556124 1250 534554874 534554897
    0x20d0809030318150f16060f020705030d06050402040501020312090312250305090304170f01060e150a1a0714070f09050c03101203050909040b041a060a090c 69
    0x381000034103a04005405407040302281d00c0140710810b40c0c4c4801e0702250390010880341035030605000c11200c0c0c42c89070506007460203a0030f040c1180100aa130000000150000440300b0600800102610050142d2082040b0003569802003204900c00c41c1f141c0f40c0540c009002030441d0710b070544030711503200c820202600d10784030b0280d0301d40c90440001c0318004030f562550001c0c1c0c0c01c00010b90381015022151410304000031b04140b0320050382c2c0e020fa0b1060360010030038034008081d0000c0030701102d10a1304041c0000e005a58486510900707004044a601c04001d0b0041c9800c9441e1405080050032221004c441e50100ea003201d4441d001580f10f060240c810301d0143d80319507072400c0100021b10051000b0444100c5841c200020a13003501c3c00500001c4091100384203000301900c40441407012142e05401c0d84034101013524095501c0e0043c09040c80c0c2c0403111070304000501c509000210f2243e44500e10580e4421070341607044c88002016030343c09800255410045c0400c41243e80020107122003401c00c00c000b084c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 534557374 1250 534556124 534556129
    0xc0201050d3b010608070b0a03060905090619050f0c091906110c0108010b030c070314070305071509030c080f0702040905010603290411010333050d080304020d0809 72
    0x150702003001d90141003202d2015203a10400e4025801500da581c02484904c1c60402802da071642c640c0612128050006030780c800c030740d010754021002000b5a2005010900c3d22410003510b4010890300290b042c40c0c101c10340e401c003100314811103114000070207484090b6203803401041c001d9040107142d1500880f0010304001d0900b0b010356610014299540d4216049056058a07030900e1940e0940301e049c0715525005014185000302640d501c03925074070030350340c442d2450b09044602e000e61948907000104006210001e2503402001803142d1402484250240c00c614140c0d08101d8001407406000980000c40340740c0000c1e001801420000c0c0251282030801c48a9000a400c80b10000700490b1107030f554080c200708004421a006400d10344403045c00b500115030982074400180c005200505407444a44201c10300e80c02680a940703901301c484070000441414102c03c550043e1090054a10283e01180006451038280848140c04d0742c0022602d095807259424490a8102074800315071025040c4261442c68 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 534558624 1250 534557374 534557411
    0x706080c1204050601090e010b01120f0603020a080303060307060906081602100f02030609090c090f100317131e05060f070611071104090b01050d0302120a030f0f060302010c0201050d 80
    0x1540980042d02085d450030f03189000719508000702118503410031b006910300360b030440c802e1080200b58000205031461929000d00042400782c10080d8009003038080419140d1000015610800041c1c0480f0221922f4007010360346000d20744151000a007500000076005000200e03045440205401100e01c59945004803406075918031642e00c2d0515404020480c40d03113401c40b0380b160481c0d0b5150180c10b13081209404100140030003400b9003100c80c00c81d00820b2603218a2020702c0e00854200d000781c642c030700e10000c007050140e200c0252800001440303c004503410b582000c131038200c26842d00781c000415140c2814030440da0450b0381854010101440001d02040c6580120982d50030444501d40d0781b040e035850050010740d0144400c0c7d000d50714260360b00c800550300e11656819114202c1d50012811100c0c034040b0302d010840c50a581e000000480d880721100c0d0950086040400302d40d46c117000c0c0c80170600410040320004e20000e40002d141c0d40d8580055401740004184800d82003402098992400742c2c0355011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 534559874 1250 534558624 534558631
    0xf26060f1303110f16150516260309010c020114270307050705030f0712201810080604080301090b010c0c0e041e0f0206090621270706080c12 62
    0x80c1c1140e48900300c25040c14083c817004d45001c178405c4108803490900286a400ba09145c10041c55494020b1801c2c0420000050360180e0422061084080172200045c1d2903001641c4803062582800d41c11070f40d41d0700600075228410b60005800d41c003555551080c2c00f410184a80c030064400f071407042d400000c0c0c0c040c0014050180280300400b91685042d0500d881c04145545040c0c050b00019414010000a51405a540e5401100c07480000141c0035640c0ca486040101865000d5281608481c1034101080200d11a280c024461050983ea0714055512094211001080c486042005102c406010303480a1507050040c0750141100440780d88404800410344c009601a030090703010031040114280322800054060101c2e1040c0408a5803010698030800f44000d21420700460110759a0329104241d811001c4403594036003000a10108941c070b488410380c0c0c1c844507442c1500841191007007070010742c0d4486501a008005051900d441168100303c041c000045c3d1600400842e1090381d581c15840c1e01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 534561124 1250 534559874 534559903
    0x120030601050909012c07020c01030f0f15050909010c140304031403010308031911070b0a0b0627090c031605040b040b0d1a06070305130f26060f130311 67
    0x503280796003840b52003c0d070341900e00b06d400507400c40100720029034007191000b0602c03030a00340852044440700055003d000b140e20030f080074a140c400030a102c021502112412540d05032801400c1c0e031115600c4c5420f072410424140041071050700d80d00342d9250070f18010b5030b10600034503282c0d8402c00c4400b441368496100707034020340340c0313540101c2400109604401107201d00804003108205c0c810310f09941545501820318003601490307809002030300d51b250315005001d50302801004542c0d2401110700d1581d0f20507040b4a4000d00316004a043c10090501605140c020003840b150f0074196030302c004200c09038080303441781c041c1041800d10001461111840c050809000401c0035070b41c66031246100d8404a03400d90f9804100000c942a07220b010b51245000c031176800e80c06240250361400c10325000d004054042e840b00314141c901c14070020f40010170384a0000355402a800e8519071085d48070310190366410540b00c0ca810400d04030040380c2140c5182d68070701c402c5407081c14078142600011201a040002c20a800e50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 534562374 1250 534561124 534561149
    0x60b04031a150a0501080a14090a140a081606020c01090809010f0903080d020f040807090209150c06010627150e030a2a12030e010809012003060105090901 68
    0x3204680e10701282d40c40203040c080c10041c000207100240d0902d12902c512818403070b0110100300e036048980c121000e10040b20340b4130900c5040c181c0100340c1d07901b0740c500c00b500e0f105510621460341c3c18000c42c480c02010741001900307041c00140074804100d010401000c550003a0308010700e4100e004280903941200d402802443e49400f4044000350070440303210f42410801c0700c07065080c00040c03e150145c4d602c0101a00340140c491480b00365007406403003942c010740d41d98400c0f000001118007040e00180008a03064841551692802200f48268025074070400c80c1c031782224006100c2c80c2d00c10004030080801e140d00090318401c1860300351445150341c0c1c10203103250440510700c040c45504201c052040d00c0381078006004040168881c5400c0314101e511120340c0060200e855500405c0102008000d028803501c0141709071124031380030300781c919104015404500c00c480001c45503813044c4100d072400c4081d070002d828440054410720810764002048141400700c01d01051346a9102c0402181c080c1646581e02c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 534563624 1250 534562374 534562403
    0x1051b0118060509010506011409040b150a09050105070c05040903030b090f01090b0f0604170f160504150e1609080d0309110409030f0c2112060f06021e01060b0403 72
    0x150b003a91002403500f0b0031a8103042c213002c0d45991221486281c01d00c56902140c482190600040181c00c0c0e5404c22a40400d49160b05200500c240c0e00501450000d5200d601c8425519801580e09000e000400381080116020400050501e500b21080c45446460b0004014039114001001c0c540161080080e10006000600c212000c5110b5107a0a04040b40d40106c49840030001501510450144484080c40481c07114203004081010125511034042616142410690085c840f0940d40c4100c610843c1480100040c01001c41c203000c058940035504104259101c002400c0040314640014003080302d000030000315000709210312060304007947e40114502c401820035074080107600c118613120b50b00e09018480001d8000d429603008800c41d08240100c104142800901e00409440c2010010011010081007507401144c810401c84001810044151601c00040249401e4024040943e202c6002c554098041c01e07007401c0740f080c40340004203400e51503601c8001e1541103603104581c20b00411224 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 534564874 1250 534563624 534563633
    0xf09090515131109060705010e030f120f100611070506210a110702010c110901061119171b0102122a0a08071707080912030c0901051b0118 61
    0x2202d00a52100014400c070310301c0003800006442003598032032044400040c0030003000021341006039a200350b14203036070320759000411401c0103600500641e506010550000346038603a01000c0319008100e03116103003100c1420b021080c2e520340300001101181d407141410003e6990790350380c01010420340682301100da0030749900c44800041c074081c00300030001d0f00b8916000c1e0208078880c191041a602480c06090100c0c941c00d020102e940b00150003034021065030001319110740c2144040030401d140b5001c0341c06001d0303032a800030909003520000802c04100d041c5141d8032540c10401a061848550001c44200020f0000e83340c220307481000320b071821910702d00800018003040d41a510410b9540d0100409041c11003640b18003078807525240205214042002c00c100f180b05800051048000c1c0b546400107061003640980011821202211940706e8548501d400c49164415a40a0f502155060b800e02922074019a282d412001070302d1400300700c13500f4400a01809004807122040000802c0000e80b003613041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 534566124 1250 534564874 534564889
    0xd0903020c150a030f020301030f02010311040f0f21020108010501030b060904061503060503160e13050a0b04060c02190b090a1e0203010b0607020603043512070c02060a0f09090515 79
    0x70240013170740306100400108050381c81c041c91140d424a40021a11141c2c1038007041c0c0c1c011900b080340c203210849000310b615408803c0e0641030340d403155920805075007040e402c0e03995490b031503070000e0000715100c2c010003840d402501b00c800c00c80d0008000c2810004100e02103011108203902c400030b41840a802c3d004030039050b1288001800c0d00342d000c2c284581030250700c5600e0b104a480390103145034500c0700280c1c580c001000928104c0f03038480d09488810a140c145132a403403d00742c600341c0b0504d28001150007401e000096800c01d002c152040c0c9107210415031105600110010051052802500c20b4000014210300220b401c00605002c00354030010980181400c5401041805e8001c1c40100040300159079240140c9900c6a84092840800407407142400c030081395001d600030360a41955641c0510040000180086010030382d120201651404012200b00703c403984d019402c881d0803c840b004c55441480c2d82c10740c074007180c00c0595486564001400484e1802c5815103c1c0380e80e4400021b40b81d142511 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 534567374 1250 534566124 534566141
    0x207080d0203030105040e073606030f0b1f03030e1302120910140105040902030705060d02070201080c030609060108130b0421030b0a0b070f0c14240d0903020c150a03 73
    0x3c0c018038601d41000c00320300310390076142120344184030f510047c120274005818401031040751744c5e0303424080150380e45003107400c1d2104050106e500812000000c0d001805140c0420300c1a501c54410103545451a08d05551410310b4106064220000f590700c401e203c00180000d0511450b10100a885460b018a603581481110129407820341e04094400d00d9062141c4410f0781074030300031100015014014400a0700d0000b965100d90380225002c203580e09074030340f158040c0030304074000e8840003020307070324401000c0d102d12007182d4850b482980040810880c0d4445c00110b54844240d0300340d00c0c0b801507261640560301d08121022036005940c0c2d400c0040c0f64007450b0005410102900f000c0c41840110070000d05c0c0310b0070500030485500310206800003481203403042034a0340c1d500304209003100741d140c0d101d4031404860751034070301d000d00c1e2180700095009050112113010465000c100b1402c1046c140b81c00c102500811400381c0451007903440d480306550318948010004014400c0003070350f4000c1d0020103030030b031032404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 534568624 1250 534567374 534567401
    0x16080a0512070f1e0b0906090d09050303030a02031b27060a0f0806133b060f060d0206030f0406050709030206090d1403030412090905040305190207080d020303010504 73
    0x244000400608212440c07800c00d64014082c210484103070f5900213080b003200501501d45001d00040c00311040b4081140c45c0039205042c2601d040202044095800414520440350913a00420004074400100da0165411100f22102603100d6030501ca89060242c100c01e90009100c00000403240d225000380c9051846910305070b40781800c2096000740542800380c4009414240301c180c1000036141e503981801ca650100c0880001c01c00c1c0607440904505501c40125070400c1b40ba13134401c1c0703010101c03c0041c20750900500d4070000c2c503c7d591044991034039017001800d959040380142e4030303041c0169180c1020b180b15110300801c0140d01d142505080c410754001600403024800a5482840940c0301c0b00c3c201c9010300e109803001003c10220749040c0d65106120315003880640004820f020402500b414011107000860361105c01554944200380215202500c0040124500300202c111b09110040103c1c0000c5003401550b4846a466000c90306000d0710007109030068000100510a0340750502c80d03840c000300c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 534569874 1250 534568624 534568627
    0x20a210c02060f13061d071d0108060c04092c0109211202071a01060807170c220b0f040e01090612030c0f0f030306061b030f050c16080a0512 62
    0x84503060f2200c266a81c0c014200c541c84110244020a486d144d9548400786c940840c3c507070644e0758080c0e035020185040c560089107081d4000040041c00088d146008200c1d10012518003403910b40d42d0001800c204500c0c0c04440e40c884464013440c10203441e2000070416060001c905580c081c50617003801400c140d8205004035070315804a0084c2d5200600045c0c0b440803000041e5100c13031a040550050780c50302004240c0800300710020810560200090f03005000d00e880d1901c00b09c84800c0e00313260380541160a0341c20701a0031b000e40c01d0790f400c003050b500755000480d01402032610303154a03d130803056020507203048041000090030407108003c03840d0640100a03000042001d28100410040c0e8034005030310203410010680203101c10f00001102c04107407070354020307030440003080c0c14a0b000e0040d0840c0d11803c000714402e659002c224482e9020440021645a620144144817000050b43e0039008a54603109910480e40051040d0211400001c040e000c41001465290302d03030b240c82c1e89414141c241d1105c1c034000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 534571124 1250 534569874 534569881
    0x10906090b070c05031e120415141b0705010f020f06270102040e0a1a09040605070e0303070614100e0c090409020324011e09020a210c02060f 62
    0x28446032200603500803144507541da00d6a8106100307002100c2d009550315010b1104620401d25040a18210700001c4c0b506071410b141e84a10042910b004030b03c54040c0003012180000d041170301c2606050358105000e0340107030820390b4841000512428182e242c00c1140d001d4901400a0340c0c00060f01e410020300351005100d181011a011a11000d014052000c10311300000d40d200400c4680381d501a15240c244021925140d0769580100791950039991038103003d1070000a1206000c08000c6140300c1031010f03113849515140d81d0b840e01c0060000410400420505d001d50108070343d001c2c401400114064070011921002284a80c0078400014000c045c14901d8032a040003016110100780382d002046c04d410584036440da81c0458090709501030300a5250107804000012a80902c4001c0c41c502c001c00c0b201c1070300d44c0e04c805408194030030000d4021403110b4459410010707500c40f0f400802c0032483c9442e102c1d208841d2104c0e03089440c0401289280e20035154a00d00e8840707641007211540c80440007031488900d08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 534572374 1250 534571124 534571127
    0x40605040201203307030507030506060702181906060507121b060f090210051305100c02040203090a0507081e0c010509090916080114010b0307091e030803010609080c010906 76
    0x10005842d40c070f0303403940341c5500c04000140140e6001e0324004280102d881032401c1713000180288001c88034400482d1400f8086035042c00c00105a5084550291560000e111129191255450002c103841c2e4012018000c44903005a45e004400c0202880c0e1103a036180e01c2e8921b050964456220001420801c00303070509100205015159a03078503400110006440c40030340c02c01d00180c11080c20180d0001204403406680310344c000300400130b02803084e0750070400984071000c00288200d450702400004002c1c140e503102614140c2d008680103101403044400008031961000d00340103580e40300050540001500300c5000885802d921b100c2603c07500070b03040ea0b0242c88d001030f0490040000150080145c140020000c0e4020800701246881d40754140c94026551085a8003030704c5440d10240a03042010000190305c1c9203c410740b401b90043c2d40b80c04840600381386201880e00d50314200e1003a079890140c80003000c42e00710350045002e032084d95507064440d4100101c46150080e445140703810401c200c0d10800015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 534573624 1250 534572374 534572383
    0x1d06090601020a151b1d1002070b180d081c061505070303020904050c090a080601051f0219060203040201090b13061202041703070605010e010f05060f1204060504020120 74
    0x102ea0202001280301920b5101600515803174410780113080402015038a21341d04946885420a507043c45040f00c8010320042c051200c5070091900090fa1015006009490904000d428907078680b01d049848000c0380400541c5004c61001c069400311000203440407070708591011100c0116011105114240c40c02c140c0c01852808078618904200010844108151003501103d501c0c40004100740000e0034210340708040d9030700030449184107880c200b2002032070040105a80c1c1c1299002030400208034100300c4011a6907a00790708103011402280c0000300c416038079038440780036180107100040e201e180510016100c0d8504d50045465160240060813004007000e0141c800e440e48d6260407a41401c03401c001c40003a02842c2c20102e00090024514898000e00002820b04240194402d0001d40d030b858560001200c000c0c001c0d0100b8541c1601c06104070704140c401800080741801c030440c03400d0484910001c0c00c0d03c1c191011100701e80c070365041c00199a0311000c1c52012040040e085101d00648030345840da00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 534574874 1250 534573624 534573643
    0xc1507110a06050402010e152a0a110a06030b150f070209071223190b03030c01021201052d0628030e03190809070314061819060b0d020303041d0609060102 68
    0x111a5115250500440315000380d40f07400272040c120f070a41030403440c002c45803c1c1c10442060007114504070000d4424441d0240c5d00001a000e80030200300240c07031949241c1d0380d1104412602c0510200116401612490321f840d1040700f07142d8916020800c0e2030303401800d840400c1003c40c6881e10394641c00700703c803101002e010340060102400500c0b00b40e603c1c0b8154060b00c5078140041e41800042800c0c00c201006400400d40300b103119102c036a0a030307291410490352654240c4030a050f03181070b82100718451540400e10081080041c03426007421480155007161042505100c0e00b200c0c07020a940c601140c050041c000110003000140d410080061601081820011166810015544003140f2964410312181c005140c0011341c501ca46c010501c900d40c0e03100e40c00d42c0c000682044403424182603002c089403000e20b00c4110a806510f4841603100d806c040c04200c40260781c000000720003580141c2d803c00061000713296003032401c900b51f00c10828803005000001e0440b400303004e0070000c2190581c0e002c18607400c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 534576124 1250 534574874 534574897
    0x5010309050a060f0b040f050c070308040618060b0103230c0d0906230f1b0a0e0a060e040f0207050703080f131d0108030c1507110a06050402010e15 65
    0x103080d512400c2140c901182d00c0c40290001e80781000040403c07409401c42c16940109940512103406014503005c1242d00031030740752119081c240b0400001074800ca85079a000342c00340750007140d101181c40b10161800e02c00c0c6021614150380300206140e65800d8058001c01c0001454131903242ca8160348607a0445100a204040e8030f8400200c0042d80c5419600001c1d14030f40240d8100f141c600504984007280860040404011000200040240541d1900030b0310039086090301851900380c01da0030340b40940211044000307004440c440504651151855200249070b15030359405070788802c3c000d01044560280d0b078a0000b07401002320b4000710b100080d042c4100c0390300c02c040c550b981a983e010812a802529208a501c0b49800c200142e41d2f002099114400c10b10400a500180d90750742d0ce19943e0b100b407040328550b03a085030718030080340e4600d0143d0316800030241c144080b0039188000f17542c1c01c00c088400111201591407007170200355644250000c2140006841c2c200000c81c680340c1d50102030040c1441c10300e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 534577374 1250 534576124 534576131
    0xc0803090f01030c021f061d131101090b1306120c021905030f04030b0103020a050108160c150e060114030304080703201c1709010903020d0f081303050c0102060c0301050103 76
    0x1820940f007040b01c00401c0c86c040c00141c00c1101d90a800f04050400c512442e0f5000806c54450141c141d0344800312801100522100600280c0950b5030705440011031a855040c84402180007840502c05d0008022030180020f81004850034050302915005401c6082d0301110314050307660390515000104010090901080440541f6881c41c00364603500c2a0380b0080708484010400104109100168a060702d2007241d180c0502a202e000445003a403088612240381e01c0001003c000b02c03801000340f140c1c0035001d1900ea1501c00c0510b48260300361580c09044d940c01f5448030004104468507a01c01c4948a44102d0246150a29101529541d000c1c140000380c001c02c9045003042440c550700b0b401e803020403800351003900c400b92070b80a034805810b031118042c0d42c243c030702d00400402482c0c26021610f50100503114444550700b140c007400240d0300a80f008403110b002000844000c01c2920b4082c141d040914401c0c411164150b103052420480f00120343d0341558004420f2015082e10101580c1c1500c1c400e2a000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 534578624 1250 534577374 534577391
    0x20c0616060b0301090318080109080906090a1a07051902010f081f060f0305062b1e0b1801090312020c1507050a0912080d0b0d1704030c0803090f0103 66
    0x103000422070300c4050b07645580b0700a4804205a0000b60208900c414a016821119500d07101d081c00c2c0c0304641001051003070100300162042c034000f0702401c2c10b458007400e040c1210ba1210ba6040380c0a80e0742042040440002c00e20b5000c1007000c000349045040c00214109e04003070168000380005070403502120a102040001403001c0740c6482c075240424199032000c40d41195038020146c0290309610b2103c00281c20300300098201e0030b154000084c0b488280001800c2580c5a0204903003500820000300d8104080c43c82c0100c3d4100c000300c6460300305025001c14480da085c04001c4040801001c0840b00b03480e4100281c40010907001942e80c1d074031954000f00969500340b5548040e041146841100714004003000900c880c00da400700141088002c6615000c5010780c41d0b8050300b00104010400400100e0304000100080d4650307088540b40d05070140405100b07012a94501d541441049803250060001240c200103000341c0c0b00301c0e42c0003881c00c10f014500d018100004900c0440d00c00311868140340d140c0700c10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 534579874 1250 534578624 534578633
    0x30f0304062f042d0b0c0a06050405060702010b01140702090415020c010f0b040618150f0e0f10060f08060307180603020a090b060703210515030607020c0616 69
    0x241c9084100da00110100c030a51000400b51580081c0504000d9101d900003980c0c1c101c0e0140a8070f1a078148529004c66558500341072991268000701d41000280503040c0100c00090240c01001d016510900107031030340c0d2509160081c01c4502011009040144001141807585d404600303d81d0990b4040da0a4070131a6a103043c050401c543c100b2900c4082440003d9002c0045819840782140801c640701c140322594586040109880c028061298207045107008603e52481503480078200684a46584840f00d65560b600102e1040c1d55000d4400545048200040990500b61480c0d200d800d4003101e0390b460b030602d030340140721050069015040c003c40d0404100c103540c2c10040d09000b03107044962210311481d05500d04001d48640d11040340241c01e402800720340001c1c14020301d0707120040900700c0c900b00450344d00c003140c0c41d5025900000003500700c8032080228011501401d80301c1d055000c1d600980c000b6034801d0628002004100404540245510400030b42d501b00031100d504481403140080704046052 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 534581124 1250 534579874 534579911
    0x4151d0301050c2d03070513050307051011010b060403030c06060504180f03021509010902030f1b060d06050a0306050f0a0504112106010e0f0108030c070501050a02010e070306060f0503030f030406 86
    0x44c40d070320303040d000c41002007141c0c1c0300c0002c0425540724146a1007040c0c1e1501030503640e0000707002e1b290f8004075202001e040244200031920803001004008140d065070385002c24003503401030308250001200b404004060180d140501c000034181a20700304110500303140131710341001314200d0080c10704281030128428980300b00404071554180780e0f1104003906010702d800b402426100070881c0a801741d448503c03c2c2c160040ad14021345205480511403800100c010400340e54429080001c42a0343c0390000314142c0c448d480180c0c003651082400107030038101090700000340440180980b080d9420401004005580035018a05200060712003241174907a0780ca4008162440c0b102400c100d11500c1d00020311306004800b00c6003d03940240f6651000c0c0d03211a4400d4403403240d94441030442d4003400f4100300d55449500140782c6102e1303902c00045d4184114035070b94109100d0b030b4400d880058030780005010481c0d5a100c1200103000440c0294505000000407a10034000104041e100540d00d0401d042c40712020b12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 534582374 1250 534581124 534581197
    0x1b030e06010b090a050d2609100314070c020d060c0203030f16090b1602060d2403030912060f0c0c02040b031b0904110604090f15030203190804151d0301050c 69
    0x2150319804040090301d40f8a0b5400c5030141c1c0344030380c49c021081020a4080d210301c128040a0300c01c048000d82e5240001c0d24401440c0000304d03000702c8004400b43c0810024802e0421a482d950302031952800d20b249150001c04000d08002c0b21402e5000c01041142c1c0c04c1410503085401500029440344024400c0040e21500404065046800000c80c41d811070840c2d40003c10300c7d041d00b002c22105c158440141400d11155000040c08601540404c2c801d0204440744044030034407911012031206060000c00007a80c0303d00d85410089618201c01d401140781c280541117048200350010520701c50201000050100c0303509182d40a120a400490705020078002c4054810764040c050750b917201d540d10000e60007000201d490400ca54913100c83c01c440c0340b04003070055003220b0300100103108070f004240d041e00c100160800c04a45000007000001040e041911503401c03491402c2e01c1ea007480c4c00013052170294480b0500c094611a0349442d040060580046040d034070000b6034074049010891020300c01010524062 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 534583624 1250 534582374 534582413
    0x105030a260408060406150e0f040206070c03060507121e05040212151b040b07060222080a0201080108030f19020f0118110301111c1b030e06010b090a050d 68
    0x100402c24000004804c1d0080d8400d01007005400b400c074607c1c5021040328003030b4200740720034080801c40040356141c0c0700e41c000b0300040201c0d2404580d0b0380d840007518119801155100d0321035040208582c0c00003c114042e5a5001c028000305603681020702c03c000c103510722400c015a44401207020741d125458503041455990080b24a0005060b008054606044031130703180d6a90180d19180d4500580c0701a0340448407003070300690500035290741e00c40c041e41040c00da0003004520207003c10b00090903441c1c0c003401455000040c003201c4030702d80001094524140c01401090384200010048104d2110846402d615960150580740180c88401c13400c00100070f078403c29542c249030360342941100049017560304a01c80c481d61030381004244285401c3e1441510900c46444091141e4641c03501c0c0c1c001c0314000801d551400144000118282d60803401200711140c000903a0b514209003400c404000c2c0310301510404a1650406a00000180f00000d070703401007600483c0c8a1005400f082000c09040060354145c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 534584874 1250 534583624 534583627
    0x318060507030203011e27140a06080c04020c0c0f1801091e05131506030203031207020c2b03030209040c0c03120204050a141c030206070806090105030a26 68
    0x220070700802a400a0091501c85e50040c80c00d030842018840d061811100d060135225030b82c20203644201c50040341090141c0001e9200e002004080c8108860107110310540c0b04001000f60030301c542d80e86440c0b0601c01c0607000d03d02c100244203a401000464034034052088440750540d9502d2808984043c42452103594540b0300b090001c11020320f2a04581045840c944820400c0d0300000c02480c26103e082d11840c2c0e50030741110200f00030400c0d2446602283c1c1c2e005d480460304030765039400b0919660003096034044040c01c10301441903c03603050115802c1c440e4100c40c440343c42c4100000d100d4010800c58031180783e401841004034101030298040e40c200c03003402802000031584504000e0240e801c0804110000380b52034603c1c4910310003a2090750144e840142207400100d0a10f8403144605001460300d960201820148910807280c0d81c4a00c0500762082d03000e8002d505164201421803100134000c1880703070b090f82c80140140d40340010781102c1c181e040840c070701c09414000c00448140c440e00c3d0100c41403020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 534586124 1250 534584874 534584881
    0x90c0c070e090c0402040e07080403051608040f09090c0e04020a12050a020a1e180b0316150207050114181207031a01151101140115030f050906060103180605 69
    0x6141c0c0814841c80e1108103550f00c0440e10800c1000301c1c8181c0c000d424986103000c0119850078481e0740c200d54020f02c2030400d24582180715170116100e5000103400c40302100000780600440c2d00550000740102410740c03080c003e80899a50702c0d52298020301900700c0740d080250000e03041d0360715280020000c0040003c2c0c1c0c0b4034400c59042481d00c903816420140c0c0903034103582000821288500c0d51048850400360040000e5050900030248542d02c04030032000981c43e00707400c485941d03060090408400902c400712900f1850018400200c0c00c50322005802d5400244042199076081082102c200c03408051483c1e40711884c06210641c115065411038000702c0007400300903480000030b10358003501d001c1c91007505009030b0b1000c04004803509010700151202007208030000f090103410940c4003a42c0c12000414901340d0f020642e243c2031400d070f0120f10ba0302d00842201139405d8051080303c1c0c2d1280c080741d0512880c9824108036607151f00180109040503680c04120410704502e12421544030b50000f001c0c0001d05 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 534587374 1250 534586124 534586139
    0xa15061e0e0f06090103023108010203040206180d05070e070201150b0702100207120305040510170606250c03031b030906050f0409090b0f060a0f05090c0c07 69
    0x16414410038000e0850400c41000e1140a01050001d0420082045030350400c002d040c020035420070200641499002c1c003c0c51941c4400da0340da00d40f030358500c01c0e5604640c4100d4407011420110b43d80a11079a034410810b200140c0c4031982261006100c01682e4840060310340c1c08207407884240d032005840303401000c2000c240c00d000c03040051301580e8240e009200309255082c0c031800030413152203402d40080080010f8030060034000002e5440b1307403031401035072001a6541581001016032400071000154009000d01c030a207440107040300c50b4500f525000d6030341040114042c0040d900507090921944000c5180524052800240102d14408900304103150590707291895a5400c40d000483c08a4271120b00001c045c15015200e040c8031b5010f1351004070003481c040003031ba069848451001d110b644208004a9000d146020740d0303070078a1107a413008045140146e80f0204803200909aa40300300e166403810040703c1c5007840c0307032029a1400c8464920585540400300c2030b5101c0c01c02c5085460146000c00600341c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 534588624 1250 534587374 534587387
    0x70c0f02030610030b10050a0302130204030b19050c030702061503010f0f0e0d080603060403080702150106050a0e06031003060e01090b131104021303110a1a0417010905150a1506 78
    0x591040e8601c0b1701c2512403200089505581e400307180d8018070a90f000700007519001c142c081e0342c48514200103103015180e4a850031580c0703080f20752003180c003000005100c4c0d120003403250951005039580351b40c0c15410400320003902c0d582c01520000d060041c40001141640d02907125400034040c40b04104000e103c0ca002e484040d0040c1448603050303005210043c02c0c50b6018090041c401e41004016201d2555190ba040d50300c408043c020740118452030035100060a50000c1c0305019100503200d240e03c5d151600401070141d20300c0c0204602515048c0f050008a00040c0818000c0d80d510240120720104006117041c014414540c001d802c1c4d2210700180042071800c8090310b080c0601030700c2004200000d030001e1205920402d4030301c0c0040faa200c3d5042000c0365583c0454004100700400f60007806940702c1601c102c07005102e012110a440001d010040210700041079580a8a940000d101d45450b5458081c0c484541c10140d0400080b0480010704000b400d80c400b141a00008003c5041c850300d0f0403000300365 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 534589874 1250 534588624 534588629
    0x114090f07050a060c021e0907050909060d0305032e0303091502030301050a0509072001021317060a0c09080f0303060f0108060906063009070b12070c0f02030610 71
    0x902641501240b2810603024280c191900368032401400c2c0a2030342808041c07414000c2e80e0821410712407090b0f0740d690300d400c280742c05000d02e80e0751281c540c0007800c2044080900a010144601806c0b25004006a00103050300c0e4004400a000c0420b2001c01005c03c074a140b4a40d501d00b03000305803180110815810001240668203210340365400810744080030390f5a48400e015050340240006030800c6a0301c0d1030081281d2060a904c2c0c60b06a03015000105030040c107070b40c000326445035000300b44613119400e680c42d110020306035110000b075034840c090002e9489106c00307040704800395110700c40c8000141c01802c510008000800480b042c44030111410381d1250001e6540e83d01c0364641141204842d0710808545000d82002020ba0205407165010410194000e04498010381c01c200550708119000543e90812007030140215540c61600100540c18a851500420703000c01041c80041c211b002210003d660007049410032074a003207218141310000c00c61a940c0258148520010015110a21a1f01004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 534591124 1250 534589874 534589903
    0x5030a08070c06021207060207110301050a052202221e0c021c050a0c020112090501020c0d0318060b0f0406080c03060a0b1305151f0e0102010603120f02011409 70
    0x2006515a0783c220f03101c030860000b40124200610050000c03440a43c018002c3c0c82c41251101003900454000c282034580032140310040d9507540c03041042400303803141d0001c04422000540f41821281d070380042d441e400010340f20b401126103034982c802c9004440d032100320300d95030545101c4810201c128154004d0f1107529040360041c0910106100016a07141c070a90050500e9100e060504102c1c103c12110300201c0c5809904106151003145a4030045100d960141070184001599540d03075480001e18116014a01034109441c0030781c4564810220760907500169030000020079548100f10000710b0b04028844400e034840d251440c000b403400c50014002882d60303800c1c0e0640d00176030754003030000040781c01490840e50005100d441203415a40b441d8030041d4000003800d11a10b4400100002c02d89450790103240300300e10041d000102d141e442c1c0041d40e81810ba10244000e004641c00d40d6629070341031502e0f000c52414080034102d043c101174000e4001c0410a081020f0081040c40c0900f9010355400f0f05d4214000e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 534592374 1250 534591124 534591143
    0x10051215091603140d02010c0503071107050604151701030b1305030c1515030c0901150201060308070f020102070e060303040504180b28020f040b03130f060b0a080d090509060a05030a0807 82
    0x5c20240103000b0152809000d4556a0555540d60019900a00c6a522440c05030168500220303107942d500029002602009802e943c0b41c07440c42c0c002030b00d004111041044130120020040002404c0c034000c003503000340048403454803489540b82c003500d5400740e8000d504c4980145074101c815039010407081441200e43c40c4884010103c80008d241d22001050750003a008001e580043c04603d0300c009011881229034800010071550300e4490b00400d800c540c10480340130741040d007030409569040201101504115403151050309081e00000d80da84198480c003801292221408800c50030002e5103148151f070480391310615454030282c402074a60301d50904028010712000c02e20312004044c130988280c117240d40002072806003881080b1246400080c81d801030480d070100c018001804480c4a1098a0320902e0003060b2482e01c14100070b2001150340240200743c3c00a1a800a010740c0000102c046540640703c070b1380c082d2903850104103c02129000f098140c4506200350b820085d58000810641d40603130000d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 534593624 1250 534592374 534592393
    0x32703051e0a022d07030605010e160516030917010506041802090a150807090e0105070f0206130c0504060602060604050703021303150906060803031005121509160314 73
    0x10714024040000d005902c070318422480891001402c078000c5801c04156896103010000c4a0720b044104e4108443d043d032190700401100745074800301600f0031032944210780c1c6043d4038003006266000d80031151072000c3c190285002410701420b61a00138281c0300d800c5110501424590078083d00083c1c50503805245480e131950303500c3d40108883d89140c1d5000703140781855151650300342c0150181c403000078a01c110311400024042030400048000780581040826451800d1000c0340c03c4030f000600480a118040201e0541d240e80803c49aa02111358003007400b14103090b041c0414a03840c143c0266401038a07010010403020f4001a03401d00c07074a0221021f2180e03a88810b401c4041e4040c0c5074030000c095191100a1000422803100300180b04080000002c12076902e458910946d074150784400000e4000105010542e08080c2200000d00000d031102c10360603071407441d03680d070340c600300020050300000b1032000c078207062410f000c0d02d10b2070320f0b2003090040c441d5100e092441c0c681c1e1110007400074510404072107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 534594874 1250 534593624 534593677
    0xa0312080906071209020f10110c010206041a0a0e100603060612050606060d110301170c0a03031407060e0a110a09111e090d140d0806030d03270305 65
    0xb0a128000c0340c2d4640724980c0d2013114400140060b28070490380880304984002c829207600514840f40702007a60b91307045005032080941d042012000b0490f0464101004110102d40d90b101084080c00144440d41510b0b0343d10100000102004080d40b001da00403141c001d1840c14990300040242ca0260a04000080c2e0301e5001c013420305900351008029801c4000010082d151a402904101c00d901e40003145140300140c3c04421170b4000d8202401c01c141d446002e2400070300400000b40515400c0d541040000d080d514050041e121000001c0540b51000401d42c04100c020707042000e00b031a41c41e0844800c1200c80c50301e50b142814180c0305500401554400180ea103221307000790014802d01c1d4081c60703c2c01003a542c24610781048140e4114803035a04202c40399064484551102581e030158810b0301c0c004400c600c5007030038030025900300000c0201742001e00caa180d4010420315800d0609013000210002403140305200644c2c1d6082c1260b172240f141c40c0e00024960850010505041d41016050800e2001c045 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 534596124 1250 534594874 534594883
    0x4020117010608091e151e10060905061c0c120f0f0b0a0b0a0e121903110102090a15140c010204081e0a031808070b18040b01020607050304030e0a03120809 68
    0x500782c09034012a841c0d5040303840300743c080e90031500c00b1010b012038006507803c1107d900c02c2a10300400b100200c0004100e560751114000015242c00c48500c1c0c41d00749404011154078040a041c0c0345456940c404c100c422a016100d0320300804815001401083c20894107600141100f020000c296070610301d100b411803a00c20b0051090f94841c0442c0381c1040840c000490700d01204180c4290841420120491042004c021078110401c1340703a150842056030345801003d0b03c0c1c0f440c2c40350f89240c2c0103001c00c8003660b03920301604040e01d20412000b0034003041004100c60030310100d080107681e61000160303611150300640042003950050b500b15a041c0f4480d00200c0c2c060040c40c41103c0b0342e500f0400660000a00c100300e00c20132035941031306229001c0d40b05c490307a506041081e0b02407a91108009145140c0b07005640042d1040c01e81128108502400d1400103929450010020703010040000005002c01d80140c40e0024401070241608601c00d4403850b03c40e42e01c404510080300455a40d50000384007180005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 534597374 1250 534596124 534596173
    0xb0901030312050c1b0105041b050d1410020a1106060904030e100e04020c0c130510030f0c0906270605030c010f020c062805090108040206030402011701060809 70
    0x589045444080b048000300030800070b400075400c4942040320311390f2a910922408007002c140000042c4030306181c0b40c0305d0382a402d40304801c02501c8080008001ca6a20030f2101200386400040a00000d420000301a0400c0011032812003007520105d10104050362200044038502e0210b000c03507040e40c4030f40d000c000305401d084500900040c440590341003241000d00c88003100c0c00d40f6080c02c450099450000134181d0300001d080c50101e600c00c1000145626010044107030b506103200d810400f030700700b0302c2c2c040e40e100b50280000b030b220090440a010030045407803101c02c02420200b0041150701d4440103403880329a20300d40e88000ca04a85d022140c00c1001d24860101101c0005008212400c0e47e0380040d10080200344012081d80103400412040fa1103000040c4590101150080c01051b0f00e01c040c1c3c03c005051150103c2000300c144240f020f280d80103c02c03107400c15012506503490303680b6880126100e10300d4a614076a03c05410000103131464101c44a240504110016180c01e804501d40504807400510b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 534598624 1250 534597374 534597377
    0x6160602090d0c230a151806030e120708090603040c030c0909020405090c01020d08091f020703090b04030c0b300402120d1704080c0a08040302100503040f0204050c2104060b09010303 80
    0x1845d0800400040b02d4404c5125491402c0603007440220100ea0903a0260a50000c4042034440d01c03081e200a2051003003210705003e000001c0d00b0301100e5221740009000e440e20744c6004d040e0020214040c030a10f003540d1030084d07522028080342c003500c80e501e04018042203402240154286000320701928404203840c1842c0304182d0081c8070054001004507110340020780b511003180280d01c0083c20030080082d640800380e14290300542c1e1102585001055908558001040c114080c44140001400e0078507810803110712403c032640310030242e240da801180300b9161140c0c8011322845a0200010b001d050244268000c40c1c0381d020695403511103640303a501102407100062a00740c1c207005100d42200800b44c00a010310a030364100362101405601e000c005075070943d000701c80420100b007140740c80c00900041010520b481400c0d410316940398541e8482c400c0c4000d20032521200000e0b0004c201c58151200c1c2c0362008072003a49980c0741a01500801010707281a00c94500b0181c0d024120306040c443c5a0489034503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 534599874 1250 534598624 534598639
    0x1021002041d06040f0207050703020a0e0c0a051c0614011e0210020706020903010e07150e010903020d03020a021306080c040204030819170a020a0e030106030206160602090d0c23 78
    0x2056004803030400030012680555110341000301545541b01400003030b48200001c0c0b11207415401040340386099940000d440120520802101d0030b41c44082c0c80b9004440d00b0920b4860000c1c0e201488011200780010004500d0010000f41a40380d845c002c2c102c8080c280c0b15041d12925616000307000800f54902480580c1c0b00d1412401d02d0703031842d8000c0003800d020b0500141030140d40e100107800d641c140c1440000c1039210020074400f03100e1145084021110700e09141c030322000124000380448070544000385c030440765245444203140c000c2c0119285a80d00404c86a812092a910f041c0102090700030141d05106400c4da4040c2c6041c24801c13142aa03801c02d6505003020b900c900c401c1181c001401400b03040141600c4222009440b981c0c59a000b8802260050380700c0d02d0b800002816803801d402d1242c801da05202080001d42c648034101c030014510019802c0008080e400c124019201c0c420ad62608000402c07000000e1021881000c0151203410000034480b20061000000005110480940c0b0030704 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 534601124 1250 534599874 534599909
    0x203190518120309010e060c0f010516090e0408070620040911070b0105090c0706050103030239091e091015030c05040915090302010e060907030c03080904180f020102100204 76
    0x3616003101c21b0075005100c14500800d0079911414880f950916049580d15071040c801e0400c11a02c0c0004441494030f02082458a0620340e40741400c030142c13003d07022090000384d110500260ba004615a208103407084201d4818444c841160f55016104081c950740c6131420843d80c0740f81d4a07041b500f441d03400413003028450b42030070304201080d90050021450075404000000015805004181c0218025000352145541402201d8035030343d12050001c120300700a2184802d01504041001c1d40000240d035480300654540d40c0040703010104070240e4950420603010044400340006080400807480740090081d481c0b028110100102c01c1c0c00001e0220461080074042c5081c9507220030041400b42c01c4a40c2c11003014a0301c1030445403840800e0300180d46038601c000c00242d00700000b903000042c0754020403c035413035a112501c08417100d001c0100601000189a859655140c008401002000d02020154065440e10705401c18030b00c45c04a01601075204018601940f038803d6400301d61030340141214461 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 534602374 1250 534601124 534601127
    0x10b0c030405091005030a05210c030a0315051206040203010c1b11040f022701050c0a060f0e070807150f0e330406091a04030b07020319051812030901 66
    0x144000c0c80c0d840c80001c80040081c041c6d82c20000510024020805420803076260300030300f0074200003800d682040c40010400180e40640000890b50711341418500001c0d00c4624441c0c21803021000d52002d640000c1440b43c000b585040450520300551080b8020440804840415074161442d44c0440302c640d0558024100071800100d048110210020000580b04415640500803a002000c0c440b212013409482c4408882146000020807502401c1c0181081c00680d00560358100c0008020300300303601d0304007030b4a0290b040e41010800944c040e0a464001d07440f2006203503189560b10400b441326010a0011111600625100261080c0c5580314a0b02c0e5800c9001d002da2818035500f1764001030301c111001290345a48020b04500f814540301101c0ea07461a00c10014881000d5400640c00a036205c2c0700c0d0091004840121421a5031002c00c80307030241d41c1c01c201681180110b800c0f640c69500c904401d40d1407541d0040043c0f052034005c01c040d00c00d13014075906105c20100170360000c44407513104020080983d13 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 534603624 1250 534602374 534602389
    0xf0b01021e010e030a0509030c03063105030a030c09060c02010f03020705030915091005120f1e0a06030c0e0601080a0e01020c070f0603060b2d0f1201030b010b0c030405 74
    0x1c001200000c40c0c5407815090a0780b6541c030420f4144e000034408904142c4504e024480c040303180400301d00411443c2032442080304c41e1070140c851000d03095114034659141d024000c0c00c00a1158200042d01e4440480c0e03000a40508a80380c4e25000050203210041420f82c000c8041100b00c0c4e8043c0d6031700340d5107024010254001e510042040d03803544001e1099000a43c1c8070f08030250440040b861950316512642d06220a8181c3e81c5a40c400384a018060800c40c0b41c0c4402d05280d1000c00301d006c1441c075403608040a0652981030f4180c8003181c50a1040110350a040d4001e8011a4403c0047d04408e90365040143c412030720551380b16000503001c2012901c0e105180d0010420352220700001032030aa00659034524240a640c02081c1181c4c0c078503410001d0640520541008000c2e00e6003051511160703038071500740c1c0c9000903080310820520485005070601418240c4d40e01c4103000060750741e11592424031480032602440304451042c10b81c80041222082c000c26502c41101c07040045081a04110410048 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 534604874 1250 534603624 534603673
    0x319030807033c020f0f09010e03120c0d0c08090f0a050a0e04052e020307090f0b0c0607020d0c020937061d0402010509010915030e010f0b0102 63
    0x7010f4969007040c8040c01d02a204880000499000d28881d0010010701c1d0200d41c00001501d058520511801803050400002ca40d440c3c50385c504d040c1e90f1601444010703500d260203503d50756010f00c902c942010400030b100004010741c50003401100c8030410102d13001c035011a20710340001c180074001d00c0b454500d820946240c070030011004260300f18483d21400800c3c141e4881d5440358045440d50018081848801c1c4410450f40c0303e4540c142808107902c50a94400109000340351a402c1c0d400000190003034420704805000d00303041d000020034503030341b42420030194106814807036171401520f01041019000041d84014031000762a081c505040340c2d02000b0301c2071401859000d0010000900c04060781035540306580892031600052288080c000180c012100641c03c04220800e4000182001c0080c807459154026070910b09235654074441c000403600c3e5042c66012400c43c00c114a042d00d403154168000981081800000b041440d81c011012002d4500d085003841c0584c100220640b50341010a10003480d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 534606124 1250 534604874 534604877
    0x3c030a0f03180524060f0a031b05060403060204030302060a0b090c0f070803102306030406050703090203011505040c0302090d0305030405030f04060315050306040b010b09030c060d0f0b0319030807 86
    0x141e11030780ba854180341130444032030340014241e200d0141165a207407440340c0048003901c0c02003560381b814003c5000b0b03042500018000315229991031440783c42c4031034810081c00000d820203854a960b881c01d00c0207504030740001c030b025005160014035030301424403030a52035400c000e02c4401c0035260040c94503660385c0710150319841002c1c00c109280104102c1c200550041d140300b40500900c43c909520b090790400001d5008045007400641e02c20103940e0344090340c0d042074100000242c5a1a1800150014014044d009415508140c80050304040b65425802150800d5030300b0f01034040300c08c074120120300c202100154810001d0401b000480d10550140d548940704a0441c0d00d801c1d95031554482c00c1d007182e444800000e4550603143c19803400d55a0a500031b0800b907009110030b06099030b0341c1001e41014080c10006100c0031034503050355581001102100000a01007a5650b10640b550780054081a0070704201075040045414260600240418020070310700012110901c0d145c0d000c94860002814200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 534607374 1250 534606124 534606161
    0x5060906121002040e090708150402010e122409070815221101020c0f0112110d021305040c0203160602030703140a2a140c3c030a0f03 59
    0x3000031010f1005201900c640c1d038072030186107045580c00d458403002c2c0d004903c40b07421012108003c03031806122035800c40d174242804002c0804040100d07100d0104005001c00c40c3c414504081070181988010805030808030582c82816505d0118103030762140e040c40340312116480f12040310002c0b291072002030b4003c0b034070f145200c0101c08007041021441120b01c10590380c8550002240340c241da0104540000c1c20801c0e501d005103020650006000f002c0f09140b1440e0050f101e00c00340c40b84480000c1110702c12101c540c021901d40c0c0b80000b45100c481494022640100c5c54515000d036220300000c00c6c0e507200b001c00c120040c030741d8266580e490083d4202400071010706442e09181040c550203a81e196200c0d01d0710308000151014030b01c0f04044599a04284404421341144200310802e1b4840c403001d0782da4081c014516a100719500d841450b04d885170418103007106600484200c0c0181180d071001107103038607660803600040c1d007078040354681c85038103035600100c0c5001300e0047d0224025084007908110b12001d21 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 534608624 1250 534607374 534607393
    0x706051b0a05160504060b0702060307031d07060305060d0b011e090603062c03030c25030201090311011e0c020a0f05071d150105030c0706060b03010e0a0506090612 72
    0x51800381c00310780484a42c3c000140303aaa40400a906802c01890111002d00c0510316094203040280b04440d4080d000b601d0010010b10003078040d8205088402c012500c0c1001342d40909603081e11225a80210f10019091601047d5a8a051005407400507040700401c54540d2034004185401c0160445640702c1084e8101c000a0000c1c2030311900c4011401604c0208a050704100315880d0004ca091502d0144000000f1800d6545400030540e03034480c6005a41d59650340c444640794101014000c00072071010b02c100420403c25a06401140c40140700e038481404480414034441d007aa03110b0030200001e06860030400a03440480d8002100d0400e860041c0d415005441c1c9079001f0181e40b0319003c1e2072560090800f00b00c1000740081d0407049407004078140c1424100117000324031121025000384d041007804808200012003a1003118141c541c402010441645d80c0e0403642190b4000740f1900a19a080750b00103075010715240501c9100340c5000300719403816543c45041003051626580d0794a5180b2506550 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 534609874 1250 534608624 534608677
    0xc03100b030c0904021e0301060504030b061002100b0310050406020c0c0d080d09020f0603090705010f090f23060a0806091e06010807180f14010e010c0303020903010b09040807030e010908070605 85
    0x7d40c00703408540d03206943d960035410203802041000c3d16082c000c1200c0c0c00300160960780403801c0c400849456901143c408884400a8504180d5000e000380c0c0c0c0d8640020f100402c505980201065000c0300f081c1c0ba03a88032944100701070700c4000e44d40544400410000102101c0c0c041d071149061070304c01401c81000d5503105020030b0300b0390401c441404c810b60000300c0078440c940c1c01030a440c0c9104024600000c0c498200441c201f0b03950707064402c18010490f2210503042103590341190403461a4050f003060346840a1200c01490030300c2c01eaa90502544000c00482d01c0e02e507004000701740301400200d03460280c2d2101001184d01c418000c0803601001076507018005251521014500140f41e24031140381e115007021300b00018814841641ca0501c41480c40c100c0c0180d030420f070900c0c0700c150507007001600c0e0f440a001207800b50030b80440e03403a44801402d08110420031608054201140240e6a0141084401d4019101c224280c02103010660001e00d0403c05548140c00400340d10030190030a035103c4607003d11 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 534611124 1250 534609874 534609877
    0x40203100c111b151303080a053018011b2001151a0c0601030605071101090c051c0524070201020a210e060c03100b030c0904021e 57
    0x11850001440002d52a078448070400052090400b0840c4080d890010300300025194515004003001d0501c000c144041d81916500d4050021604044496680d2280860080155010b8103162460080801c0c0c1c07080c4401d0720042c4689481040382100d511070311100c070050b055144014006c5110741d06e8405140c04446280b151404200b90780d2600360100101c585c00009c1548090002440c9a242460007085034170b071240ba042c03c070340e09003c5066030080151441c0e501e40c420040b0000d860311504000004000042d030185200d56000c2d60b03041c251101d0070f07180a0070b0f589031010103045220b0394403007445076240120701e500b40d0070500e00740d00d4901c61659440d50705100c00b100d1412001d0000c2452020144031306600b450b4484030324070085151660203600588040c06164143c070410703050b10011460600c0c16440600404c408404a400078540100f07e40155482150740f5860380426420014103070400c4800c0d640500040b00c5100c2c10044c043c010312000f1340050a105c002500c0d4448405285030b074510 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 534612374 1250 534611124 534611141
    0x17010207330e1011030402030606150c1f050105062110030f050a020f0307060c0b040309180605040c0c0b0402060c0106031a070306151215230315040201080c0304020310 74
    0x10b024182c0e00326000c0d001000c0b9181c1c1002044410000c10802005907408148a03500080450304084158400403001010380116070201d1003501c6410003965165011020200c540305210f242805960b80b0760061000c40d0007803403929a50300b840c0e8030010b240c0804014050354000b44490420100d542e90303858210700c000d040b803c150f17a80e40148881d0720660170401c004660009050f00108000ca281072402001680c16080c0580b5541541d4046001c251003000104028811049144030802d03c440341000148514404d45120381d180c40d2804c12964003030f914074108223400c400300191640c0c503034003031002a901010400d94155681e00002c00012000c004c08030003a840902410f8a03481c0003500501158940d4000c03070008404100c1d1301030301e258802d41d41c0780c011452100c00310b06044802d4206414010980103404001c2043c0300010400c441202401c1d000842181200c0b82c1c0715200c096080450020398001c1d00041501c13001800c2c500115008507086071018046503102108024000d00700c42e00780 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 534613624 1250 534612374 534612401
    0x1311090d0812010b031603091505010603050f01050405011d09010e0a050d03050c04030215090f101101140108030304141c0c02040b01080c03220213061701020733 71
    0x8181a20004600b0302514054040e0070490b038910b05206404404094030003c282c0201605e60250808000300c1146862003098000c0342403240f56116140034000c0d00040316400103894900000040529180c05034034101d48101081d81c05901c00c3c514008030044004040f680250340b0f1340f0212006804c2081044643e9001d0b0b40a421240c1070000000d003907031005004405590820320083c4051fa4941221100b44013420502595034068800820100c0c803074a508181d10845014844020346d4022401448a450403c000c022401c2e00801c4c008010b03000b80250540342c1e00c10710001e00000d0250040c3c80724801c5d604121001c40840842480046107412070850020321161407000c1141068051210388410900b400007292410800213441c5010041500d180a080004402c20680c110389081020a80282100285144000da1400500380a00c2004410401d001101184a0040c402c4d0b40c011503014401c0d60015288100a000011a410140355650310b07505000c10344c90418030480c00d0000c0728 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 534614874 1250 534613624 534613627
    0x703050906091c0509190b040504140f010302061b030408070609090b010c03210905160602150f0a060e040f020312040b03060d0606211e021311090d08 66
    0x31001401d10101800640155000041d0602100509010b0318502a907510b4100d40b40c1a498000619a48406101414100080c500071802d81d0b070302002003040d542d0549092007220403215140a010904444603d0b00c480410014030051501c0c0d002400b22442031204500b0080d0032060085c210703401355001580b01d80c0000001c101098001d03001a00500d501c440400c0003d41c01c02c00a44007503041c8d00d000301044541d1a07005201d2500c00c5002d401c032003c1301010090b80c4401e1604a507074140001014031a440b40300b01c0001d1180c4000f4046249502507031210b500e60301d885c0e200c40d0600e407010700300c09500303510fa000c003007807040082688074030a6002e02c5c00945a118035005040c01e080012120000345c4000300014041d140880d8102e0750000000e03943d02c62001c0f0343d81042d400078800d6410400128a40c03641888043c0e0403450314264090041d092480b020100f040f095000410481000750014419248034080d0303070f01c44c0c0c0000c050f030703213044201c0703140c000040b001070350032101507100301c800d03040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 534616124 1250 534614874 534614881
    0x3020a150903180b0a11120d0b0f0303040807171504290606160f0c06170606070b0402040902210f150403230426192a0e070305 56
    0x180100c0c0c00146201004840f40c10314142a6105074a10985a40c041448840454210081400c000400c1c46442c070317854885d125412000b41801030400808214850000d072201070b012490080101e5046034003803030082c000c2d11b207440c0c008a09510301508284013400341668a1540201d00e1044a00c035501c207006008100c01c2005505107200d941266a401c0241050200096515610211841242034008140c10541c5515103408101448903004005082d06840007038251740010914562078041c9201c00c0d840e541e004c0500005024413400544003030309200208015040c0303070380709010300c0b400030f8030b084210b07a00c0070200b17000e0450b010500c403055449526120f00700d1500303118070b080301d16010000f24560305194a0003800d40141d400c085c0481264051581d8408580c40100c1d8001c0401c070403900c6103560510350f440088105600c6141c9039000c2d01d440540722075421601400c1c0780f135100b20540303500d00f0a00062620803040c02c00c5406800441c3c0800b04020084040300c2e4482c0f080e5030380100d035515 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 534617374 1250 534616124 534616127
    0xd080601030c1d01050f040f0e010f080610050105180a0e150405040b06100203040e090109060c05070c150c0204050405010e010b0306160f051c05062407080703020a150903 75
    0x5080711110310811005507074074404094050f2240c9224082468150f84030303403038a04c011115102c6e650109107051840e460000708001c600d4003544c1201c030099407828801ea0390b1441c15468000c01c032210a174200d1841014441903000e54040d12040980c07d2425881ea800c60002c205482110307048050514140c400b04005441a1074561800003405d86040c0003504191b130b290b00341e426010340400d210f0500c0300d104000942c401c000b41e4009044d903010b1203100342807440129000305604074054409071b00b44410040b0550080c8101ca01d915070045803211503901d0404040300041c02e4001c2c850401401600032809a40c0324020a03000340d009800004602c03910410441c210351684254901035004501005031200c14001c2d0381100c207145040050000206602c11540c520071070202c1a0700e0b400140380840700e08101c2c1c5c040c1388603543c240c401001d640d4036242c0749004030003000c0581d04a10404c100e01c00004400d10050081507201b40104c8541c001c0640d00c4414103034940d0341700403003a60b54004002c20301d03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 534618624 1250 534617374 534617381
    0x1061d0907170a0b0306040803131e1a0f0438010e010501030912030c0c020a03080c07210809030703020904120807051c0911120d0914030c011b02030d08060103 70
    0x748040c1c810804281c04c1e4000c2901c42c1c00060025000f04008000038180d040b6542e1a5000030385c0c04031147d0034a0010511180c1502c401d07160a507090743c09004e5803c01142c1015450b40290301045000f01c2d26929a502c5881c902da240880350072121040c502d1403807401d414020b2010b4040070102c55011076040a1000503491016407026042504200307400c0049411032030320a0402c0c10900c0c0c0812110719074042540e010404480c02900404418800010f00c03044501401c0c815000006a442e41641c0d10311034070a0f08103003a407d4290782c1e40344280000042c0c211004001108014041d600c54541d0b03074000030500c03d01143d06070fa81100744d11125070b0950740702c80a5581b140c2542001400c0012a001c40c010302d41105404082d2140d0350030100040c0401d640d0030880490005144861000112000c1a00d8034110341118021804841c00800c54462203040c8640c0b50f107001d00100782070301000004503103d01c0001c18400d582c0041d200c4250140e103060012074031002240c2c4071412681400c0c2c0c001002c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 534619874 1250 534618624 534618631
    0x80f150d12211802091308030a05090d09030507181107050d02070b030f01030605090307051213050307120803100b0703080f06010503040f030305071206030c031112030301061d090717 80
    0x403602e85242c80300b100f082c0942d80300000b074041e940706060b90f448003c100c0300700d400b000000e04039080203c10080a008160400b6214500342c50070740c0c0324102480c1d403e5403002924040140a5046160240318408800713801c1c001d07084104001040c40c03001100904e04d182c0c810b0708142c9441d000300b42400d0420350104100c90084c200940b59902c0d41c68001120030003440c040c01700038a495245d0000c1840b0303140030000c1c2e546407a04041038131000c9084015001448c0c0c46102d8203010b00000300350000380391070042098400c480c140e9030a110040d11950f03aa030b0480e8002051480b818100110124040b078002c805040c28501c0f039151807050b41402042c07020302c544000c00c03090400908008110010300400e418400d6558541004185038a402ca01030382e24a00344600c4801807440e21000009100c50040e840302100c2c01000e162070150000001d101c181400211984010380c4104010080c0b503201c0c1c900c211260f0048091001d04a0400b4000b84114605480c0e410002c0c281041d64610310030740c001040e81 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 534621124 1250 534619874 534619937
    0xb0115020d1d010f0309050d090302040c02010e1002090301090c0f0608060603071e091805040b010e0601020304030b0c0f0c0618010e0d030203060406050409050304030b07080f150d12 80
    0x21104028445002e604a040404504204400340c0701c40300c150003600891050350384201690b2145a17040d000403e072880300e2100380c3c812400c00701ea11602c94010b126490b174068040010b406140204444030000c0d50054001c2c9030199a10a041ca0109548001f40c030040c10000b11039040c02407030440010800d12001c0c02052040f0401c2040c0840d0302e070040440b18007161200709000505c14413103010f403038110b0194404140460ba03c000c003128001103038020b91080d403007040350740e02d145d807105080e1000c2082207500f00e01580c0308104c10f0003c40c200748c068580c00030b052201d0303e252404001d4101d0281c1c0040740700e140c0c0c652043d0305000d035482a50303284807180004c0704000c00000e00c3c1070080c1961003a907040f1001c241766001012588a8445420000241c80e000d03100740901c03c07961a003c0d68a6206202c16104000240e0215003428031070b065042c00340060b804c98454030380303586851400304902c1d0b0700d080340d12071484203005000900301c1103107000d441c02a407508150307440300b680701c004140400891010f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 534622374 1250 534621124 534621137
    0x60106050301091e0204090204030611120f090106090c050702030c0306073e1501140307090b04020919060f020f03030f06120114060411030907050411070b0115020d 72
    0x41840d60020903241125070070000031510b1000c0b65444038070005804101409140001800300d000c1086400900442e4801c40d02085240c0c1181d1000c07429000d0700e04060324581a08002c2900980f00510007a00300e642080002480d59075000224111400100d011010402c007003042801c1d45002c2c8242182d06605401519041c500343d0340040c4081c01c0f510394400306445c18203242071030141c3d2100a0190315001e150558078241c40c1e40030300b507a401c101a481d80402070b001300046082c4080d5601428245405030043c01c0d40b5091080c43d5010300041400290855424064100c003981c400301d0740d0940c0100b0052034443c5a0820a008110596000800040d0740c031956001441352400001c9980c018103001113400e0701e8a4080001c2ca0101640c03105408542c2480034400c107411540640c54083d00085508000c80c5128282910840c002201c1440b4a0307041600304100a041c95040107a007504080c04030307482c1c89940d0383c07000c0b003401c0f02707030000c0241134001002d441002da0100110020f0208904080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 534623624 1250 534622374 534622379
    0xf09181b0f08070315080a21050c03040b03360d26100513020301060206060a120605060112021b0f010b0d030509030709060602010b01120e2505040603080d0e0601 71
    0x10b45070b04405400203007019a0b40300b0010056261502d12009000a94203441007174889043c1605849001850302011440c000030342d0a45031300810840d41482c101c1005035041615114541c4a070303402c01400e040f400d40300c86c19000d0401000525030b480d81032025014030501d0140400481c588891110b2060902540d1203c40300098507410794041640100d0840c1d01c41682c0300c80c248050344d021684069042640043d81c0990400c0b1600514142c813442c3e4225411650384100f00070460072288200c00e44100c0b21114880404e0032900141d600440c18180000034009800c0380004982c131000d885000107030700000712603d4440c140094840c12410000030301000c0c45482c00544001c07082c04004060200c0002c40d5505a00c040c000403008008000e0100101039485c10003078082d01407a0013030750008442c004020b52381c0c01c1520401c50085200401030102110008141d0040743c0e0030301080c0c51202801d940002d49503158000e0601540c450b045960303d540340911040c0070354004001e00e400540002005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 534624874 1250 534623624 534623627
    0xc070302010b12030c0c10210b06030903070302011803090605030a09022812020609060309010e0109120f0c05060a0b0f04052e080a03080a020c0d05041505040f0302010f09181b0f 78
    0x1026407023054144411451400c0c0050000203042e0315030710300c1c0c01400c003004215216001102408606001ea00240240c184104042c1c1c603c2c0485034005001c202042c80610003544140301030750313210011501c0050a00c6903500015005140b0b60300d40440502c40101e8500c5681403103a108005114450456440414550000d021400707031400c92030142d407011000400020b0709420410201103c18020440d1454505042004078a0120030402040301d82e07144081c0c40f84608205120603821001a043e552103981a542c0508083c03085158004420b81d4100c91a075264421540a01c0132085241c40281100440b0454030724401000045803048440400103d038010440d030650390350610b00303103d0540e2207003410402030140780d91208003031103074120300200e098005005105440f5060f40340b000709107840700200c500d481503008030021000320500400c0154002d10080c20080b401d030900c2e1000a4546803c0171412403032209020009498078001c82d491504191404044500f80c40c12206010900c0c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 534626124 1250 534624874 534624887
    0x10204030c140303070c031a1e06040510030c0b031008070b03041712040501060e060a030203071403010207080d051609050108130c1805100e010e0c070302010b12030c0c10 75
    0x1c2d10605050380c02e44444a550300b4012151030350390101c03c040d07a2540383d0500980c2420f0034950b800180e10f80001044003400e00945481446c01a0b070012405580d0b0740040c4405008084c0510312524800c140120004103201c6090002d401c820711388039243e2400000b10344201c0f041394440130b0640c00000083c800b540c407040440b41d00c203410141c66000b1403101036000780503116992241c4c1c07034800c1c06800c2c0030801c40b064100000f100c20500203103646440c0c1d2010041d24042501c80254954040304007002003095000b041d030800d4100078001410440180c90307000b03041c0c0c0580c2003414034640c0d490400c243c18200c01054440c0207100d01d003028030303107042000191040c0302c060052992501c860800c40b040149900c4803401800c40d503101e008109401c111100b020700400d854600e0100025030000c9000c050041c1424122451504a1843c40d1114458a40795a008103400d608554940d041d2480d20b403500c000c00380010401c10021a41c2c0e81c51400c00e02d0600c00c0c04c0b00c12911175168a088070000359840079 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 534627374 1250 534626124 534626129
    0x50c01090f0b0c070b0d0b0f060c0a0623040b04030f02010519050405070803040b0d0b10050a0c08040503010c05030a0c0806100311070c0b0919120f0f051e0f010204030c 74
    0x8000e9549007a40303c3d91914142842d03101420041d00000c90001c4e060700c94201c01d40c02e030700030b540700255032288100b0005a4052181741808980c0400ca903a008116190030522180c440695034020540c40c1c07903085505000100c5040d92071f511541c1c180020076034450040144412284020041d034202210308c907021401685080c1c0c80c03180c4880100d0b06001c1c007440803c0c010004c0b10304423680c50f40e0700d880300800798000c4180709200900c5c00c0300328a100c0c00c0040740c1c00c820030701a41d14540780281400301501c003403030034007015156440144400708003510700b442031018047c5940c403015106e281000910b0b054401900120040120590030300038035485128040c1009803030350a0104a0029000940b030441c09400d00150286100b12070008003840000c004200000c002e5a00c417a041048500368501c40c01035104000c4140d100540b4440400c00c6041c5800c045489200161028181c60f00c078039141540700844c0c1d00180100c0c04e402049518200906803041c81a0f0f4000d5092a1854484101c1440c003407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 534628624 1250 534627374 534627389
    0xf0801051e040227160203071a1003050a200102010218120f03030f04030f050304120e06040b071506080d21110309030703080609281116050c01090f 65
    0x1101042c21961500620000c0300d41c415034040d00507544003150140100241c0340401034020108400c10b160344003000711480384da003004a441c580303640c5010b01e40d014080180b41c1500c0811b00780d070100000b001800b2500c9280d01a00011521520303202900c51706500c29074031035040d68410003025545034035400401e40c0c038030811680100d10303109540141c4d0030b0100900c030a242a00000081040380c1c0c00b41c4117040d0056010395186c00c04418140401d607010321003a50003408404442d90800d00701d81c401c030b02410350b00d5070250909091035503500c00441e00c2e030802c120440e1204083d11700940c07840d0003445140024048a00141a401c0403110003401e00120b200390301d810310320b1030440c0441a8209400415036080a141003030742c0c9282000000d80c481d00050305c210001040440450054a4400c03181c80c0900c04988030400218034000015003c02c03a03041c0c50f081555110034246400810b40790143c00c03124218003242c462810249000c0c2d040c5410312446d01c1c1442644081403048c12184c0340700d207080e1443c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 534629874 1250 534628624 534628681
    0x2004050c04030f020f0f030d030e0f030a08150f0a060309170301050a2d08071502012a0c05190c050409050a0f05070302090a14061518130203010902040f080105 70
    0xc0c8000325100b100c0a00380380f47c00d40b203581150008558180d00204414088074160b815800128010070380343d10070554440c0001c0c005c5408144003905000c09040e26500c0104041c07032414040d0302140158602c2c4d0f1004001c00e40c4c802a40d001d00144901041c0f9101c0b030390400d140b5642c1828006014240d27280252402c012225100080c41002c80202084508000c026074a0640d502d4124982d204030b03a014400f0781013a00c81c00c840c147ca005001e101c07035041d1191124101001c0d60302e00700040d82800001c2104001c40c96203c400410000d03c0010080721880c0d2120201e102e0900b0140c0c10800d90368000b50245142207168800703c1e07000700c0c1e07800c00c2690003c26600103030710a05020b45803060980000c6c0d401010442400f40c10800c0d035002840a4046c100250381980d90001005000321198103500b11481c1d00300401c00c0207004502c0070080100c00180b1980007191a54481c008036007098222280e403d83c001401d21064000700e58060050542c0c030b00038440e40c589909410800e48100300120602040e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 534631124 1250 534629874 534629899
    0x51801060f0f271d06280b0a022505040608031e21070201150e060904080328060801060f0605190e09160311070209180a2004050c04030f02 61
    0x1050322440040450f158a0701450107007501c0f514441d4405d80c2c900d0b2241440e000141c80e0140c5030503c1030b840200c80e00401c495540b500c0091322070b079070204a00c40218000c409101022441104413442c80980c00c940c001c1c4070034180024001110f0b81034111101a0b44144090000000303600410b844209201e2001c0d070703d66400360504000c0340e1070308080340308103100f100420030b042c0d070705510000020111a005a100d2942c418201441c0d50065490075080340c0003500240105080344010746e040b080d01244800c480203461801c0003401d892004180100e40c4403030081004071400d0007a000a020305103601a051490440041c14038400c40350b0034440d49d01c90411510700075002c0e451000c5e0741e003006803200840e460f00440d90b40b0420b85594401020902e4032581c00303400c0100d081510301169001c2c24202084c0c5983c0c031001702c02032110350450707001d03c204c10820f00050191203040401e0341241401c0f04c1c1400c400c20811013034480041c407202000406100030804113100c00e0000440640582d03d5008920 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 534632374 1250 534631124 534631187
    0x1d04020c030f0a2c1f02070503010c020609070f2904050d06020306102a0c1e0602010c0c12030c0903140c0103050a02030606040302100207051801060f0f 67
    0x4291a82c000140c0c00314030b00c0011038201c40190b0707108038650015a41040c0160b100c0d08100807040c2111303080002d442181511541c000e261604141160044540031651200003d007134910a014000041c0c01070b4041c00400d1008001440103880b41412183c0074505103034141d01402010104071008001c0b50140510340d031002c030215005054064805003d502c100d00b0800080d502c152100b42c000c04d24400081e20251044905400d51400b07140d004844840e00c10341c600b0031801407142500d020483d42d000241c040c646240382000400040048030300241341120190842d9a000d00901c01d106508426100180310380075001c0241c00c0600b00001c40c001007900450b0900c081d81c0006009080410301c2d8061703507800250465290b00d0990b4140b0881e0b445074580000e83c00150b4007150401000d00c07052006190a0b50344181c03490070352044135005aa00e000081000b856880d1000c01001524010310000d90305ca07640718500049418521003081d1903100040813081c00003070a40c21203040800d500d0140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 534633624 1250 534632374 534632377
    0xa09170604021507151d0c0307350a1a0115080105150c0a05033f061f080a1b0c0803220c0f0e1302060315040903020a0c061d04020c03 59
    0x51000c0c59040000c0840c0081b02e402000346c02d00c01504d02e10500812000381d20f000902c0ca000e03a40c0071141280d078018800c9540c030041300011020a01c0100304e83e645000300e00100030f80040b5138002d19000c3e9407055015501084044107801c6084c2c00c0c0c0d071071340b40030141a801100042c1122426610b40150b0501001c0c10f001601a08203240501e019160810040c071400101500b900c6550031414501c0ea1415510070003c6003100b01e00d40711034407080880c404541c18a14081e58400c0014010620051007440780300f0040d0100020722010070300c14030038043c01d02000e11602c1214003040301c1e41c410030703807240b03e018041104400000f80070040010004403445103003014004030241e4400c0700c0520031130b80c3c9402d94207510340d0301a040300c0000c203100004418441d00d60241c082c5182103c6042980825024003542c0c2e80010001011144208081500f075100c500c129040103009901504a6011a1802031aa00180e50100041001c0b0003104941106c03200411298038a0883d0b0050740ca440b03000d411403d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 534634874 1250 534633624 534633653
    0xc020a0302041b0305010b16060c0509090403030603060506181609270c0f05040605071a01090f0f0b06120603162709030e04090c0b0a09170604021507 66
    0x50b040c90f400b000c07482c00607907051103030015a40701400303242e803201c03906c401e41d02800005080407070300010040045512a8084402c3c840503141c00351401c680c000104200003802e0b102200002d40d941d8041051060511030690800c9080380d50340946000707020031305030410340a81241d644d206070103103000001340180712400041814100403503078a05d45955014807440854495660241440c650440d807d108064401805082d605c96034101403e00300d04860f543c02018007160350b8494040e00c013040c2c20b4610b82450090000041c04101050a6050701040c2c40d110101070803500d050042e00e0003265200010390354101011440b81c409940e0b45030019181901441c80c3c0034040417180004607098001000c0c04440381401e03502c006040e41d11401c50422a0183c050107800912500c0c40120b40e45429040b01c8102c0d80941003040d0080e46510051000b64031004409000c1072a454041000b8103c1302060400440c01002030541e0f440e0540108a5072160805c802403950800a1402d04200e84212055003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 534636124 1250 534634874 534634879
    0x30a0b010602030c0705150301150e031b040e01050f01050d020102010605102a0512030c0d0608100c05090a050402071b0608100510020d0e0a030f060b010e10020a030c020a0302 77
    0x1865941da1000394495221031a400c200e40a510740c0031a07a4200391103520000300030742040c01c0c550380c81c0410780a125140b040394003040208403040c1100c19501048250080c40c800d180e03403070140540104100c201d80140d50003403c103074101410400c0746505a210681144c0e41a140081d0011603480101e00529454015990100c0d4030081c00e241107600492122002d400d034810f4038807070402e104059441a404002c000e155601154144105011600165800400c1c60315007500300940c4803805000e40303045412406142d40140ca0701c01108940d0701030b10066044504007940360402d528040746890700d0b10301441e03000326000101c0204224804080603a4450301c035441164803500c60100801c03800c0203841c60240000440070108240c034202c80100401e00c80c0d9001014540000c1e8009e4490030044000307264400070210000020400790042c101c505440340c1d2000544500c0900013511071032445020ba802402000310303003000f0f190000303141d00b60b154060030710045002c2c0a200044c1c1e0171146070402034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 534637374 1250 534636124 534636143
    0x311010e06030f01171b010c17120f060d0c14190906030209160c02120c150405130c0912060902040e0c040506010219020105130308030708181911030a 66
    0x202004480703072081c165401ca175142c40c2d104050600d00c80d038070700c14100d56109500310206101c055601403103920045501c00c42d14120081c1900c0000e650640190f11800c44801c400760030170804000004038241d04c0380c81101e80c111100c035151113601d40da03010740c022800481d440ca94a86150343c5e0b9500055251074074640c01022040c1c4034944540a0701e11071004a0142e240000496101901e0801100a0340aa6659101c1031143c0b5020072004070700758030795030030580512008070425482d005003c800ca80d41100540e642c40b45840140201006075a402965691903d8541c2c5106070740424082e0450b80200e142c10340c401034504083d4010601d41c24000d500918000b120741004001003600c5070480c030104e40400c450781d1001c005a884000d00003039003c0c440d0403044240c00540c001d43c040e0003903a40d800117001c0450384a55030501c4070f9006943c00340204851004200c0000070500c03548102c4503092000d85401e1004500c0c0c2d522481c2c80c52001400041e10b403c0341c40d83d07510200a40c4a8442c0c104283c134 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 534638624 1250 534637374 534637381
    0xa060c03180807031a010902070f060c11030a0306061b0201020303041704090906050601180b0901050c030706050112020a06050f040b09030c0a26030702090402120307050106060519030e070311010e0603 88
    0x340002c45039202c0005483c0c0817000041ca103d035442585c01540d04070b0583c00104055a03a218028101034041e14288419600d5050303485000700080c00c912821030301c0000d1042e04102028052170301c09100f00039410b03071011840c40180d03400701c00c4c1c940166018a00c03841400c041c800081403401513810444915151140c171809210240c1c1129005010a0700ca0b140090507040c0c514131041c0d40303400350f1200901e04002044a9511500c014204c0a154a05590070720140e079413a00d055400c283c1c00784500f024601000300a620340301280000503ea5828118640000321000320498047c03403244001801021034030301d05a0302d003030145503a800030050142c2e0301d05841e811800c5102d02508404410b600030202c00341d41c100000401c41e440c4540080040c00c8558581c1d08121020b03102010383c0d0072600040c403441c000030f030003402102d000c0c016680b00d8940310007080c2981100c0084a104420800d42481c10800c143d1a000c42e00340b0035640c101205494544640340140c1ea114142d09403140c200340c0c00803c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 534639874 1250 534638624 534638633
    0x8071703120711030c06161b08180402030c0d06120308070320070c08100c0507080a0c0f03030c080a020721050c07140a1a030c03130609120e0a060c0318080703 70
    0x8807480381800680801000302d401c8812100c1580300280810b5002c10102300c0804140110064500407a001c2c012684548162002c10144c0c2c00c19a281154004082002143e04145010300030280c0280b01c0c40240700020340e200104146400f4004505040d600d0322055081d4034500042c03a45180c0707400e04d465598076030f4070f00b00f50165054410381c3c505000d081504410069507000c1d152400b20b10365199030400d1100e4450400c2a84540143c0d0240b104111042000035441c0414540f01c40c0617460000d2007a010740d50244c0500c8000381300700d111520401103c80010407400d142003012445c1c101060707020503240701c1680c85100e45003400b600d40c030802200050360704a441c0c0908040000b614100012945d0b58404901c01c408000004a40c500070b100040c100300488000e145d0216004007140301032141910385408448140c0e1080e20a101d51009000e2201d402c45083e00030f0100903540a08454980000140103100e4580024104111080100302a10302003000b1005040300303500b40d800d01562881d2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 534641124 1250 534639874 534639883
    0x3040c0b07050102090d14070501052b020903010c090819151a21070f0f0e0408070804030804091b0e01050a050c010e0703020114090f151c050108071703120711030c 72
    0x42070041b0b00c20b8400109c1c01e544034400b6200780100101c200901c008100608400b400d0118440300441075007403180d0a0b1b036540034004d2440011841d10b0700c84041e4108034031281800c01d152a8900840c0e1180d0350840000d40d90f01d02d94210700c0451400042c0d6401690005420448824a513030b44030300742d411b0017030501e020b1005100c0c00c0030000b011598840d03560a441400070090f40b049a182c048255001c001d0080917910181d4001c0c0308003882450810280d0328000c1c0350708250004c0d98891030114090024102e6441481e90b84d02c8410422140c200311404020205021852407504000002c11400e03d02c0c1d008101b80c6424460b580c0003445903810364032032a079581000303201c141d00141010b60721508e00c0315a003040700da50306006056600c00000d01e03400d01072909842d0300c03184802c2d18208580d01801440c0c40c420103400560101c0407450b9494601030310300d042010b802c4210b00008607003600a20380000022105d20040045044001d5a034038441980c1145650206400602001078200000711012a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 534642374 1250 534641124 534641153
    0x40510060e0609040b28060501090801021c1505031f1514100c050d0309110307050319080f04120c06030b031f110a1e020303040c0b07050102090d 64
    0x140410140350307078030211488000203990039034008a418022802040042030305661000103060300c1c801c20307200d001d0140e401c201c040a00c0f15529583d010117001a42e8010881001044914020b608204c090740ea82981503012108610050355035040c248842c0102c0308800c4000c1c00020181c40c02464001420441c2c0c00d41d0030140003050b481d000030750300c104007003408605c1a1940c0d60351401201c4580001e0002552642074102c0c01e001c1d22009841c0066007c000201c0703041803503030f00030030005810f240034202c01d01540c501512941144105004036200098454046207010480042d8058942401e4040d40316541840c0000e10f000500071070552140e5102d0340d144d0b84500c016030226039403030404404480f04400c401c1c0d8590003480710810740a820400c0c1c10140700d007080c1d001441c00a05124020a5404810800f0206408441c220016041c1c400320399015101c0340051481c5103026903c0761280700707281c00f6102030100042015014003109505560346501c0250043d441090030381010005004500c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 534643624 1250 534642374 534642403
    0x40b10080405121c0203060301091e12020f1f02040503010608150a0213050607020a05041a1305070503181614040b10080a020a110a0c0f0801020a05041505120405 71
    0x2030f07403110300d5041c40034215403505104154140040c00740daa5a40c3c042c3d131020b0700701c60f40f641d02ca40c0c003240800d4408100c000318410a101e400d40c00000d600e40081c4038000d00c1c5074135080d5001411074441e01e010100305116031010503680e89550790f141036203840080c0660f070002d54066191480114210100048140045103481c512406541c0c03046142401c0c0d1040d0b200130b90668006c00801c010601f071540140c814a8030042030002d405440e080420100e5159031907032a8000005003819005013400108001140500c0805001c4c9203040c0344040c2691002402560000c201000e084041d00400d00501034860f000c260b0320b000c90b50340c45014840ba05600600c4a104601d45000d80d071043c548050b4180ea40c400c9501e46407159902c054091000750080a80d80042c000290405841c11070107000c841c1d089441400030300642c2d8203002c1c0da40c01d206415082580560310411a40c10440d400034280c40c206d942c200040000c8025044084032503003e00500750f03e008041c0c0041c0000c0080108200d100c43d20300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 534644874 1250 534643624 534643633
    0x1509030c06030e0f010c021c050d0f0209040b04020c210c1b100503040f1106090904050a1a1306020724090501050702070609030f02010509090f06040b18070e040b10080405 75
    0xa0084040c00c0f6421180d901c8003580c0842303a90f0b840011152201d281004440c1440c9040c106407813800e000b07841032040e040c1240360703000032000750910b020310406204210588085091401d813140d00796850400c0030000da821a0040c0e003012506411108555504a03d001620144642405a8101d4101071881d4031711900a0701e8040000c0c0303100c2c3d401d40f4480c41d0007000140405c0900d0315101c21002d494020072303400039402c21070718060741c56094a00d80210f1144000b410343c42076600f0210300e200c184604030f481142c2d030f81c0d0510580c07503006005200001e40200b070040c0c6e5400039280c0050226000e00141d03045440000c818a080303040b60b8000f0760024040c0009100940e10a0f00c1240c8803c003d002c1c0001003114003030184003144040020100301441818041e00d409104000281c15001c1107031b01780c0700b80303070100c0401100342807600544a1003c015280c00301c600d48800c40b41100d50100078041c404021000c0118880d40c1d82d16003010300103035805000c40440503117905c401403101c1d404036000d0314141328 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 534646124 1250 534644874 534644893
    0x80f160b04121d04150f080a020a080606010f0e0f150306090c090102071404020708030c0d1a011d0420040609080307022d06130303081506041509030c06030e 69
    0x50a51014a50b42d0652003a010040e03802001300030603c010208907490040c42d4086000c100d503000010191000d10024451100309104010000c01e184d0030000090b00034009201d0640d820031134807240d0340c41c0381c10040c080c440080d001c52401680d1000456201c1da245400c980101586030065000b404259203c40d84d07607880d541c2c038010034440c42c6025401a400200c1c1000f09a46816015007040f00050015250044c1502d0b2200c10340c20603a1040601c5e840002c8412940d441c40c070800d0b08090080c0e49100c0c03500103400000e0f201a048422844c10f404020744210f246540c0c5500c000c3c041c9440d9000190040441a8501099007050080201049038240d0102d4008000010344511a0b4000c1107a91011150310590401100e0f0891104218400c1c520f070100c2560760002a055820f010138140302c01a00d075050050002c0d0001c0d090922028005564132202d480d0704048078280c0d5034000c483c02c0310001c40001158200804ea00181483c0000c0d43e02182080c0d00d500b0100c0408005000c0380c410b0391 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 534647374 1250 534646124 534646127
    0x21010b18040603031407060f1b120e07060e03011506050901090905040206030c0c070b07111e0d290906010e2203120608010c0206091006050a03080f160b0412 69
    0x2c82600026000c0b07030300c840d024014110500000d281c4984100000716143c1c204c222100c064800c940c40c0d01d0343c1203000d1251042190b5124020103815044140c0c14000f00c83e0010215850b516980030700c1c0302b004218807442b00c242d01c094020b10300c2440d502044021b002d680e0341340144560401800e507400112100000601c0091a00806c0d00954004100500d15140ca080055590380301000aa603140100700c0000350948031180541121400380a035200c403080d5060410950000c001840c2182c0e05030389034101100d842c0c3c1020703a84040e40c01803200102216644047c1c400f80300181d00b440030b0000040410002400102e0401d04032482a05503100d540c480300140d0035841300003c10340035a5031070301c00301c080401c1c440c0d503003480f120301b4140b40001e80584850546080d01c00d605410300140e80100c2c140001c01e0406c00c0000d2070b9a050080801c0440e05150009101151510015120002c0403842e1881c80e06000100e805426610ba210003648825140c141b0020104680944060380030000000405 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 534648624 1250 534647374 534647381
    0x7050f03070605160f0c080a05100509030a030e010b0402040609080f030304120507020f0d230c130b03010b091602070510091203021c09090b0a08060c21010b1804 71
    0x100c0b80c0ba100e1a0400c2200800b8084840c200141036804018040ca07000114010f582080081c0440c4c0010300b02c20f50941c18a035150a0350906500380c82442c09041105241c40071056076030641c0c440c9000301c0d80000c128121409086458801c50b4070070310008000995540019050046070350240650b401034200140c030036100d0104130b4000d4420348800c900e03180f4991290000703003140d80c8018030f01d208100502022a0f280d480c01d507411241d14a171603025060803170f90303410211014074140000b01507410580020a2015400070741c04080c098844110b05c60a59080d0401190310344081c2c00c40d01c1500c0d001d510a140e810404440c080075014840b400718590500321036000361000c4c2174440812040c50241e50100081201c04154214000c1407108080300c3c0b07580203510740c40c01596644022003410700d035a800440302014140d620a803070701002008884404241e440d84990b01c803005c242c070b610000a88e88003420703030070010f084504a040001700e41e8549680203030401000654517a41441401d4003440102c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 534649874 1250 534648624 534648629
    0xf0c0908060705030c070f0f062708091201062103080108031206090a090b150f03030403261306050403110904022d030102160318031e0201030209100207050f0307 71
    0x144200700003140f89245c03200500700e5500c02d0204075101702207074544071309440c40c03004112038441e16210281c41091008801100e003200030b1110700b41030142c1d40d4420b441480780e03248441c0200440b0215034540343c003c1d84182c008081b045080f56100c1010505103c1d60f100103038040b004a0006030000c61030031000400e0752101610340d110400d55848540c1086081d0300d006025690103920341c0300d007200107810700781d845009010041c40c4000706042201001042080e06600c035009502c1480708001169484501e150701400c035000f14400c80881750f0903c08580300320403e1050004003003600013904c6510900030300c1101c4c0203031000d950616019013000540034060f140a0b6204210351020a2104031041d00b280d40c5541c0c0420328151120441c01123804ea030400c000b003519002180c01c0d09030615400402c1e2031010020f11040003c510709640d20500d208101c01c0707022800c0719030f4140300b2045902940c101e580b408001002c080142d458100025511121406124014801c68460408600740060044103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 534651124 1250 534649874 534649877
    0x40f06080a0c090c080907120f060f1e0b01050304200d080c01050a1a0f011206080303150409020303040e060604030b15030706141c060e040507170312010506070302010e010f0c09080607 81
    0x21550314106081403c40311460041d540070387e1650344840000c415128184034190701d040c010a45504403058a002c0c0d0840040e50a065420315030dc00310680c5c0e205084030343c055800642440d01e03261000c0c405619100b4100007903041242580c0482c10300014a01400482a003a0001d000c0e9580b40a01c0f0030503103000c01084100b2aa0745801082140f4240041e8102104180742903c0d00707071840c4260100f964003a5102215640002040c8003441d08070380d43c04100f40900799814800f0303001941c0400c2e03481c49144034100d0318501d10f101041096403184200c1d00211381104081e0341d141003c0d101c4940d0104180105071091003a00300005003180070307808a0f80d1911000d2002420848147c03100742400300c41d04225050b940d56218003151500c0350400040c0564002c0c00113110071070406030600702140311f08409032a103510a00021003900c860303c018506441041c1d441d01d07240e15803031030260b026022030910003280354240711040b000460140c0c058131001304c45541e817000d881d589424140c1c58500a603900030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 534652374 1250 534651124 534651133
    0xb090d03060312081504050109090203060a05010515030702031c050f0f04050304090b2202221a07031101050403080601090608090606010c230c0414060d02040f06080a0c090c0809 78
    0xf01103016210307441e40305080d030a01c1d901c0c4880d0400000c048600136081f00c040340f43d5894001080d81010800070754090503206040103e0f50601000039100d80354603a110304150310000008002510030710030f1314644404400360030034401502414030042c0000f1208810206001000560440e2107042c102d030160303401070051032406052424000180020714003c0f0b40295204880413070340b285a903158880d00240000041e12807548228100d1041c0d92250000c0483c8200c0c8803d10408000c2103500031000c40000c100c65981c0c031140380648418808411308003007546404100000d0540214041d071148009036a445107103500c405056401c10000c0c0c407292070550003400010884d5000300c079583c00541c040e0841d841d00813000000c0c0e048241c03004138155400d130803201e203010030b3b82014058007420703e01616070340c070f0f9924091010034645070325914080d00c696200ca581003160181a440007014001200980f9140b007020304000e0480b02683c465480f00034900251070400c1c500c0381c0403250107010643c000d007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 534653624 1250 534652374 534652403
    0x103030801180218130b0303030103060c0e060418380a06050a0e0405071808100606050c0a1101120f0506190509040f03050d181a011412010204030f0b090d030603 71
    0x80407010020440c0c003803881c0d41c0d1181b052a0340d01080510300941c03084401051500c4001030050520b1585200c95014903002c0c003042c084d5050780c3d041c4180c04007070150300051a1640e03880c0408e008000c070755155140892a021681c0e66205915818204902a1428102959146011141842a5800800082c9941d1051f07030312031400d0307004241c100d0301030319000140542c16941c1c411000401e612038075132644100c11b0100d854003180507501c01050f140c1002ca090000d0306c451246ca51070900c00041c40d1034921080c840c00f9a016a00398400c20001c41010048030144d44410f8006140503100507221322007041c0520030000405102c0c0d005e481000c2c015000707a40392903070749001140342000d00702e09100f802c0c0481840e074141c1b071180000460754094031b1168001c942c10038900c0f141004403120450b03200c40c001400b440e01c550040d60311600003550038448200140c1900d80c0207002e150001044d001c0008061400c3c00010007865024803104d0059454100c030750402035080310554400101065611200c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 534654874 1250 534653624 534653629
    0x3090b010e0c040b0c0c030f10060b07080a27060509030c0402030603190f2909070605090609030106091802130b0a0e073f02130b070203150103030801180218 69
    0xb8000c0c40c0c0018040b03a10103186e0301c00007810a0400d00701000c0300e034440d08040903d419603014102c010490360701c01518001d4561110a134031312a00d000c28040c0030403c0103031100e6903c031603452013a40b6114000220440e8072940014859440711281a12a00c03e001284480b407505200710307409032400a0040c812110300c003903907031456682e00e4015120090b50084104c0400e0b05544c1e0990110003000c801d000882c0504459007910308058207039030582c0e03c02d00c01401480c0c6c201d001c450103998111045600c0b08070020000780500340c0ba07000411283e040520017000035154000c44140140300300d880064403003504104008039081c911742540d02020b0b0800821000e0405111580c101240780361041d82c0380c101c1000070031030b10942080320ba0040c07845003401a03002200c4000031251008410150720b0702c441d0340035003e0a204035010f85402e0304000240c227402c6640410040b541c01c01c40c103003e01c0d00c1d51f0b52420003800d482c0c000d11500094094689070440d52000394404c455440d800c842241c2c003424900010b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 534656124 1250 534654874 534654877
    0xf1103040302040c14120a1112060906060408070b0c120a05040608070c02190303020613020a0e0702031e03040203011506020316050111040e090f0a0b042d0303090b010e0c040b 77
    0xc0c5009100541413505003201d145c800a0000e011701101c900880c1c20300403200b00407144504200d0394188410710410310f02c01d000111040c1c00800464485003076480c5e002c0005c0c005d03c65640580b00f58420403800142450800001c0d041e41039100e010f82c0d03200da0000041c410103104030b080072000164100003d0119501600440d44c0206017450103106d840025030204910358419001c0c0f003509151000c0800800d94100701d8076078041d081d10a00b414420003a408605100894010034102e51240f1001a600030306c01c00a41d20003140100c403000c0c2c0b103106070610910950094400382d0182d42042e015200c40e000c001400003c840c0e40364020741c5001c20100c00700b0903100c4421070841d0b85540721300c1c450410040080180002d0903d8046207015401c124008510b07007213600003034041d180c01c42d5440e080851080704034240e00031f070800b0f0809003d00c8144c051040c04410440c121181c0e5109140801c1895410f9202c40c15081c440c00e40c0800c543d803900d40a0440601c1110941c440400404c010f015401c007900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 534657374 1250 534656124 534656141
    0x3021504050a09050901230f0a0608070308181804050c0118231e0f030105070806011107120b01060206100b03060d0c091103220201050a0e120f0105070f110304030204 73
    0x178000105030803405035045101e1003110486507074451a00c10b11040032940880d0070340000740d8031810400b5603d0511a03030703150502880701174050390000c1508000ea00401061201599004101110a522815080104210030b4400b51840d108658180f10035500030741da90441c08115000c004007007071a00807048104506000e00840421095005c0b0036070351660960f56140350756591401d05022601c00c180b010008600440902c680e04100900c881540c200343c80c244c020100303280403516042c10b040d000f89800e07810ba200221241c21035040e40d0900050900060503904258265910760b00e41c00c840340c2c417a41d0940a85900c40c1410008103400d80340c503140d00356803948038420420441d9a10f001140841d24140d03014107466500004001801c00000301c080c54558100c50201505040d03034000034448d014602d241800d0100c4602540c040d81d9581c60140040581340c011500e1445a03c00058080c00f016500400407488441c100d464160107814014401c81d803200045080c18695001c000142200f40b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 534658624 1250 534657374 534657391
    0x115111b040b0f0409080309121c0207140703150f091a0601180806010311010c03090b030c0403200909070b0d02030c040803030c09030c010f12090606120c03021504050a0905 76
    0x240e05908994840c1d02802c2c417414080c200103501c83c6002400c186c100184007900a00d43c1004001190410910803c644c0c4400341501c40181c43d0b07000c0d8a04100851080340740308005204210001081050542c2009810881060148440644022404265510903100810102d980c4000300e6004141d2080254044014503040003c01d00c10544c0e0068602950131186040d00090f00500910035200302c1042e10f05828070304008040f2054400a0940d07500b80560b011038807001011900011100c0b007074030f02541d00f08142040781801a076202440d112145011406159180c0000b06161b4002c201c000898031b510070150315151040050b80001e42c0010400c1911500510003c01d110300104061032040c8581411142c0e22045402054581440c0d004018104501000009500c0e07902800d40181c210b41082d01080301d42042c605000500015003200c00100c00b403500c01424400c608810800300c1e4025550700c410041c421507414060701c501d00074243c0001f5141d50800403900e40b68451640541c09 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 534659874 1250 534658624 534658639
    0xf010c15020a030614060f1903091703040b1b0d0902030102071403120c09060412020a0312180902120402010c140d0906020d090501120b0112050115111b040b 69
    0xd003403005007207030003054907400000c0e81c8500c140941c12103103c44d0014001c040356603500f0490040402c26140c1b1030f1060080e108287c031018102c00030b0091b04503c0303007250b018000b851281048103429105400803603040c2d800028503404110940c628480d09600b0f00340c03039040710313182590b81c00d01000a0011a1000ca8042d9420011440403032560403807042001c0711080a560341d9000101c1040d159040504800364203002003100000341e035a89e070b0854046a07044690200a40068000542091019480580001501321805110a80c044075039005030301c0503129843e086440d0303080381c412800f6039211140340840050104004d58020103200b40c01c0781c4200a109a4014042801c40c00c001041c0c403414041402e00c00c0611100e0f4050040b0145011140f0f400d845042c50100000c0c0107009006400510781d036101c6807a400d03a441450302d002d038450308480c00d1000d565100180e0348500134031401880081d1204a08280600003c984c21101d00254280c03080406004810800145100005140e101c01d2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 534661124 1250 534659874 534659903
    0x509151209011407031407110a0b0108030a0f020106080c06130b0703200109051c030609050c0c1603111309020904030903050c0f030307120903020d050d0e0603060f010c 74
    0xa4250010710901c006000030a40040d10903800c0480c00000e040c0b0360900d8240b0307480d805510108014a40d11032050b00e0a20812041c401e0340b03c1c14000d417a940585003820b4003001180d034007070010040c4403030310503036460b4a01c220701403200306d00300c800f103018624058101898000c0a49008005031505900f40940d48440c1d950302ca42d250301c2a40010412404107400103115000500781c03d928040380d0b110f40c002844480850750b40c00e5104c89280c2203024648030442c0100c2480c520944c1b00c1d102a100d4481f04000b0303418030030040000303504600204142407065607000071048210f49144d204480d4000c0c406410b40c1c82c0141006518901050035407829aa50000c02c00540e840c54090340c0118002d80b42c140e4068198181141084c0c01003444a008840b8509484417640300042210360305c90b0006400c040501c0b82020440d103100d4a81c5c4042d501400421420040c000302052000034400661104007422000209000d00d501040780d00d81c1e44030110f00c0e032280c41940203100091440303200741102d1805c2007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 534662374 1250 534661124 534661147
    0x1030b0306010f030308010e01060c0303110d0e0c1e061b160b070209101202040902030c030604032c01050d09060b0a1710021305010f1e08071b0201050915 68
    0x401c03d901a002044142004205141d000f410721030140c450002d60f80550341c1403010251880710300600060070036654160ba0034950003c0003da400d41c0302504424440310040141e1295180c9c3d01d0682d49204132203880b21000807061032001c08803040c00c05881e01c2d040500ca40320702c0e80b05c81e00c1007088804600072207a180b6280c1010701c00d03800c00b40000314541600c0c0c01c03003401885840345004242e03081401402100b808a2054400030f410050f40c1160089501011840840c0c181000242d4413030b050710075502030108054001910303025060440c80d06a200314080e0071040c5040f000440c0c01c90205100b0084c5400091040e041204454041d11003c520301c0c00381000f0400e08409544513034003504907000c043e60032001c00e002c0203070050015502582804442c02d00c0d03d213004414820760341813010350b100d03260745c150140c0401d410740c1141c0d425155401c040d0110180000304201c801c0000075100500e000c0705c0c0c01246007844e0360070340c06941d100d081110301003d100c000d410341c0c1c5107200d15400a000f08440035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 534663624 1250 534662374 534662383
    0x51309050f0a0b0d0201080a11212d13050f0f07150305010e0a0c02100f021209030c0d08090a0c12110607050a0204090317070e0a0b0f090d0201030b03 66
    0x62208181412103842c100d11444112043e2640c46032003400784080260142c1c1c1e00c1040300e41c005104c51400a000e203e82e1004068907c940b44800c40b441c1026a079400b102590120568490150254540c00300b030031480050f00d1900b0129034244040b0a45008a500c51204405001001d03206a080b101c0280c8405645031620b03d4100090010b5030001c02d0510039003a039540f078900038903030b02d0600380140e5041240150000d03100810007540c0640e43e51080c0e14241c42080140505042118108052191400c02c080039512181d48108c1e054840004203550314000001c03148458008000741240043c101400c655036600a492501d0922071082d00340c0205d00012840b200070320718036802c85004511440d0101c000b0121030521480f0300c500340b0000d404500049141a5040d44c110740c002218481d41ca8155a4980104114440000e01202304011203801c0074201314001812620142c00700c0d075a000d5581316200d05404101c2092051100c2c0c00c1310f00f0100303005c0e004544141804141041d0741c4000c01d241 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 534664874 1250 534663624 534663631
    0x30a02340309080c01050306060708070b0a0605030d0801150c0309150215070c030203120601210b01030506030d05090423091b01021203060d030e030d09060311030702060705130905 79
    0x100006420354100754020108500801440000c0c0c0541640940042c0413404020700c41401005c1c0042c482c0100039556040318000e60340000280d030f05003040174a075401403600d401058045e208050003000000e01035450281205d80c0012510748054a24404850000886030210305220301103101003203000340001c4010729805154018201d803a00c000c04051400e0001d400d810a201403800c0300c102003580481280c00007541c141e040780b50ba07140c407401218240500c03c0d91641320410420800034044107600903d103c0c4809907810312082c0c5030407040588820002c0c860502290042020000506107900700c40c800b01c84002c0c00e0f032100c64089024540f0341e041140c402070b81e500b080751441c9240502208500c8a20300a100a02c5858026a402c1c00d01340f10281129100b401001c8125081501c110071203640c3d840d0103019203940200b40540508491001c0c0034180200b4103159260041c1e03241302d005e6074400e02107507004100c00d4694640c255135941c070171140150f07154074016001c02c0c5400c3c01d0080350701 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 534666124 1250 534664874 534664957
    0x901030f06091e0b04060f0b030405070f03060f0b22110708070309031a01052d04060902090a09020f0a0f050d18020f0909060109050907050a09020a14040b030a02 71
    0x3008140c0b4806104481514504e94840d070b2401c0d2040c003007501003d811805581e00490102e1b6030761100e00384680b410340306901803405407818100100401080381c002c0740745c08011314401e00c0070310056000c00035501c6903210024909403101e80c624210301c0e40d40d00b190f102000103d803c2c0349071114940340c5150301d6020181c00d23008102c1304d000810070007076004510103955904c0b800c095050750410f000282d00403c10a850039042080c4035041d1604c00100c01c4100d41514024002c2003001e17135603040d0350003940085400c0d6226164101c0300003101c040754006c450004048006281ca010342851081d070b260700340d4200d404100a001d0042001000b294840c4903c106e80700004820400610301c104004485a1180107000384a13001c1400b040110004029042d43c0e2072030404181640d5035014030b41350004030b80c401580010ba4640004400403290b004002c010050340d10031204540d40e424650b0701d0300c25889210a00c410800c001103003008164060801c0c0b01d10070001500e0b65000743c01c01450f407071030f1425070702 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 534667374 1250 534666124 534666161
    0x3020a0c0c120209010b070f060b1c1a0a0c0e1e0a0b04080c040e150414030f03090705040b06041208093d02210403050d180b0702060901030f0609 64
    0x394038125000170b00405119200c0b07460100d43e07507070302030b080102d010b0014003180e02c0700340c1d490140d6521180f0b0131428481c161504200c1420f0b06220001600341c0b0200201d1415800c0410140c061502401d42d51101e1903c40a4440281074203001c01d0841980c08014100c1020f01074905a580d601c99010042070b0007411191990705145940d4205842036100030b200d1032500d0400420030320081280c500700150014484010b6071582451501102d1031500103000d8000003501c0300e0851380c240040c50180c050030b02141e1125803914248011074000b54882544103000b030004214003100d45140c0c1c00c10b144584015401c0c00030302c10125a15541d454a000180c0d0b01840e00c464250304c021610000c40000b60700d102c1d800398070b00203000e5210080d840d403000462100b1a1089010146141294015540b0104a0350382034100b07440100070014860072480f550780401c200041d1071a0640035900e49940061066140981150040d001440c2c440000328200c1d0321440700103541d0b40c1510270b80500c51400907245 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 534668624 1250 534667374 534667409
    0xc040609060203120402120703080310031a0c0f0a11030a0c021c0b0711240708090607022a09010e0601090e0c070b04020d06051302150a020d03020a0c0c 67
    0x140029440e07030001e00c00c55009002d20000c07403480e00a402e03040358050f00c10f43c9544040a0106040405a42010308101d070000248408505860000ea00300c0340034001c0a2820304190080100c2d03041c041d1a240c42d000000c0c041c2403000302c0d2800080190403d641000310111030500200e07801d5030088610707070700455940d1442c41e05500b05000030303041c00310320801240340a0010799a03540c807070780c005030901082104910500540034401c104442c40c0c5000e403780c03142c411111504e00c3c04440c404540340e20000c1c0840d4045100f080d000500c0714080e03200b0b5005000345224040860405407003c1038603860304d040218881650b9203840e62071a0181c0400c0005900a2800c603001401480c002da10000c51194110100103242201906617140c40f81d2002050b14903403518000240100c02050707001d0b00702ca02c0d00043c0085d0702880307010300882c01c4c400d40c1c0120b00c2c0c2c000e58075441b0640c000c410000016810803160b92101c0d034401d0380180512072040c00c003000c00740e80b107403200700020842c1c0d04140d80040002c41d00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 534669874 1250 534668624 534668627
    0x5010f050a02070c060e0103020f0403120215150d210e03060117070e0601051b010519051302011404080f010f0f020403080a0c080720040b0406150809150c0406 70
    0x42680c000344030740d01945403080075039820f0220151403180504010301c44445500703907817080d0111480030121074400ca8403180c403801e0100e20403143c00900b801602c02c2444490116440c60325946c031511034511145000e00c04001841114048036108030382881508403081809451214800c003a03990f03030b540c1e01c9800071109060503d0a14180c01820044070b002403909414040020f1800c2038540800b01100143c49160040c4da06001d102001d124020f9100441ea045460541c0300754030a5050380030b0f120a00d80307003507101422180140c0c1e12480020a041105000d940110705514800b0700d0791200d90b00c3c0541d104070303032410150000300000059454100000089000340200c40e07410001800461800b490756841400922400c810903007072102000961060081c80b0382a40d1200d50010390715080c4040311400c0c0600107020441d0b540c495890701c20700003d1070070b2a01c10071080d030b4400394145140c0c3e100a4019102c100b4000e0500500b4400c880c091841d50340c0c8042c2d1503001c6c5081c03c49403622a0700b000c80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 534671124 1250 534669874 534669881
    0x703030c0f08010f0b0c01060812030901110313141006081b0a062f070b04170d0203031f080d170108010e0a080714061503070504140a150e0405010f 65
    0x903071400b0003400400600c00b1511805500044880d81030380c8980e28900100b0b01401b501041c1d02c1205a0b02903400d03c001400c0b5250700552140b22a00001c00880c00c404140d0841400195807402c08100f10b0074a030000a4000d03000000d548216204841519165000c460141c40140e0803806c40c54002a9244880c080c6e200c2d2048801d500444001c5525818940d000785101107413605401550302000c5042c041007a6111000000c8805000740c0d000319444e120403c0075940980700b030b0344850941100601c8025008154441c158980d1741c0503600e11707200c050802d10034103040404440c60718401c00c40099040820041c0f900303419580d84401c8900745840c1d51110510303030141d001000f01c0e4140b525000b5050000724241031000c0e13104559584450941c01e04900200704410320318014400d0909005e82d0350102c0381c070051060340480c01c0750001d076240c0c0240800d603100d101c00e021a296003103010806c1202203811180c00511450300c04110240c1e191078000710a40700f80e07019078640e55944141e21010002d4007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 534672374 1250 534671124 534671147
    0x319140c0306041109061302030103050601140103090f03080c040905100e060118030816150b0a0902040b090f0d051203100906031109190608030904050109090201050412030e060703030c 81
    0xc0141c1100d103865100c00c0c44d4061035140da00d105444500c0090a0356683c01c041d49502084540e0031500d940e12031a000d07a640600380102c0381c1480304054030b0031355588a03000348604244c2c131034445c0300d100780320b0356080d02c03070103c00385c1022a440700c107000106807400d00e407144034840c1610701c2074170f4540c0340340c6504840e0450004d17201504001c01044600000404013090303008a80c0e0003d0a50303600e450388401d90401920080c80146609180e50600ca01025140c0028a100000301d464840711691011190100c3c4968403a0444103034050000340d10742e04d8280149141881c0250030320014007100c7d03454070708140310800e440c03003d108040180090034101249c40d1004e054207640c10440d540c21030b00c40c01b540003280c0e4220b0f4407940c94140000c0f2103101c0c0d603059054210600c041400140e03164810513480348c128000841c00b66140a00006160006004000d01a6010786a0a18113800c0100c8505a90400744065040c02000004c04000b030300d80170010303d040d41c0207a400080f0303000020070003000c003070280 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 534673624 1250 534672374 534672379
    0x30403020901050a0f03030806040b0a080c0306070f0210050a0908030c0403031d011e030b10050a020f070f03080f09030d0c1a06060a030207020f1801060801080105040c0608060319140c 81
    0x1c0205000117016201c00d8810769803d03003000c410540d01e80300000c000e0080d030203240d9002800d106000590100019600c0c00c072910403006e03504583d86080046402c2880c032610240103174068260100c4910081d132149811800c1e119021510800d0740e03e0b000c506500507a4801880440000c4c10014981e1000d00223180801c1d581000c90312909050008103c4034004250b03000310f4110341e00ec044520702982c0a80e01076000501a01c4221800c51b801401c82d80044c04808094000c4501e0b014841d00b000c24040300b62908001c0c0c1d00000c80c110b4485204e590005140902d526030300b0131401070740d590204003000d590b044d1079a44d441c02100d98030780078480005a0300c1d518091061002800403da5581083e10581401450016280c0e003143c00010080d01404c3c00054220304040440e50201c81c11090080c1610000c1c0c80b15001c50740d803440c8131400c83d00d040f2406008041020303c14082c4038884c00c2c0440d00103030700800712001ca0b241e0a0481402103980c0d10102c070074004804c2d0346170380400180014601071004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 534674874 1250 534673624 534673639
    0x110d1b080a02092409070305090f01020301030b0c0a180b04090608010e0a021905062113030503010b070303020d0e01090c050a061722050c01140403200616030203040302090105 77
    0x80d80441c20045002d015214010440840070180c000c480100140411000b4003000450806c0940500280020340b18546540a4050541c40a4105001310f9048940c40b07404070360395585881c2c10003425004200d82c4002c1244003110719162030341c0f001e4800081c00c40703e207140303541d9458a182041152907503030020328242d040030352050808801042d000303800341c3c058440201400440402a058441e5074018542c007001c00700c0d9a041404408200241d00d480c0d140c5582041d031150680b00510035107040d80140000c5041005105c107555000250510a00c681030140c10800426440341c01d40d001003034200c02c180e540f501c5403824440b41802c4080140406d0f0380039480982403040007001885980f5066010300341c403901140c9840e00d42c04003141130b00003a608a035031640091400035181c0341400320090000301d4900c4c4052110081e030702140c08480c1c0c0088036188030602800351031045028661a60307488582071201c611051568500c5403541c5200354041c541d40c0c1e040d4410440c18a9040c0c2080340100c05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 534676124 1250 534674874 534674893
    0xf1602060d240b0a0c03020319030603060506031903030b030c040501120201021b0f0423070810090606080708070c0b1e0c0408150c07020d081207020c09070c110d1b08 73
    0xf0303444204d0b000b50074149003540b0a9441800c082c0d245215130030b120001e0b0600da2104210b0700d0360640c803480c15280b251806010a803120380402d070b91080e082201400c08104110780c000064001da010381c00440f0f0203026540e43c6201400054106c0781c00340e10003117154001440d250304640c4d0500545102840107102c807641270302d409000c1451101310301f4a080c0117a549613291162101551303d000c0a0344a00012086030f40303001c0034000c00110007aa120004002440f8011424490502903801991080d956441103592101d0f4116007480018080c407083c09501c98100d4007140b45d900e0918071920883d401e403145100080384246846400600b0000281400d000c14001400085441012244049080320b4a621110704003040b0b8410705000030341c041522aa4031b0104024000a82408040c1d1802034130382d07951300a410381e152050016403a502c84001d04c00501210300520b0000d0720b0502030390380e00000101c07c5010030300d9821410000d032440c426040144103401071021040c4054200003018040700079 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 534677374 1250 534676124 534676139
    0x603060b0d0c050f031203010b04060f091208030c0c0709050711010e07030f080408060709030b130f080a140720031908160218010f12080f1602060d24 66
    0x20384030b002d4284074000940050303a13142e50421290062100301b02c0d0fa242d49503969414030520342d100e8401c500c046080186040c418a008030074070400c5a01202100000c58010340e69100a580024103403108207100f4403080315002e004100b804050500c1c0400000c0c9401d00c13041c0070b404030200e4905410907a06120340790040307210116800044a9000300b00700011001890a0364580c0a160402409813050000304042e5503803080007601201d001d52040200354039850450102e00c0e190389000f030982c445007103945001850100041c4162091483c00840480885034119400c0c0e0140d4405d403002091541001032010031891000b510441c00c41c0141084144a00901c0c8a03200d09130028040400104100854034601c070b0242d610980d00800c2a0700030000094144600e00081c010ba601c00d00c981003011400040c015196001650091078550610019915400a90384280040520100a8000c550058440c04090184842142800f084582c11080303040540d0303da800d000c4040018042c02040020b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 534678624 1250 534677374 534677393
    0x14010c08070c060311090f10020f1c03060902030c1e0f0a03090203120a02250b0c030a09090608120f0706060305060415270c030206190e0f0a06080406060302040f0603060b0d 76
    0x70701c03003030f2488084d0352325100080e0b0800b60b901040188a0182c146172908482802c403154290350710a071001c1005984034080e04c0124001140e0a841c00303c0104091007105004000c903d5010740a8403681d4030745210281d40d0b820581081c2c41d8140881e884012240840c9010700036152440000207400342002c4250100a649040c1f500c001490f660017031900c500c003841e082c02540c01030711007040f0142d650030703c0030506aa41e520a060041c000f500c010070104011965000c1d04040b078107000000d0400c041c07500241c0343d495012480765407518900f0000748000407514042c40300254041d90103040e1501d450f0031b05681c0f100c042c112401b1003d00d821a80001000c001c010148403107428011801d032028180b40c103480c80c40e801e80019610950200e010f5410f03040042d00c006103540c45a603044082081102801100c6044003c1190b201c0c0c10b074642440b205204044107a030160003068003203030980e44d98020404440e458140140401e840320410301c280440c40c0500120002c0580362149084800e03258070128 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 534679874 1250 534678624 534678649
    0x6150e06030f040f0602040b040303050d0f060f051908010509010b0102060a060e010e0628090e16090c180906050109050f0915042c120a0914010c08070c06031109 71
    0x13002c502490b00a10003558151005130020212156070703183c482c14050415007004407140c5008c0d041440802d00030400b4001e02085804410341501150700305020061580403c3c070352490003101d0301d40700040000090007664001c030795040001a0281d9080c0c002400d04000400b0b000b0401c0c2848030402064180944180c11280744e04040790130707a02c2d44c5001030f16401c0d80000720507840b20505d6500b640c00034000881d070203d41241d142000505c1020590b6034407180d00c46001446d25801500030402c80403180c100594540042c80d00e05080740c43d00079001450750003038004e0400181c1c3d804080c0020350700715410708050101200e040007054042c000082e0544401000d0492800180c100403415881e0b5800c4001c0b6035200300070390ba580780c40f41d013641d4075004000f010502c05442110070a100b02031002048403281103255891100c1c450410043c54038600107815124104410355040d880400e10601c064421141f1400d805c11540e071401c0e20040550712428524100b22030200801002a0b48000c904c011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 534681124 1250 534679874 534679883
    0xf0606040906180b06040b180f040609170a0e0a05061b011e090512160b09070f060302030a110a021b0609030f06090f07060801060503091006150e06030f04 68
    0x4001c034a515042e00a0800042459074003191a510f41d02009020b0304494454207007a0f400f00041d51907001003107405041c03505001e0305540c01f44045070307185002d12009a4000e004e8640855904e43d541c0d1144200d040c000d120b4010b890021451130000c5522440d500400441100d00610407400c00c03000605903c9181d024014087c0303421403180030134500390012003a155070301c0072107045080ca10300350070083d02200340c0442d0a8081d0001c2090000c12080540708000a42c45003183c0201c00c0350394401050301c004e021003200344150040041c4035120303400d00101403c20380c0c0d80941c817810074a00c40c80035100e040e203800301003400c248071854030940d00041408020300035100042d01c0d507541d4070104040d80f103800380742601070240307040203841c4e10400502d46004070049801c850b604082c4449040e1948554058a40004c02060040000310310a0001d0741d000f420344c1d13081c1d8080200c1e4500c400202c40865012038031074021060981c170b45a030803e40040622106881d55495803900120309501c01000600040c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 534682374 1250 534681124 534681131
    0x121e030e090a0f05070e0310091e1a1501030b310b030106080a02100c0222020c010501081b0a0315020c03040801050c0421030e040e0a21110f060604 65
    0x1007903502c950704150402402050108601e0a10314002022054290740941c0039100780f0111b54100d28551142441c0070340c20005038201d4035101e004080400001000a8400034074040a124070800b03000500c81c002c80310180380042001d801000501035031420001e4031300c1110700c0d002000d1203002c1c001e140c0c6042d01854000c2c0403004081c68003000204506100780390998a0070354089581040010b804585078000c60350100e0450140b101214040704080b402500a03c00380c0b940340092803580d20141300944100c501500742500d0314445802c6441c244d014052a601c4501440c2c0c2482e0401c03d8001802c4054698107909c40c210b031a8905d0080280c0035566070254002a003041e544824410340e8040d10341d000082c803140c18910f064540c9500140200101c9180b058440104000301101c00302496a058494421140058003000005e0424098150280c01501450000501060a00d40102003011010003001e412860013710b034054018603e546a88609400904503d00095aa9103e5811100407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 534683624 1250 534682374 534682381
    0x60105030a110c070f0e010f09090305160b041707031b031b0602030a0b0f030a020904020a12150f06031a09120408030a02101a131104121e030e09 64
    0x240200300c2c844000242140102e1609031808012641c03000f10780101c1c0000268075150500d13080c0c200c4d4203215402a01078400c60802040c501c5422030a1000c1c002d0601d14101074182c5110150003c1041d4120340040c0c03160100010802c0841e00d040b403d1062081182c00d0481907900600320301506407845030650411440c4804140c8a120903c0c20700c03804002c0d1024a02152820b10045d400a541020350740707050020100860610038842c0d03440c00001001814044000c3c2c007071023030003000644180e030010104403012441200707150305402380c10721598030349000111150110381281c50310024001024101102000840c01c0e11152150b000018140300b40c1036118800d6185c40e00140d0340f401c544c079407000700c1c0008403940040042c9c280b0300c02d15002d80300c20005030601d010840d0000c01030641504a118107609083c10301300d0380c48403440d01240c80010428542101c581203504203070f03c8945081204510042009049241400a4051882d90085140540d0340183c20741c80100d8985004a0582000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 534684874 1250 534683624 534683641
    0x1403061c060905030c060702061510031e020c0f070b03041a09100929010803180316090b01110313030b090a12050408160f06030c02030c06010608180c030606010503 72
    0x810780d00e030f0b40441142e13502c1040b00e042c02c2d00c0e000c044034020054006d1000044031000084003a000c0044010025960000e85503800d80050181c3c0c24000a01c000140140d00001110f10050001d2207210b0000c0401e034864504084c908181a004940c43d06030500070703c0300048507910701c80031004080711000256602d0110b000e250120b0312041492503801c00100001303003c90b40c04225120b88c07280c82d1942075186481071a5400381c5c03081c410700480f0f900c2040a9000c0b910382024044042c40001d040d03c040802282c41100903400c01d400c43c1441a40c0c4902420743c1d0740e00a1030710141c1c0c040c0031010f94140343c240400c0c40c2d400001c0d031001602100340800010300106080c804444800e62081072a42a002c80e584010020b0300b1a0249071240c0c03240089482406001924400480b80d40301492010349017040c05c114040c241e10b07c03007601544401e110042c811003090001d030303011700810341c1d40c01018a8060745042d44207000e004400e45942000d009094561808508554050070a08185541c2d407600c0b000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 534686124 1250 534684874 534684881
    0x22080f1006361e0501050d0309060e010e03010905010e01051303090506090d02061611060c07050616140a050c0a08030d050c09040c0518091603090c0b07080a1403061c06 74
    0x24900c40b64038040440c41c40c2c2d82c01240703410492100d40b104000584e2500e0911070300241c4020041c010a9141c8001c000d11881009084407120042c50800314104481e00840d0035503030004002c40301a51168150842e04009108007544241d00d0030241c4005601d944024010003104d010300303800f540c00055504526100e4100d11a082e55001d020569952301140b0f02440402100004072031042030800040d406240c03030401d40c0d060307455000140130004d14000030842c3da81d00501c80e8100c006486031106e800b1a036030034022a00c00c40580e010301010449450264207100205031520b11548400100f4000204000300387c919109401e08005070300e03160182d81c01201e01419210550290600804911069010018090740c03101841c109803009162000c102080c001192402070800101900f840f50501c40e421102d00207006640c2e0247c402e4881002d04156440307a041600c242c1030004403010300e180c2c090488004150480011815420050b000a01c2d402d0601c507000210000001c010082c00119407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 534687374 1250 534686124 534686219
    0x602090a0b040803031512100b21210712031e060f290a180509041101080f0f0109090204020904050f060306070309050a020622080f1006 60
    0x40c402d0321030383e03540342c2240d5030b9004485032603520185075401492800e0a10344854200203240c040c04c00c2c0d0b21000d91420003010354000310380d407115400c4c2c442e4080148616072344054204040250000400c1c41507100d43c070b485206501c00e51028104080c40c082400015001205090b61902003243c1c020711031441d15022030740408043c558a048400201e20341d41c03500c0301c0206c401e0400461a0f4560707018082c918401c16101961941c10104005600e5a219040c981c01c0e0240c08c641d41c003406501c41c00480d844040403141156001010080b4507281d40e045030151354440311140c5504400c0c60410801a01140103104104069403208440d504650340c030b0f01030b101809005041002680342c14810428440401d40c0d11502070b0090b4408649003d1083c0600492660000010200740d0425070a01105d07071b201c6040001a10401051f60301e078a44040094001401000b0091400b1203403400b0050070402010150010f0600d00641003100041000205001c2c02045140150580001410400c0c805000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 534688624 1250 534687374 534687389
    0x1504050307023304080c0609061b0304090f0c020d0807090801050907090b010503100501050702120105040f051c0801150302040503030316030b1e040e010605181605090604030602090a 80
    0x142080f450920070310503d0300b0380c41441a000c003e001e24840e4124000c1c8242e005044998200720800e0a071420004000d091562014210524020b4051000b0700101c840c010081030a40000504000e42062409142c010004a410030400c1c1c605418000c4e503105200c810800602481c8030000f4055400b94000500424000000703201a04d40205055100c4109000d200010362803c0d91000b055446502682c0c81003c2012002481a040c03d00641e050f800100080f80e1011801c41c1003202c80c0d00a0203480e0140d84100c125500d10b909500c0c150f07041511481e02520b40c0b021511100741c085a00041407411600c001006421036241c0c2c1200310080d00c07441c0c00c6150107100020610580804850302c000003942c1035903042241ca2030220400140622900a1019014009054502d545000e41c03001c2e00b000c4084000154195884001c68045c100d0365105400701e5200314208000480d041c04021200202d900e13109240c16400300015449014030f00025000e66800305580da13003500c1c0d18006101a03c41c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 534689874 1250 534688624 534688639
    0x2100e100f150e0405071508010b0705070b04081f0219140c01240e01050915030f100f060503060609160e031c031a030c0103020f070c0f06020f0d02150405030702 71
    0x7268410f60b040b500584003111a4070806000240704410b1001d1007803020420755a4500d40c1e403900520980c039402200054410b40a0640c0c000352150740c15004000070038144000d04607a003001100d0b00d080311003481140c215140100544592020743c0d880c0c0314400c61130340c103141408042100c00c1003628041d01295403001d61900612203800860314090040b60383c0c100580ba14800d446012144040d40700780300b0a60804002004100944007102044071107140c017504503050040200511841c080641440c08400c0d0390700c482031406000f982c000c07003010303000c00d4009204504094000c12031f02d51006054a21109602c4c00e048841c500c00c40c14104040b81c001d04403580c8014803003082c070b1210310034079940010070f160200d071106031200108184000c107401805803210103441c1d401940654415040794210060410107000000c082e12080000b4254250070000382e031b82006406442c040e0f0108061459505c030810010340b4560025000d00040c4960003ea10691150300c0c019185000e0042c009511610 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 534691124 1250 534689874 534689879
    0x2120f0903030f0c160303140c01020c060708160e0a060813141b0d0b0c1323040b0303160219030b16020d090b030c031f1502100e100f15 60
    0x1c3c41000d080d134004041c00760f07036450303401079102d0241c00d0343d0307100081c04299055100e81240c02e0510145c050803404400252410024440580c1801c100b2507124002c00d0501c0b0070701c400307440e100ca1142c518900c44d0405000c80d050f1440042e40320405841140204100d4a000496201c130341d00d254042d140c0d0264911400b240d81f40072041d120155250507403481e010340c1c02840000c3c40c1c0480388206180e0404070b482c40c661a0b03d10702007001d0f40f054800341a0101000d20000707052589800e0120b449100d10710402400305c0100412094a5800d0314091207603005200c000b548580d0b980e26651160f034102c85001c10044c1240c0080c5c81c5508551002e002c3d80072500800150003001c605003400307280203500f502c403200c0c805135050f51003103058051902c44900500004030746289078002541c01a40b20803100300302808401d65410782c0d2000d50055078172003051410141010341c0401084c0d5000c0c1c01000d003480600e80880005980c2c44201031a820007079180c0d010361400d10f4180c0c0c0007410aa0102d022240c00d240c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 534692374 1250 534691124 534691147
    0x15030603080f12161707110f0c0909062503060312110c06040602030729090709060e0105100305060411211506072d0c060e0f0102120f090303 62
    0x1005036903440f40c1c032100d071400180744001882c81e5004103c01910303101d4209080f000c8004800b00c1c014200420b00003406c2c40130843c2a810003195000f07404820003017501c603041006100c65681d01600c00f040075408001841950400c3c40040c00da1100030742075003a1031076046181100075100780e81c005041029495201e03100c00d41d201c0b940c0d003880c211620454a14480c134000b804079a115610031500180c00500410b8009194810300b2410004d410030304030450842c504002ca80f001095559420941c407074041081480001e020341d034024820035602d20300540c54000424014001001c8040400d40d440002a2607a43c860744801c51012413110b01c51349036000e83d50b40f4a50942c8006046101150f51000100f01c141c8215000d030840f800580f00500b0090103a039504401110000c0ca80c055030840724100c14124015400d408017a40520355180c00e25107006409030103101e80124450268900c401c9403002a42c0000d210110049120342c507035511800c4075100c500a0107546100c82d4180000900d801019 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 534693624 1250 534692374 534692377
    0x30204061d010e120f010203010b0a090e010305060406112b0f050402060d0c051e090a0b03040b010308031302130504050105070801140603041a090f0f03040b0415030603080f 76
    0x15405a150019441200100e1401100e0200080d42c00500d0f96009010340341068584000c04030700440440300c40c604c49003161402d9800c2600007081d03100000c14004611380c2e0004c420b0000b407182c4405e690241d415600c07200e8854038018805010303030742c0b00d040c8420020100011581a00c0c0c02c1c120f40a072116030a049240e95a012a0030701c84664241003540030390312010321682e40507a074000d0015140c03c42d07840202014100340b00707540c002c4c44401d000c86008164080d03a41081c06648134811035948960314100005c5910580150200791418002c020000e07400c3e0018605582d000200c16440b0b0b07580310500a041041c0400c0250010545081c9402003020f0790040c034040d40c4200024016039440380011038080c5400d104864807410440c06420040c1054401160054001c1000d41020f0070041e440080c0c0709400e075131034901680400204840044103020006904e840d8a000d1890140307005520f9040307001d1401605690b0001450000c0818002d9100d440210f40c010040707600d41100440007541da = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 534694874 1250 534693624 534693629
    0x22d01030c21150b031005040501090207020f010c051608060f0114030d08040204020909040506190b0607060b03032802060a150b181518040209010c030c21030204 71
    0x82401c2a007441291030007480407012070b0030781c0e1088100c2c0b041207203107074409010024903840e42c4524a05001c01c00c0c81005000754410300010b40c1100c18245010300744000c0b40d030140c0c0440c00e524412702c072101c0103039207a045181e20040246404644054541055400c06c0c0c2e0742c400811440101510006403900042080303071140d1034400c0c2141c0c6c0c507aa6009a074900880d002c482030342c16000340c4000719900e0300800c07005410074000f8000500344840312020500001080d542590b03681d000008000821215075040e03141c01e400c90000740003a0401e14003068040c0140c8600418060b1250b1010b039090302c1c100140c0303807101e1070000200e0080d4040d0710141014042001414018020000003441008240c000d0400c2858034a40c0d411116291108910880c0c01407640f110109008407010a07441d96035440c2c0c2442540b40003e1581d0341c04403022200c54446949200a000c2c50051145040e90307a0440c40d044201d40d0103081400c0a12914a00308412040d55142c0e81d404104280d0314444841d03056016105 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 534696124 1250 534694874 534694877
    0x602010c030b0f0114031b03070512090c0105090d02030a0b040606300809012105070914090f0403020f0a030c0201080105011809020f04050a03150b120a0807022d01 72
    0x2c415011820300010014800e0b0303140c04600140440761028440900461b07004030382c47d002c6403408042c1c01005c8516481911440d00054011488000310044a00301a030421400001080780e40e04890000c0d20030b004400c1c00c503110b00b0f003550a41d819520280b00701d2a903681e100311224054a05031170018020840c46c000c0c1c00071005030000c118804ac1c0741000ba4a0b250303829540c450400c1c211961540c400e58010785a113410801c1540184000b075051304103034080c019148d48046210f282601d40280401601e51006549441141621165848a070040354000701e803014549204c1e500d0703081c260319010003400e0144041c45001100170625500c41f48008205100360303145042641d891004490051b000300c10001181103502c4100800c4041f42c1c000c00d5110f0719030400d181801e40d1400040c980f181e00303038010349003c1c12070510602803050610802e44c1068084030902e810501000e50160f40350000d120003480000001000c60075951215986080e002e08000d00d54003071880c1e00841c0c42c041200244490 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 534697374 1250 534696124 534696131
    0xb0c0a290f0c030609041e0c03060e010612060509031b06060102150402061207020705060d06090c0c0b0c070606030803010314011d0a021306031202031e211503070602010c03 76
    0x2404000d1010750240103418005889056072a0442009010f81d0080d0003212014103c41c651540d02500c00301c003a6115000d866404546480d504041d029100340075004036003645011000e0050401428001c007201d50041c500040980c0c4070341c0414554810390042188161034400c030300051040000f2000c0c400e003000c0c1d00340c03241c0c5001c100c85809200c20039907000790300c00d0301403001070a41c13044c0c00040e42c2e02011b5071040700c00107a0340e100454410350200001c2c070450782d140c1e901402001036900440ca015006494809030b595956115103a8800c0d014150400c145400220402400700c150010f0000c0d64105001c0c698035603492170000fa103003112454615140d400c2041c504200074804690f21a07190f600009410311016036801c000300049110320340355851342c0d15040030011411072160181c04480980055503105107644102052401481642074000030811140d1420445003001003000680c0220403109a101e4191041c1030800c52100c2d281c141c404c9c1100014125815000b50080c1c2c001c1c2d84040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 534698624 1250 534697374 534697381
    0x11e02180d0804300f03031b030608120a08070818030a0f18030804060e011701170f07180915050c130515090105091906020d0f0201020a02070b0c0a29 66
    0xd02c007a00800c001c03414070740300780e113000020a10344403c00800ca40b0034900010300c035030203045402209000304201400030b6513900003401100d40401c0240e41040d007000d003036400c080b0b82000003004400010042030070400000007007440505000110304960700548103694480400000040c0400c200203030b86c400041c404c40d40915002c0c19202c0410940303800500c014036140c1001011784141d03005001c201e04110b007007000c4208a41107001c1c05806401c400300110040f40742070021501d4540d0b4115054400e41007840c0411001d0340450000307000254968001c031b49501d82e8148100340c802c1c600c00200c502400d107820000c030b1780c0c4190014040491110f0f010b8420b01d445078107004100e18141c00303404444100308100c000560103640070f4140041c0c01405179817048812002c0e846c111025900102c05a44034500449441e504022401103925052000f141015a0440005d5448900d8418115802000203120820380760601c50221115008420201030040440391441c10035004c120f90448c0500b41d0010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 534699874 1250 534698624 534698669
    0xa02160b0702010c17070218071106070806091005090411030d031413020423060906010f0c120302040801020a020601080d03060e0a05090c04090f02040e011e02180d0804 74
    0x1070300d4100b50180c0d5410044480c50352402c2c0c1901809000c0c4603030b424144804d80059580040444041068a004010500300100080c01c1c41d902001c80a0064008604000b90968005c0792a0ba000500300e42c1d804140d102c200c400c03600040c10f03400c01038110000d6801c0105005030101001081e03203050b01150711fa0080e441c0b041b41294582c1d01400403c0e44404013090b80384181d0850044968001840065580601a00c8001e8824546900c10b00c0040a00c1000010320700010b100b64018000e0a0003040700c0224a4010a0b6560000703005010010344601690554880c0c0e0589001d001c666008540d0340d0000440603581c1c00091041c500d03184100c4541003e081e12078043c50080f1603d42001342e0b20380e21810a544090000202a041584a40040f11000d07544501420500318000c081c500040ca0301750060206403009044410b65903030605105800c00e000030703a9403c1500125101c01038640c04413034600140c8545000344250b0102210314507005110044000b0404c84583c006074540c50011002c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 534701124 1250 534699874 534699877
    0xa02010903081f0924030b04050606040501050d0201050c0a02120106050a1a1b03160f031e05030105060c03041203080f0a0c0e04020c15010603062303062a0a02160b 72
    0xf1000b024241aa400c00c10081c46400038050460000c20011128041c890000e21000c200c0c0c1c03041d07441a100794203000c20311000340503080e000202524244110740c104404101c2c09801440e0090401c0303000102151f005a0512012035001c0e4001c1080311100b00300d610b414068041d9006032845900320850010300031908406512034252140243c50404001d882035090114840100405038002000f500b1040013406049901c0c40344910140c0c0e1446201d400e006103000394102c09041038120700c4109807000f82d001802e890440310304030344069036410310307041c1182140142c2e8814000c1c161800d003800c0816030004203507441800700541c44610341c0d0310b4090020546894800c80c0300803803e06544507509003801d40041c200c0805250403100d2074440300c000104800c40c00d034454000240d03180000d101c80180782d0908188501c084c02c0500b140c0300c000c0006511400042d2004501d444951814007465440d41450f00581c100b5600ca1500e0301c1d03243c24040c5d102c10880148030882c600c100408107082c0c21080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 534702374 1250 534701124 534701161
    0x61508010b1c030c050a0c0f14031b0604120b092a0d0201030905100c020111040302010909200703030b01080f13061e0e010608010f02030601120f0209060a0201090308 73
    0x70858626480d41d80c204042e030000b026400d8081242e500c0402d80860350401500000d1441419004002480c010585038501d80e07640040754820011280d03500b01d55000210007044100e03141c00d03170300328080745400140c03a8820365000320b4140c04140d515009000300400740f984500c008109580c2814447d91018038400d0205484e4032864490b6802840c85051548405224a106050000e03260360f481d140c0394070342f048201410301c43c01e0b00c4641400400394280541581c45010410131401c00d4190390010b010442240211669590f807034131410303092000300750303841c01082d20700051990310030070360400034040c4c8015940507000c0b4a23690003040c8484601c003481031040c100c0c5280317440d852201d5a40c5070040c0a258058603d01c0c1000142c087c0800f005219059140410340c00008c0d803280741109050a44036084044850140f06004100450340c0201c590319040b208108000745810060716210000e0041d07850840d0894404148444029015405001c1040c00390311504001e40e038414108810700c0740c00b0f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 534703624 1250 534702374 534702379
    0xe03010f05010e0c09010e041b140c1f020f0c0d1b030519020703020301061d090c0d030c0501090512030105191a090114130f170a0f03020118061508010b 67
    0x104009070700c4c0c0c071022000d40b50031901458841880000c40700020251002ca008400b40e22100c80c90340d00000d50801610940e64028402041c140341024240d03545844004881e012140c61800e0b9402c80c80b0b100c0d030b04940300c44005e404500d440c1c0c059500001d65500368080050301107042002002c030003030b965006880c0d4480d81070f582e903881c1c40c3c10700c4100c10b580b020751140141544a81d03100440180d4080c014400030f40b2051044541000003101d02c180c43e000040c081810640005c0c3e002c89e0715880f244036114007540c0608105001039814580140100440d03070014006004514912201403c0c020044d4100c81c41141c9401d0040c228102c1180c0e503e20a00c91a892110b1010041c1c0400561b4009050907071b0050400c44104601100c0b100181d03130101c980001050362421090008010803149407014201200e4046400000007806594444003098050036007200d80350004201031007500f10140d41760b940b5490081d49515803800101030460500b0a03441c0030101c540c046802c000501c100003800200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 534704874 1250 534703624 534703649
    0x60c09090105060702040b100206070e0d111903122319080618180d0c030207030209270a02031009080306040c020a0b07080f010f031a060105190e03010f0501 69
    0x2080c00f00034450f800725804a8229407503e40351200c40d9100c3c1445803040440c0d40140c111841d14520080101000006662184090386210703400306000401d4038044080549401c280302c5841c00324503005a10590000b0312a40f84510214043ca900405505607550100c8044441007035a5044140500804a6021104800c0b040c1d5603d2244285035241c2c0201000d8441c115001d80c3c404000346001d0120380440307840002100d4400c0c0e8601c20400d02e00d021425150968a24105550007034a56041d444080c2c0701c1d90465010034155a2543c2694180301c0e02c055080c90000e00e6405043d44900d90703080207030303c640103001c1c0d115540d828500801da60a40d114000070f14650f1030004010007044003003035030340851280a00b060001295490030758064242c584400d600c80c6003003c0380703030000881600f00348148402070600300002010807020200303810036100e44500c03d03a03c03280102da0300c0c0212070740c42036028411541d00500980103041c0419843e0142d0080c4940f042d840c0e10b15050703500a01c0f03015901d104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 534706124 1250 534704874 534704879
    0x12050307080a090204061d0613060f09090204020d0501081005010e0601050f0c0c0a030b18030f0a05030a1b050c0c10170a150306020918150d260c060c090901 69
    0x2030b20381c003110041c0c0c4003d000140044e2950741440541d41000b00701c1052484620a0200901d002c0b6200c0c068440313803c8080c8070b0a030400200d51180007607880b03990380594507400ca03401190b03104e80648100c1590003008000940c0e50b0705170031343d5500901961040d03a900c5c00c03002003801c05031842c1c003500c50003060719402c0c43c0c4040d0032013210721036010b40305004450090802200490350741003480d04c010b50284100440c541403100c0e94802c401074402c52030038203902c20009008444440302c00d03a5428107486c00c14a481750b5030b0b401000054501070b22151410660400e40a0481d900710001d00707040c011b01750458200407144001c1c0320000407000807480200b005030105411112461342c11a0f406880d070b0901041c0382d01419081d40843e2002d070821504c50360042000d54890410703c030319000302d580465804000d4100700b68184201124644280c0c00303064440c507080140b08001541c02c0903011010000c00101c0840c0c402c0c4c0100380c00c60348000c4000e000d00b4020170540e4508500341c4550580090407210143d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 534707374 1250 534706124 534706141
    0x1805090601270516020d0207031109061f03020d140f01030b22080d1b093b041403040b030c0d0b0315060103050c07050c04020d0e030c0a1205030708 65
    0x49160403010340c00c022903000c6140c1404207005444c000c0e02d40104e1032101d11810500641400e5107419500210340c4003c50030008502e07414205544190280c0301440b503074951002040450201c2ca420300c00c010f030a40c06002045502da07009004c0340c1c0c070100c810000d41d50a40c1aa070712181c1c0c107840080d01c00c00310600520104507040e008a0b0000e80030102e186468107041014100e007014554250740b40b81e008140314020000c01e00442811444608500a100040e000007600e4030469000e0302c4003082883d201c451840000445038400c00644509040d001d04e204581448003110484040340c3c002240e1148068008000050740e0584450420090841d5114004030078280c0090240421041d141c2081440b2900c0900991410000e1300b0b800900b946420000541a03800181100e40301c0c80c01009840013043e0013145400d03442d6021600940d0301e80c0705004030000f0706000b1341c18101e14040001c003002041e20014151401034030813062904a034000060545182c0004c03684140841d010390001160b24 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 534708624 1250 534707374 534707399
    0x4140f0604080f210406060b04211e06021c0507120209010e090a1d0304060c03030e070504021309060602030f03040605100f060e010e031b0d0f06050f011805090601 72
    0x2040d070140f1550408242030425090001c64811000340c564003402807005110b0180a9000036090914503a450945400c55195541118a903560320903d0310940c0c91040054203035044903044542003502e080c01c403c40c00d250009500030100881650402482405a0241d41c000d4600c51529070322030100782001489200d001e9400070000340c0c100422000800f140e59240700e4840e00411040c03000041c0342650512030000d20014807107940c407551081c0020404a03038080104143e8a42c14540420188444400c052908400d60000350b0f01c1400402c05002c0c449050354090104c413440ba0702842030541d201d8081c0d0f106e1040c1c84009801d05000c000060100340143c1040307800008000007900b10582d1096520701414280e002440003074948028100290780c00b003680320b0b4444045018140190310403440c00030300642610074500445100100c6070910000142401d1840c0d0403c1c800d20052034600440f40c2140c00900031000c5040e0703d940a480000c0f902d114041c850a0102d0090140b13900780380040419 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 534709874 1250 534708624 534708637
    0x706050706020c12180f060a0c030201060905130210030603020a21050f0102090301060b1201030b070c08040305010f0507110709020c1f061a0c1005190203090604140f060408 76
    0x1950302000f1002039540c0030069402806519440d4688502203081001821030404041a204860100581825030342c0c800456005a01a0800143c010b06030715007039001d080181d01400b0040d00c0c01040140d81152850240462407080300c144201c2c281c441419400c075449804082e40242e20604244507142154040040e15888404c581062800a503201890f100148034a40183d94000c14039840d2828240031702005001c0d00c207601c505158010a07408c1a0101c1480003814000444012680c1c0b40e001d0040303072419a422a400c6c80d41c0d240c803400c240d806000c40d806040c038807529102c0029400740c4030302d840740042c24100001c0e180d0b152820170244040d40103210395085d60301504c0521045480c00c12000390f01d01e82240030105156142401614042301c00c151105800c440c2007044030035122001c42c25524504e030100001901d6240c10041031820444140c3d030030035040c030000500070784010010704c480c0700d0303845500007484001510411944988100a10645560010b4041800210000042c092 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 534711124 1250 534709874 534709883
    0xf0813020a1e0f140f0906040e03040b040806011203271205150112050a24020a050306100509010e0411130f03140d1d310e01060807060507 61
    0x2801d51210103424804001ea9181e00c1544010542048102d801c08800d00c000c000d100c4c11a804941c001c40440e55000364200701ca4070512400e00011056900c40d4000c50000003e40201d0b52a581c544131b42510300ea00c0b41c01103801d240b20704000020329081040f03000d0b805580c0340d51046c2503004808100d0b13a0b080040f103001e481c07600402c80041940305051069100c998010300040c42407000d450b000e45150401038200c2400c02e54100d41c220042580010401c28480d0301c02d410850501d11040c005005c58041d6002c420017500008010f8019a40030010714080d13a000c85100301c0803001103105862500c6103170a0140441c4c10140f607440c1520702070340320201c407100700044c851401101b9407520f05001429003203409400c00c8048244107101b0040780309460690b440005041c7c0c4980140702404180e5424100800100105030304080c03512500c5600c0d4046400c0520b400070720080801e00c190403000003880b0883d02e440c1c05011941038005009200407034805101400009043c00d10454195022440646 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 534712230 1106 534711124 534711139
    0xa022805060a020a02090709080c0d020a060f0212040803040e0705070506160c0c0303020105070e0303120705070f17091309020310051801050907050306070f081302 72
    0x40c0c40341101c906440d12070601c0100c0c500401e0000080d0856904000d020f410781d0440d1310842a0750f18041a50840348030102803103849480d540e03029501211800c0204001070040741d06d02600080c600c1690741c0c20104903a0040c660b44560301c003000550000504000d191403540c40f1710303040619440c0003864840c0c203032030380b51303641c0d00162602d00500c881c00701908040d4000c184110f0b0056004130406590f0350b980c2400fa0013414100d40b4000410540710802410789808002ca40c246a240181c88080c2d0b02c1d46001154141c00100341141c20740b080c00e442002060420440d81c01031041900020f0b0341304002814010355441482d800200141403a40351030041c2c2d00860400000c55180c00e000074580e0702c4d24000b9052012112428507503510384010311101c0040426000c003a2a401c0d400c071140350310303a403404551300b2003441d0000c400115010b001c10a04913030905c122810702d00040058 = true := by decide +kernel

theorem cover : BRFrame.Cov 534532374 534712230 := by
  have h0 := BRFrame.cov_init 534532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 534532374 ≤ n) (h2 : n < 534712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
