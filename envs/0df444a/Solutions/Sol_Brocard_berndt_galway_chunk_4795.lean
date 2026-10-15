-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4795
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:45:21.27251+00:00
-- url     : https://prove2.me/submissions/b3937165-06f3-4def-9af7-05ee52fbd737

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 862230215 ≤ n < 862410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 862231465 1250 862230215 862230227
    0xd050c0702120105160e131b0f21021e03010b041703070f021003020717090102011b050301060e0307180902011b1205031f0807050415030b0f13060c 65
    0x59482507030708903542d041d012019030890344182c800c41c409003041c1d181001e100d03101d89401c1080342c1c0f009120310514201100d00c00220b4440071007900c404180e481a8200300c5030000703800d00aa003920300f44128003100d40301c1c1012590210028a91505901090520315880512030b1450524840d03403605959585030400064039800c540304480500b108100c59000403603000c41940c8070705900104011551400d50700b0844070041840100c4105982405144040b0b590f40249001115520390100c2d0f6506e00341c4002425207100c0d04800903548140c21051485581c00011681100c1d807901d015070811901e0400203007401c2c803a40c80391607412075104061070a582581d010410032031003601c07004d04515085020744006542414050144800401c1d0028041d008a0055900400c018584428030211103808081d090030f58020041e1580094230034002424544104800d04a003030806d10581c41c030310303270b18600e1828004010110104141c1c022842e0301c03c40031401d0818960000003800740f02d100910040103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 862232715 1250 862231465 862231477
    0x11103091209060304030e030f010203252c030a06060806070305010e040305030103020910030b0702070f1a090f030106030c090902101b200a030c0306110a020715050d050c 75
    0x1240140072048034140032100440e035101d10302a04640c11980d881d10180d03803c680714007a8a03018051001014002da60a02c001c5204042c9182d5884901040c1c1d900c002000c0c0100b802c91003445140c0000f00001b8240010742d84100c4c6164140001100005000c24100854410024105030806c9804540840003240e4141708039030707e036802c104681e602e250340c007400601510040d01240013000144090300b000c0804580c07180c960700864956a1f92951840d503900002c6a1810042e0400e040a110085507040000020040031800b444101459403510145108a0019501c28502c00c0611130700b40d01c084d0049001035422030200c41c86a551040c41c4409480c500740224442e40007c0c060040300e5024464007032110044800540b20382e45ca541d140d223002000340a0311901d0010b51102c05000d55210100a00030314442d00101c1001843d51a0000c1550307890466081c1d40350080c00102a1980e0018041d001c488110090b100480030007a0b00743c40394854014000002420441000545207241000300b030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 862233965 1250 862232715 862232731
    0x3120d020c0606030c09010902160f050f0c300f1905010c0c080d0b04060506030108030d051e0c0307030608030415230d020d0f0c020a050714090a0507020a05011103 72
    0x4140e40325010581c60312080440291b000824070b00601c20800b00740e011303000040e02d000a10020b141a51204c0030710081c0502c0890b61a480b0151040e200d082c28042880c13000030545004008802c4403c841000308001c1108409103040d5500c0800d031031004008440400344020141c420207440420301d69100004540c0a9400f513090420781e1502074414130b00d8070903e9411144590074185050680005085080206a03100e5101c01002c40c144d550800194000c001d004011035440803040009420f482c0f000300400010150f080010009600b0031002039408021001803583d00d81c0c03000c10070350040c400c642000c031052001003030120358580500180241c1011a4032243e2410b0703107078110000c500885512100b0b03403000600448803440072035000350481514068002c03c4200c400c03400c0300112407075280b140303005900508000050104c2849114098552043d80d2020704400f0070101e05200c2001e49a12051a41c920014002a20074000c200304164828024003c070003c185001a0640050361016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 862235215 1250 862233965 862233973
    0xb0d0216030801050114030903090d0302030c1501090b0604030f0b090709090309030204111305010f030f140a1103221e1203051303020a0209070504170d031d0a0b0603120d020c 77
    0x203130311b180c9240c007500c0c41002448002d510b0086614288120400c901c0c000720f0a41c0310a00c03001d002d0040030304c214005031582c0e44411003139604d030952000540d6500080d16026040402c01800410b84842003420b5180c5c00041d080314030340702c01139003d107400700590104d403820b80340807421000c02d54840340707040849000302c401340220328080950084900c00c2000f00790843c1c80c01c40c000c01844d400351506841d80301d040c1c140068024964440e0400351f52001f09031400307000c1c1c000e040040c240450703c58803ca01c0210181a81940380910444003038245000c80b0300f000101d400f034100204070740c034089842007444d003401c00b0803410103610b4042241150b61001c000428100000a008204411012050640c140e0b00030250b0b40c0c8103809210b0100c802800150070008104808180d00b4260454130180490200c014000c1c03508200c4000c1c01c4450f466600c468070118190808030141000840e10060368100c0d401d141281c0354075000900d000114500d2140d041c001042c0c00c0c03401040741d4040c0c9540c0403550155 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 862236465 1250 862235215 862235237
    0xb04030203040302040b04230901111305120105060904140a0f1b06030e120d0b041e0f06060e090a0b04050a062904171213150801050a0b0d02160308010501 68
    0x81600d003240002113089400921070301000c080048d0090300854080c0c00045d00c141c0c0941248a5684129008110344841c4038081105042444c090406405540b000b006035040180004000c2d2078080d00142c000b181a15000399143c0d024072005000551025050f4600c00309481c0c440e1640041c203100b81800003101070005601e81c028021300003000140c001070001d1013070424a406643c4c00100241e90110794409158525885501c0703018660300c4c28103c20300c038075021031401c1801d03210608040a04142458400c00011390480001c20300044110b8280c201a038802c000103005090b90400540d1040c1050184410b107040e982c810303000c0e60340e1010b0842003c51070061400301c80d00c3d000c81c2003041c5441040b00304070300380c0c03543c442400250b510003e07507001d041c502c1100c0a482d005100c0c10742c0e040e4021141040601c4843d559110803c20b98280082503600d403200084407000b8900c00d011440d0f4001a4500f00c1071400c2c0d04803040f2040d00e19006008040a080c0240525400d00599012805120f80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 862237715 1250 862236465 862236469
    0x3080106120b010206060415051c050616050403121101092405010e150102161e052d04020d0e060f071b1b0e0405060702060114090408070c030b04030203040302040b 72
    0x20144203050613001032440b52207000521000304003d184400d14103105a0300400d5030b69920681001d14081c8010515a51605082c0700e428000e000d07140c1d40d481c03414a070441c0192a00b00e020385084030380001100340851540071061304c402031700c2001c01d891035192901c000100020344014001c1007441c0d92101d9a55050302000c64105c810038020b4001050340200001e50b414041c00c007850034141c3c184140c1d00725149a8540d064803c841c4e030000c15010031040400c1c3d24003200b11000d44001c0008a54078000f10146008405003014814600c43c003456086101404c02d440300c0d0115000c03141d41c000100b0001e4003038421541c4480003a2203940d420b801c1e03030000c116040d100d2415103c02403000c7d240c5100c038820f02d64928800700c00341d161241e07074000701540020390b407090304220714400c50003400030b40001d14042d0301c001e08042050b00002441809100a41b2068440c000b072643e00ca81d0018586a8820350307810518201021580014104101c06003000100f650200103807003201c4c401e450901080340b003041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 862238965 1250 862237715 862237721
    0x60f08030c070e06042703030f050c0d09050c15070510060f12020a12120201060b0a0c1e020402211e04020418080a0e0a080102030c12040c0905040308010612 69
    0x140ea401c00703074808441444005a0b10004640004c4010300c0080e0007908100500d082d824400c411103000e90750204a8402d01d6014000d403400e164240314200189d01d0305448440d0140500081c2e95003032540c64401000b00801040b2010b944000244003c40c80e0040c3d00820045900954080320b0301e001d056540c4c0101042400380c4c000707880007078400c1c052030381c00c10009410441445c10181d0380200c11401c0083c4944043c202c884a00e805040310b2890810b1a06003e425203001d07a1220f00d41c0681003000762003050744504000007a0764460b554012820210f100d545142c1d0801501a5200c0d1000076800044a4500c1d285096500c070010141100c0e5129201054018040e41000504c2030b5050001401450580e200b11001800c02c1c03c00c1208050540303680002c0e4211111040c040f0b500801584020302d072028003c0300814260009503d90320f041d0b80520060b005582c0c20204081819004c1000c00500c401e24002500011604121030310f810700b4002d10020081c46030001065039401e0745207181c503883c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 862240215 1250 862238965 862238977
    0x126030a080c0f090d06020403021008010308030c07030212030c130e01150e0d0c0b030a0b031b0f0307080f150603011503030f1b0f060506090405060106140f0a0201060f0803 76
    0x24658905603594030b80c900c00150b100d50004990b6503001c104080c15552400c0342001164014030005844900f141b06014034140b04803000c20a1100e5180100000b030a01400c0301e5218541441d9552101c00e603180a03032800c1004854280d4070036012042044014448001c0c1441c1e00c8501d1203401c02655130101a04480e0003030040c20f00401c0d0055004101502441a20703c9810000e81500417100341500c0e03c48405055801612800c040001407100401c041d010302c4080d4034045018100141505282d1f06005400701c1005006a04504105500359000d105a40040066405581844d080070f080681c60b0603109601c8030303520464001143e050304051091100c0d10202c030041418542c107545060740d0425140702c2c007504000c60a01c01041c09e82c54502e40ca103195125499880b05007003985404015103100801c4c641c080e608030801c12011a80c00903141d811180e10b8200740c00003220035103000c000f5200d0941620322003200000c0140d100e5505511083c11200da007451180700b2900d40104a0302d0744620 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 862241465 1250 862240215 862240217
    0x51e090a15081b0a060f09030201051c050405010903032304060902040207141c050702031506030316030e1804080313030509121b0103050c0a050904021b1e0106030f1212050126030a 79
    0x501f0007400154024030003010000340444000c66104403007410314050324070441d400ca5482c0d446021031810580c05004082c0d40700903400310316078400032032600d40304a4003004001518003501c9175200300130342d11668104d48555420003506002900c5812000359681c2c612171036212800218100e021846206000b6a080103600030050400031402d80001800010040d02d143e03403600040105020200fa01c603143c12070340c1d11a482c0e945002c0da41c08100100820101007520100d8101c500708000034112100320f1340d02c009040101190223046040032a80c50288203c120b401c4140c1e4443c50028901c0043c41d40208902116136810221603c0c0c01103054034000d544440c660f001c02d01c0040e06d114080c101511901d40e0191005080c51050180c80781d18180396107807100795411502035440002111a546400d2015400c02407084c00d103184c1c0d80a942980f0404040c0c280074500c0c00f8000f90901c40c940c5044400d01a0b841801656100c00920310700003074000c8200140c1202c05031800d14160040291103500440b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 862242715 1250 862241465 862241477
    0x13030521070308250309060516091208070b130203011b0915020a0501022a2103042108070e01020a020d0b180f07051e090a15081b0a060f 60
    0x181c2e410743c0e42c58005800d0f51448460100380c2c000d0b810002a07001207603d02e0743d070042010001070074440c00b2500090600c000881c03210078850001a0045400000c0b6640200c403581e84c0e140c1e030700b862203150003a800020a2042e002080c0221210128107151503180210000c0005030b0001d090075900c40030307021229020550001040098203140460150440d1841c016036255820070f54855007241c0c4040811074603484030003610b05400c0c0c20072090010903654400148034402c00c002101c01c4503880f01082d0030204400000280400c030190540c1203014001041018031641107210150040c18101c410500060800c4d60314602580300251146555801070200035028450b91915401201c3c002c1620000442d5002c0800c0000d40070086c0000400c07030840503054540c100300411150409034002240c1106002d6140041a03441001c15500100c04203c0041c80d1907115080e00602d040d190700043c150300590041c24003403d9075075190b0503034000c11030b400c0c108151244000e07102034610300d4411000400b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 862243965 1250 862242715 862242727
    0x60803031b0c0a0803090303070801080a0f060f1d0a02030c0114040e1f080c0307090221150d0b012108030c2d0705010c0e0f04180813030521 62
    0x2014801440900808419550f40e1078680d00d402825134000d40b25010164000400c00c001141c2c0000c81e2409001e250b03010b400350440e661501120031400e0310010302a140c0c0c9074801410f003c0700303610615490010041d40e00c404545249110786070507540c5000d07070090140c1000c00c02158491100c908410311250b0034203040504011308202e2030040100716442800b0b0315003d000d403000c83c1c2400000100100f00042151581e684181418030007254402c10449005000300c0c005e001e80c2d690019209007816098800079079070007601c2c0103c8411000c100b50018602d603030320b5051000d2000120b0681d507442c800c4601e41c1c0206c0300010300d9a0b01c500b201402d04c100520110308003030300d03090003420351040c1c94104602a0b00c500c4c0000360070903400c0c112125000c00016410301080400c0c00307508041e041d142446031121040c080464501c142141c0c0061040713603510040d50006240c203001c6804290003000179915444850017260149610380000d6503030f44241d4080c0000d2403600203800c4101c5420460780c0341090 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 862245215 1250 862243965 862244011
    0x303021e0331030804080a03020709090c05010804230c010e0f0123090916080907140f040e03030903130f03030906030b040219180e1510090e10060306080303 69
    0xb04070075500c540b2048400d40000302040c50200a00042d04824001d03080314203083c500607103007a6803907010001d194240351450001c19044080001218002e00b810101d41d611442c000080d210880407900c50302011401c108901c44000a294140c600207894801050038441d04001001000403407460008540514804001d00e40711481d40e150315441841d00e0a00d084940010b01c07088044407003030a0107411048098000b540042500e41140c0d201e0090f000a5007486015500c069200514501403882210354101350b8489030310a404032006142070300e4132420843d40458070f03035105180d4004032401410000c900b0441403500d410880e40cdc0342e01d583c19081e142001c15030241c181c441145078410303424040200880c07800160150301d108140e89940b18524542c880380c3c00c01105400c42821803554070f081084031295901c804101c10011180c2448800d2020411a18100250000300a512040060016001c44501d510b8113440e29600d00b880030383d0702d4143d042c2ea41c1c0811204240c1d6400002c00030074408d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 862246465 1250 862245215 862245277
    0xe1801060e01090b0703210b030a06020c12070c050901051002210c0a030801060305010b1204380f15030c0d020a0b040b0c0601080a03020a080a180303021e03 69
    0x1064040c1001c00d0842d6580d441e402050f0400c0703406030003091606103007c0d600d42d001200745140d40b107220b80400c06403555401082d660942c80078010000c03a030008240b2443c002c2082401d000c506081d1400c1d68886040c946652160764038403405015140080006c240e0b03103000c09601e54280d000c1d0b170061510501c0501c4001b668550645400c4954004012800164006000203929140a51101000f95260110041c05c94105074007041510809100c07100364014400394281d0802d40002417402014000c0d03083c500610880c2c0102d01500c800d042c40741c116803030300b400424402c01550010f0700c3c9030799981c1c800a5110f110215941d41c16003100320ba110b0b151400c1098a40e038107002030721814900e5250301203081980c0c4103400c8400402c501081c40c10205508010040c00345c400080034001e5001076a401070355451800704002c1a0070000300700b85903d40e1080c0d8240e12042801c5c0002e1b480c40d039480c10b000c0e40382d50583c0215071a6070303005070303014186000001c204d40e42118400000c9803003000f441800d200c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 862247715 1250 862246465 862246487
    0x50f10080709120b06240a08061302370e19080601141201020a020606061e0403150b0a0e240a030503040623030612210a0e180106 57
    0x2e2001c0b000d03003c2414440500c3c1c0050080c811340c665420307410814104a007000c1c010800c0d000c030016002c0714504681ca14010b442c525055030405400945900b80090121081007100c40034040c8046003400c405011810f5114600300031441800046040c40d82200103403110041e1071001c40c0c0007101402d007074180320308903184c200c0c0b078034a840c0e2141f6140c1141c9070900d80c0070f91001408900440d511b500e00d10b4205a20030003852880000c42c40d04a1400c0702070b458403401060035209610120740001c4031039046c59002d4074803400e544041d45d21500d0b8988a10301107102281c1c00d07002c0f441d044524005041150600c0191500789812076010740d2800701c104410701d00928001144c4207a060007000980311080b032500034500c518061500d80c1e041c084e000308054007000488441c6446101d2840c074400c130180c1280c1c1c111030169120700308020911602454800c480e40a00a20059181510503801c5208041c210030240d0365991030281c500c0904011074104500d8a80308810041401003214ee07020f00c0180c81 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 862248965 1250 862247715 862247717
    0x6010806130e1608070f050f0310020d020301030c050d050c061804060b070501051f031115030406060306110424170703060e01091a0d0c05041503020901050f100807 72
    0x10441c40040c1031803064803440c82060442d0703403012451640d6400482c0552014003440f0f001004039902e0020f02071070480062040e140621001403c001143d1800d1144501050800303c0c00d66039160011405d02c004c2d803003403105942c0940300680210f860725018170703082c018a42101c0140b107410050070400c10300d580026807644003079000f46c000040d00e4985e0300641d0002c1140e042070541302c00c002c2c18018259840100340c1c504011000c4406900c42c03187c229008c080c0e03a000301c824281c4610b02000300c1d6500407802001d8891080210402081002c59040041964860314003401404402038980d0018040c5025130010b110a0061410110f51502c2044141503064a880320f141c0030151380324802080241c0315000003039214a4140301000b00d80e100c2070f00400306050100449004031200000010b0b441da43c00388140c08000a0341c0900841c50703003000207004010020040c10740d00d100075000c0785002c1c1c402280110041c100019203464103140e054421000507021062281030004101c488150082001c3c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 862250215 1250 862248965 862248979
    0x8030310362c0708010e010903020a15021e0a02010c030b030a0308100f0602030a020c100807050c0708061f0b030408070f0303140f07180501201905060f0c07050606010806 75
    0x1008805007a60303008004000c8000b0b0109103050030780713150135159541d84c030980d545e041c0500c0e200001e03030001e1500f9501e9086000c0005d0003074400e031420b010313101b1001c40d4600f100130701071030108041c0c0700300080c6200c403010f400801513105030340300c01d070182c031181e40200343d042d00061000e6002c82c0c01021711b01c0d03000c40315129240031951a18841010b1110a4008000681c004908101c131144c0400468646c42000c49100244400c50325000305011401006541000fa000c00d90f0a50350340d0400450025282c5034080e5011440d2150181100d0658804da400031001800d60004201c0121012070f40242d402c4203481e03107003c04940300d1500e0200e400c00100c08060340c450014a050858070a40d07401072800c1d402c1160316081c0020001d000c410b40c480042c624038050300e800c000701d80e04280038040c4c2501201071440410910042a170418a40c1e4000701c000412064800301080302c046200c9202e140084801c3ea56915402c1e4000098041c4580080a560182e000304040d0340c0a05001075000c08010480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 862251465 1250 862250215 862250261
    0x91203020a020303030a020310090b03030714010902041a100315140d0b0f0406050603030a08040204181b0f060216062f0a0201080105040207020102100c090803031036 73
    0xf00303141d80d004440082e040c1347e0201c00c3c03015000001c200007004200015042c8507403550200001e1302c0384100303d13004040009508070140c5283e0b003034000403243e83c0c00a04c10001817007543d00c0e49406180340c1d02075a200b0703521900790310042030080c13040d03500306a0410000710b0740b1410110b01011340514240216803100d0500030720f800260120140300d02c90000300300030300345500b400e20b00b24080c1c0b0405440c5d03c1c4641c02c02d20038001d03503c0e403201c078090f4029011a400300c0d1412402d1041243c502c48074030043c10b0005580100b603032403401e8014442c1164030b2040385032401c1d681c07214101c0c4c0343c40348110050011310f2080e5040241ca4032603103101d2420300340a204c0c16004070403c3d0780c00c842c00d050151480c2041e0030603001007096680200000b401060180d03020752503c041540002d4880040c1d400c854000b03541c90708015030b528071034a40b0b0b502070b00148044940c2c90070000c0500c43d0924a0340b05080344454142203445400030702401d03000035408800007807120030803241200b80243c49010300507104d42841d01f01c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 862252715 1250 862251465 862251469
    0xf031b0b0a110c06041211040e0f150108070b040e1906061e0206010f0506160b13060e210c0109060f0605040b0d02060f0c10050f1e0106091203020a02 66
    0x1410800007685422100c0d04a280314181845140c1072030900c190002d0004104501d0a801da00e4605540711181030907d41c045400a4010072840d17800441303a10510700780a800c5c900c0003961145206031200c089000da0b0741c5074030f1183e0318034007802018007140040c0030070015000b50000300e07600702c81d40c268061308058000e52420200c800f40c0e44210001070740c2000c6040101040040d54008400c0c52002d001c80d90b0510040c2100aa800e1040a00480c4005100790038050000703050503207180d200305e00e103100e428a001c1e80c0148040f074040030794000e89403400d5002e0300d910001d2144180c0c1071300e03403400499041007480b209141e040b50b884003080b9525002d0a0340010b500f1310513610703042c01e54100018a1800d080031700007150540c98905000d802030001c6070300969554015180114440300302c0c10350b59055594028140414240e000d0f00b42c0f410f0009003c0c03011818200c65101d80c05054220a90312003451050f910210f00b84900c201261380911f05104c1040c4440494000343c1c040e0044800458803540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 862253965 1250 862252715 862252717
    0x50f090a1e02042c2d030904110c06090a150c111005010f123503152b110a050a0305060106350a0f0c03050711070f031b0b 54
    0x90303481c4050700c1d0402a000000d051920f0b020701c90b580140102100d0f59101100f50420b5104400d4020b428020117800f0b01c011000c02c115209145e010380140451140c40b0a44404c83c0c00200c440da006000d4100020404031000070100700d016003200381003407058281d099071802840e80079154405c0000c4109089032a131000c2110071002e0382d05880014071585004035500300000107421501a41040480000c003242d1a0110506030500340540c0c0c80c10904a208030703041c04000d00740540d1000300c02104100031221600508254010141e4061185004085500750b0a40c0f0550201c1d001c080c004941c0700206505030032009403440c01800030752804e6183c4000608100040c1c1c800c88207544150300611050f980200d1503a0550390380e0300b8020442044030405c2d0900c4050070450a5520903050010b8200b0505400c25180a00c8107a0100031605034450001c01505084503200b01041480e5903040f600940042c1490403224200a00103910f82940d40d02c20350300ca42281103102c10a00300002040e6900404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 862255215 1250 862253965 862253981
    0x1119051302070602160203060603010605180a1e0f0506060301060507060e1002070c05030d050412080c1e101406030312040609120c051005041502030702010914030d050f090a1e0204 79
    0x10424000d617074a10402d454558003d001038081d9051140c1040f032505c95076495241c000351001414801da0b0b5002d1600300a0910291907036446100d0309503031081e50003d0b072140d80380402c2018180b1040d07440ca41401a244400e114020018108006203000f00d41c180e8002001c0d65140d10603a00950700e080e40c2c00059810040c0d05492f045401901000286400c01c06140e094540b403d005007410b15018140c20240c00581001d0000040010500c05400081c400c04c45003c2441922a12510608203c181c0c4c80b4060103800c040740d483e00c0300441c141d00ca070900071071050304020300851a2043c540340c1c1c2e048420020f4822120180c50341038990002d413500d04585080c0405940344020304a050800303a1502e005c140c1000540c6282a0074080815646044c44407520016440580c0e01d441e000d8049004005182000c3d154004143c9030034001c04010005043c006007007007082c84251501a25000c40e080143c0710065594800c240394400961070030300400c4940000c084403560341c0e10035004141620a10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 862256465 1250 862255215 862255237
    0xf0f08040f09291014070c0333020c16080d09120c3303060f0f0b0306040504030c15050105100507030c020603060402040b0c03071119051302070602 65
    0x1281071141e80924840c11280564090f0085000100b0354440c0c00718140d12621075004030055052000c41c0c03800f41407420203021842e04005d0391000c8606001000103041d0000f10740c108095100300c0e10516141c6240f034403440f010903c0110107800c4983c024006d42c0002000c09190141e0301c00c0341e00740280e158151004000b1200600400000000c00074800b00c1c181c0c010500b06009428100d0104150045d11026a15400c4002602110100303c54060510300051408401c03011f15100d200c040d8541c109030104c0e01050702c2001c0c0c1d15244d04960030030302c07820301900b405e064051001503200d190035080107402c039000b814407003c40d183c280c8901100011300c0c2c6c0c041e118a134441c00104214106112210450700c158540242006035540c1c00514003c2c60303141c0130784144404004100b050342d403641158000c00d404503d04da5280020410151290881c0c0401d9800d0070324111542d015040811800c4800343d070040107800c001e410202003141960854040042040e03080c000600081c245200600c02c0c1c40903 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 862257715 1250 862256465 862256489
    0x8091005090f150c1e16050d0e030a021e060906160510020304051506030f011406030606010201090c120501061a0d06050a180509030c070e07081e040f0f0804 69
    0x4803803a02e41030f40c500c000d1003942549801c20141041d00001d4844440346007502e12002d800088440b0f54500a00354400f0341d410980f101c1004000c070005942461502680b070310381182c034440302010b0b00c0f17440d00e0602a420040302c04a04140390740c1d17481542c0c070317800c0001c200e0f6040138000c80104a8a0700195850349171040a51183c0381403190803c2218205019448254514a0190b4441d611810116103400c54094000049a61683d003031150108201c61718000f08860b1200c050748801c081c4043cac1d0094000c0c01200c01140142d4030602920307915642006840074200d26200c03415044c45241d020030380340342d5601d030404036807200029000011a02d1003c002c0303403a0320400c2502d10444407640e100a20445d50340004100b243d03000500c11501c80194400040d0940c2d500c60707001e0852140310060328440c02000710100b0302c20307542c0310307814080e10b0b443e540c0f41c145544100300e050703642214145402041d1508000500000c400c2480c9180341d03407103540849a00000d5075a44013094006030000448048 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 862258965 1250 862257715 862257733
    0x9151806010503160506090109090509160801111b0c03101a0d05100b120a0b010812030105011b150c0203030601030f060f1e0b0f03070e040b100809100509 68
    0x40400c141400b420007180a0710798a4640c1c14070080c1e0980ca4441c2a003e1000452010100e038000c000c00001803114900c00c0c03040d0301d070090380580c481c1c0148a422854007081280440c9601052140c41c041002181c01186009203080a4040b1f50455032003c50380e6104140491034507403030501c881c490030002c0b00c10109840074900385404103011541c0180d8082e004881807840495030018009021180034540020340c0900e010200d662111001242c214600c60030304054100944205190304840300601541e80d0102c2070201000284401e200d941d000070600c41c590031042881522803075210344116503408400382420140fa054400a586110158001108000c82035802d40154400040362040802025040c0703c5d58064890742da0280c4000c100740e036070000b40b41c5400c0d03080c18005041c00e2190540c566916070015007450303004680c5200050410003409001e401d10703000e9040c0110005000b000210111318003107500340b0f001880d00400f4403a02c0042104441144201d50041d8a150050580a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 862260215 1250 862258965 862259011
    0x31403160c0e280c030207020618040501050a03151e2a0c1703090a0f0b0a060b03071e120c020f060f2a2118120a03050915 54
    0x302c401090f246010702d0881c90300718a4514a440012050008000014440401c0404800a002d09a0000c0d004140081c0181e003090468800d14003401d030072034051015a03240c0301030080c0d00c1040d200041c6481c00389560b914500303025802c00a10b02c9483c941d4481a842407640c03c134180e420014161036009411140d2192000d031030384000c400e03840941084400c1c14800e075140000110b450f0700781c102d500c0000c004034411440070300028410719040740e0b400c400c0c41c44a040907258060151341038030a09180010002e001c4040c4810b8a22076006912520981100c1c100700d8a11080c440801c20108440108148140d007605d01c24800001520f0b0300510f100d034110304000385098000f8002c900850741003000c101d04c8094201103030f03a818081c850b0158214680041c50440c078000d100380d280c0054900440e10f0781060344000b240b44a080983c3c0ca52a1000c810000c40d51222116400c40010603410484a040075000f42c100d10381014007081190006040c003c2c0c90001200b00f624030490020382d9142001d125 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 862261465 1250 862260215 862260239
    0x3a060203070f081e1008120c0f12070f03030b09010b0a14091005070c0906170c010f050301060e0604030501020d0504050f0106151d0a140a0f0e01031403160c 69
    0x4402c506151807039080407a2052040c80480c1d0110000721144000075104c526456842c80c0100440c4080326040200d01c101002e954000100c00f4800e4840c1007040308072960001506100074143c0c540c0e03c1e00d40f6000c0d0300c82020380350755440c0c01c0d0706154880328860410f464482e9540d0003016040300942d00c8401180b40142003088185101c82c5540040c482141503690f00e01c105100901c071810210366505241c5009940980c23150301082d050f80c54803500080b40400d85800c0c094801d0400252046030b40d848005480083c2d209001c1000604144010f00000e4020000c480440100400b01c9007400d03582e41d034160a980c0a401c280d11402e44502c10320040001c200850840d02060358001c1c00841d083c514800d8140c141400b034042001000c42c3d601c420000c15a00d1303d690308401030100d0050603210840c1d95109142e80d85118090741081c1c0002400c0800e20b10b9003c26101802890050b80e4613585421050314070030200349020703020070040340c81001071481e541c126807807180b4000201a460200c1203021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 862262715 1250 862261465 862261487
    0x2150307120203100636060e040c120b0102030408012c070e040602030402041b0e031b0a0302130209030d09050a06031b0f090807080109060510053a06020307 69
    0x1c0340c1c01801804401003016502205541c80361a095210f40e160392162280c01100180340c86400030701440c01075460f0012444142954001d40351380c0d10104219080c48200c400410303e01000031541d101456980e0690b801c440050303881481102e080075105d62426003121065204c01e11242c0c20071031003a0000c5980607004545030400c402800001d40381010307440000d54000c100420303280e030010000b001c541e41d681c40440310703d00304004821040d225680281c40542054003803442845040e09000d005544882c0f40400c050300604190030a0341f56501748003081003408003000049400b8403101205071402c004212440020740d49000d0f4480c80c01040c000b62820a400c45070401d41402101015000e5901c104880d143c180d24140c0c2d40c8400034542120302e880150440e08042c050b240c000104078a054200405150180b803040201da100d56404010071f001c0b5201e00d98111054080700520781d0442c0032061150441c400021140000041c4244072a903904c100407650300f507020051000066100340e084007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 862263965 1250 862262715 862262747
    0x3030c030c160f030b041703090d0809010c0c0f02151c0c0903110d0501060905070203211b030702030d020301090e1903051803101103040b07090e010308090d02150307 73
    0x548541040c8491400141c140005003c14030242d0108081050705071240f14100341241e071f00e43e2241001e0300c82d41d4032070300c5d0a2081c100180151011030307403068062281c000040c1154440d40340c2d01c502c980e20004410942541179030310100000d9000b00b120f6941d4014245034103c0c10148000e06030812200084070340202e40d0300b080110440051002816040c0c50340c20f094022220394010b10103501d001805803140f500080340403801e102c14482c0c0f403500040038121128404030301c42079000b60b03402e0303505950000301c0d004824007440e5640c8207060380d40503000715005501481968501844100148282d80c0282c1c401207a0719a40d01ba14592000c0502c0980c1202d01d2503c403030a044207803602c0041c481d01400303080c402e1b05550180d00540c280e804000340c80c1c9041d043d1400b400044081c0d4854882a0000c4805a07000e10805000540040c031480e601d5065600105038502640d00755115502c8a400c0004032503000b005004e10000544d0320700c1c0e403800d803160f03003240482d81e2454203403402000c003030000b001c0740 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 862265215 1250 862263965 862264003
    0x21b030318041e0e07290304060b030f01020d0e1216051014160509010e01050903030d0f0603110a030b0c07020a0506030a200f16020d170a0305060105211503030c030c 73
    0x196540103500c048080c84006c0d0f00010342c507512079050140040159250283e8944100310200841540c190050080e801010004200400303002510a4640d000740c888611625002c1028150403400102c01420a41c0204100c42c1101121300200c001c03144620806042c03041d54008014144c089006041a5174903d072414604000c1e820002808070300c82c04812506000020405481c9514204141c49840e00d2201c0c05102c800d4200c1009001050070b4001660030509040131400c0a08140c1c100324100e0354004108d982e943c0d520f2000e1001d9400000080b40d00008005002846540c4e0101550050207030000018a91003080c0e00c514041c6000d186a140c0d40d1424801c0c0420f0001220a481841c1303504241660181c83c03d1000031855480030b080104001090b004000103007e0400c05442000181c1d02e08001d103845400055a440c06450000030402c120841d40746000b00c1600031050f08442407a00c0f105d903071020403002905542089042d0300389644003280b2070f1844d02c030410000c082c08103482a60 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 862266465 1250 862265215 862265249
    0x1207210317041b0e01080d020a02060f030c0706021c1d0d051b010912020606010c081801020703080a0c11191a0405100e01021b030318041e0e07 63
    0x3402481c50400c00346a211007003030004080c00080c460340841d151910550810740741d00c032440b100458400780a218440c0c461036041d00007241c0005a08c8810700e400501c4281030401403007400381070b68002054202d04001c00e000b010001100ea00103000740d0703107082c1c03200f80400804e0031200007101c0d2017940c4649103602080c0c04a90a440202d0121030000f0340340380070340e50340e80c4509110b200c1c3c0450403e02c1c01950301c3c01e80034400780014003001802401840d425a002078580e24011651101c01d1200903125450030020341501010340920000091010300540e00003d5036601d070140d10343c000006150109a12840050410009034081c9002000403981c0d20758002c803102c1c17945000d00c010300841580101070555806500c086d401a9801000014280c0380b8140b0300d5103000340a03140c1c40540b2405403140111032804005601c030f01c001e2204016005500f4901074820b1000c03075003503610300316801a0784d80c6811580c00c0c4100e00f4514903560401400308040345000358040c82c000d06580b0002c0c0800d015520 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 862267715 1250 862266465 862266467
    0x2011b0b1b191716200f16050f1210200d0c032708090105090a0803030130060c050d020d0b04060506041404021812072103 54
    0x611500090401d60700c246076510480c80e480385120b80d04035868226900742e074082c94240d001164240e8502812182c0060340c0301c0ea00e055141004600613500410308070000441001741d00b5030b00049400072a81100e80c2c86548401050401d5161b4402516803040f1309001d11881c03d10789041d14103d101603c81c0c4007400c8450f240c0c2070b22091410818082e00ea1214000e8025280c0f03040450503100d01c0c03410140d030314040e010041004000e505079280c0880c0c245005a0718600b050440900d12420140c1b07a9080101c181e65623a07621703400703244030b00d0600605112050f150f03142c01101c0c801400c40c0500642d41d950411806295408401407180080f900c98030f120b0408250410507044019071104000c502104400010b94544c010001d12008052010402c001e4001d10764224000d920f03403d030703000c2009a4803075040c0209403082d406030090482640300d00c0306c0c0340e003415401010740308240040245280f845000251100450a44540950380b010344280440c00c2043c5103200705580540f015502d000b12568 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 862268965 1250 862267715 862267733
    0x9050a20070c0b0d090b010608071805060702090703060b0408010e21121b070302160b040b180f0a0b031e060a050d110a06020d110138041802011b 64
    0x500ca541900c08a00c00100350056000558042e51001e41031081f0741e19550b005003000301c2120f081d00094000c250722004284980580000d50f94090040e525001460302403110f07060020300044201a0340700400211562503c020b0009452031a002103100542c54070418900440c0e0b81846803010703d0012602c04124106003103e01a242c0e1450b040f0840c0d640d522403105141c2148061100f50000054a01c00c2643c0030680110380c60484c542c8007a92038903002c2102c901c0c01240140a5400800c000503c9210440703044002820b1005101c840b5012040010070b1050305c0d250b1207218030704804001c0c80710071520311005240c07214802040a0445c80c000d400541c1c4000300d4403a160141d1400140d01051003c407181c0041c01c0c0c50090f050140c41c039a6800001c0d07544001e56030410000e1404480d502d1039140602074520582c04010500040304410b9075086a41c4909402c0340700b43d08110f114400207500c0318052510380c1d07050030304220087e00c914000540b000c8060150f40140720140881a030004000030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 862270215 1250 862268965 862268969
    0xb010b03071e0e0d06051e15011d15030f090c0102030a03020f16122304031112010609152c0705070804030506220c030807060609050a20070c 62
    0x108022480b0b2120200664003030306405015034000129a10030342c203002a58120500859440044104501d9800c0603d1680e03a010348050101112620078420250301c00c50401040311a040500c098511042d00009c20806481c040d800e08084080f003000f4910341d20380703c1c0640c0302e2203100103440c00c40720400000b501c902c0b54004040902d07602041c405140f6072464184c840300e00c072071b10400304010a242485001c88050031112000500e80c040e540301596541c00f405603003a00c60020460070203003940e40d0080301110824000d1340081d60741e031444107900301c00d0082070001c003544600004c040e18241001040b031541d0350015048621804528000a00301c400b6041401d185a1542c400c16140c0170f204440d244181032025100b00d80114002c002c5c06008038601f0b0140304640d101030800c10325010000440030b075440003d005410544810008110010010a015840342c640000d2003510703103c8100c121041620720340d20305079031422800c5168000f03015581034007442050b01814586a582c44450300f035054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 862271465 1250 862270215 862270247
    0x3020712082205130f05010923090c0306040303091208090a110a2d06210b0411070303051b0414060705190f03080c03010f0306050402031006120b010b0307 68
    0x2c41c030300c49040c1510000350042c1c00004c0c003600380298241ca00902909400d031802c05240d02c0c01c000050306170124400c04030395901090024505c010410101903004000408a4600340640300d8565144e50b000d025042c41140701c0e80f0000703151841801d24040c4600510700a03c00c2c071040c20140080d0940001300390441e99402005041040c507401d02040c030b441b030700e03a00080580140392401c800e80e2145a500311000c0140c594141d43d030b16600c14080341c001c80ba20100300c00481c850502035110402a401c2141d43c480090004983c2890048082415910401003540041ea682060202141031500700450054040d00070605081c180058102c2c0c000032031240d80c2c40380000003940c41c10840103101782d03070030f4522855005114642c2030605160114030344104400040c410800101c0b1000750409580c141e88100b280e58041301d040d9501e1000502000d481030740d05100702942040000b82c2130049502034418106880400d02e800d103005c031114034040e00f00c016407010900070003030301b658817141483d500161 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 862272715 1250 862271465 862271497
    0x80f060312040f06120207030f0c0f0c03080d050f15040c1103031f15022a031b040e060615130801020d020a0f0e10050c010605040e0a0302071208 64
    0x14000064504007002122110100c0046400184940c070f07010600f04544454031620b0104450204110403482500d40c000e0115600345ca45111243c03282100c1604c69116081409551100340c80e030a91b0300c01e0070340c41251032000005004202d918907014243c6c000f841074030700400034217003901c120318144038801d00e030340c0216603490551401e54800c10041c90300c40306c030905595032070400c0c140308000450038a5650b280364050100c0056045410041034881101d03d50250580c141c4501c544d400b9a44011420382d806e060344580c02c0d4141d0f50a00104000d059040d15036488141c1c0317001844251294060440969000041041440d4072a524102d41d032400b0340003000e540781905040361002e1541a0000d07065984081100c0401041c254007e0264101c01d4480d1030001c510304500300c884001510860303070880c0350f82e415100254015030140c4020389c10314001003507081e02c48001c1011160500008481039001e10040c03014540c0502c82e180140c0141045142d000340151224492407080c01001d03118669 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 862273965 1250 862272715 862272721
    0x6050f0316090509011e060f120f030302090f03010c03060e102402030c1006060e0d0510051b0f25024b03070f2d0503070e0a0b04090201080f 62
    0x10707003035004841d9503010f20714440704055a001c03148024a064010584040231429002c180c03a418038095001c0c240d40034050461006c3c035984d048020350414040b8981008440803403250319542030140c000c0802040c0c0d00064658a8040d07041c91108024020003104400048140440031104480490302039124400d031010000c1c030042240f8611070b100d00c0e801c4a0055000540780340d1a80d802070800c0742c0341030743c43d2000000b40c8010007030418400d840013015540540c016a980e102c40b0b40046a004415240e0248016403030400c400700340c0d001404103840359400282000411340e507140049104c040c40e41c101914042d0543c0441d0410240141040b4201401c034003c0042e00807144441d01c1e0061102c044500b00689110440d50081c003c103811031280c000c0d0280403801840740720111049481e034840d50320f24140300c3c04415658080060080030b00d004105004512038404001d80750080507105400003ca04d4a401c100c0c0440d40130503102d511460034140030b000980e07030011455402c01070071641891161 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 862275215 1250 862273965 862273981
    0x6060509010f181d0910050f0f0411040c02210708070201140708070303060312080907060e0102010e06070801030302070e060102060429040b0601030e01091520070606050f03160905 79
    0x701d00f54000d8100d20514074241040b01c0b038407804c00c1e000381c0026080721000d0f81c1010303846007a02c0040360440c41d5040400300241a4164103040e9a801500400400032120120800f150030388420b40301c1031015070f2024140801c04844060668552850304440e40d00300340d0107940e980414480c00d9006030410900070300740c41729000038004985580ba48810741c0ba0303460004e4030780540030b00032510007559420381020500c45003a0040085510524000003e081c0e10f90a003d42070b5098000e14140e1811596100071010b1501402c021040c001d00d01a101d080381d561451500a20f08001604030000c030b45108002d22490b039800142c0590080c1d8826590b1814810303811024009880a55041c0004101e00060000303200c1c600c40402d01540c400e03038061014071503980100d42600c032100402060105009465440410381d54064200449640c8081c100703280080200c480d5504011410345055079960003c00c0f25280c42c04040c065090140c000e00204100100045042035030f178850104540e49034000030300e0700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 862276465 1250 862275215 862275257
    0x3010b09060f2701080603060612030c03040306060521030405130b1c03120b0a0315020903061018060602031605011116110102060c0a05090a0314060a06060509010f 72
    0x300b20150050707502c81c0b06100d14485003040214070800440051030203128503503c076400d2244504e4000d001014a900d521040c0558444600302440e003034042803148442001e0140001c0c0011406008003042c1d15003054100060311103e01141c0364001100d20210790000c4e80481642e00703c0d03400f00c40302584103a0464000002c5c08501e1301c07a942c8000b0445103850110100c16281e0300300c40c001c0d503d4000505a08250f00b044610038005268003417001c81c82000062003010b914080c41c9600c00c800350400c10000003091410800b500d0b200851a0441c006100c20101035007041c080604a6400707110891501401a40307910900c06045807000c0d08050500602c08250008040b04c01000e51182d030f1123001103800c0d03c075480b0f03143c005c0360844490b00c0811050340c40000d05d0303400707038252404103481c01e40c0300017094403c0c0d0300c9411096000580c0c0fa0000020a2000340c5218410b165980a01660303d020391307682046410302d03005078043c06010700c23154403036036401070b041910000141802c0d698407040f94002d01030707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 862277715 1250 862276465 862276477
    0x131701050412030b060f04031a060a050109030f02040b10020d0e04141303110f0703060f0e072601050c1c09110607050c04050103061d030711060a1710080d0206090303010b0906 77
    0x1080d1070000d1f0000800400300810040700c803030154502a00e0300e9044c10052404802c1c400d1034002040c168052000c501018803059801d80b0041000991141400100d146142c402d140c90340981c000c0398a08403101c0d08450302c1a58824120340c10014507000448100010b84050080300701119040d90070410540030f10510a164002c070310440310283c01c4014000e5444405000c2150b0f22800d00402c0d60150309140915040e26064034050007aa40c18913a4045504100e03180d411980300d8100c401d450914401e00c1990702500082810a68070011204440d2404400410203410686800810f1020030510400f0040c100800c0390ba469481003682820303850002c88407100c55000346030400000c20802d65500c00d804544040c1003140906410782c14081d220f0050607006440081010070545d6940307080401041e003e0124203040035884644001c0200c0c8180889004040984605040c0702004c0104101c6081403101c1c030007005945001d200450300c80c0418801e00032500c0c40801c0c4000c2c0b40d0394000a43e48 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 862278965 1250 862277715 862277737
    0x20303071b150c0506060f150f0a261501020f0f0c1014040605160b070c170406051b0106170601091128030f02131701050412030b06 58
    0x480035286800c8414100c46881451106004240c044080078043c000b8018400d400070b000d046540e40d6042480254150390501a03800120030304807150510342c82e0040c00341541c81c80586510756081e08400740640c102c0100613800301400f200c0d03c1c80d060048243c12a40001c0d03d0280500241300d03900185e02c1c3c00311035451a07500c1c1c0110b031358102c60300f400040e20a4400604a5002904001041040e40c2030b50600c0c1c4100302d0320303404002c28003400303019400030451034440d920351100f07210864513007041813202900c180c000101e4158900c030500c07894a803078800044002c24014542031031b0a001030807510911003124a02d44404900822407c0294400b00c01080800203100c0704090b040700b41c85c3c8641c002d0189810680c50445e00d0105000380809031003041880b40404100e01c811544036071029401d40d2800000c03d80c8601c0c80000742c482c5400502066039890000886040c20400c404030008020a00110a6031610007000041000000c42c2c080c00d007003900700000c00d0b2080202003400c80c800e9220340c6c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 862280215 1250 862278965 862278983
    0x2401030f0f060e1e0403080408070804030b010e2e0905040606091b030c030b0105070201180f09091505040b1906030f0b0a0c090503120a09080724110d050702030307 72
    0x201151043d8a65205070300d603541041c6840d200200d0004034200070354014000809400000340083c4100c401085c5050083c6512801c00e40d90356518035060609810080070010b0b10814005140c0c50b40d80c41a11846203103d5041c4540410902c1c6515500300348200c906564451000c1010b04c111a482440502400c03102402020304000885102001c2551520000b900c3d010305000781038807034440c040c3c41480580d1006d04d800c07031940044072094118079061504d00311f0300c040000e804c00c4a9562000a0206030300c00300c0c03810494241340005400141040070352600740340400000a00e4403402c560702840d000300c4900d060f925225000c00900f655000148101c11141c1d8500c00d0050401d500c1e441307904080740901c07400d400000111a404810301c1850340503800b58a10f0031801004030702410f00a0a98549180c2141c0d5503200c4901d091595441401c03100022400518200c455419200200b411400c07c0e60550550417a403d941c0c007114941c50080010203d81e000031540c00f801207901c0582c001001c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 862281465 1250 862280215 862280219
    0xa0926101a150406090e060f0f180106020601061701080a0f0512041d0a29010e030a06020a02060f0c07061806050406290f042301030c09052401030f0f06 67
    0x2c0000350321070b01a2002040c4440750014030700c1003203c0340912034000548040110301a840c00c1c00910020b26a0550340904298104003036040c0f81c0e102607000700303902d5005201c0c0c0d5141c840041c12804000b4200c0d504810480300511000300700285000d03100781e1002c0a42102151402d02508180c0b007884039042c20100040c0004141c903891030b6406e02e0180380903030b00805449480c01442218055540c2c00d0081e150f55100d2031903d1003030302d0205011001810000c90600080b00000d090102100c81110390540c0443c00996a0358108036042e0b00c010200303000354a9003060b410044060155880042c0081c0e00c941c61074402890078030b1018040e643c0b280c0107000d54102843c1c510090446018850b589001107024040e858102c081040f407600806032140d0014115441804058100850603000e0120801112016070081da102d0f079000b18080d4002c8581141008102400e031200901010348a01c0400c0f401b00f60070100210480c1d55000c01d00b800110100c04c101c128004e492800c0071544024944a00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 862282715 1250 862281465 862281499
    0x70e07091d04060f02030106080f061528030e0303011502100e0d0305060f0609041d030a0203040603050108160608092e05010b040f03081e0a0926101a 66
    0x101d600a0740f00f400144415103482c80207a049001c244190b90000f20324101082c011040001015042030010f001060b0314501c1c510045070030760020100821420ba481c1142945010030684505581c54620702407000008a40311590f030b03404180200103501d074581a180c0c000c58002c0207220758449203001d042c0b00410300c0c454856190381d50292030602003414000001c0031440c0c903440107181807400030001410144542c0601c0028007200c0651a020000c8456002c60120f041019119140e01daa00039a42e450600f2002020b4880c1030b48110559404080809010320f00600e40e070094a21a2030b10600c0c40c1e55034400b032480c0401d114088000c015520030040b035030044228111900303503000d11007402180d0381d03a0f01521240c03043d40310325102800720810510001d048a4010048400c5a0740000c42000131080c0300303100799000002140c04603c0100c410040c80a00c0b0780b8540b58603003402c102035200e8a292140740c2c0c0321b1040041c91001155a001d4000704c12121074840c101410024251484007007403070394 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 862283965 1250 862282715 862282769
    0x20907080a1b0c05010f061512020706050a06030c0611060c0307021e06150a080703122102041502061005280312030e030a0c0602130302030105190b0d05070e0709 71
    0x441034820b5400d00d2400142c0300c01c103002c1c0808650200748d0340c0e801614058021126124040e40b00751680d6000c004460110710765005440c06004001e000040307603440c40c0b501c0f2a87e06d0f0303d64040000e00015200b2000c01303880c081102c5620101080f00107a8076a2180b400700e003040c11040c0e04101d180141c09200d401000c0008a080c8291922080600384082000400444d82c1d5244a02b10150b40042c0701400080c805000e000c0401c41f99042110072548c6000d4400240845080d10700c010310f601082c200806101081c103c0c00860090000d0300540c280241440301e1405280522801024110040004071464140100000f1516011700358030340c0d00c9291413a040c1703903003500000c0000c1c20180d548022881c08022035100d201c0b40e4480076501c1115a68000c086d4002d64a62030005d006107100101584084c0140c620440700781c80c400c6403003c00200b11100f00d4a43c1d603806409040d0b81c10b2148000794000914509858203082c01c038100e40d95200341114031000726000000e10303c10103030304d45641b040016 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 862285215 1250 862283965 862283987
    0x9030a050f04120f020a06020a080306100203091309020913020f040504080c0d1106010b03071706191e1a0a03110c0a050d02070816061d0a0602070e060904020907080a1b 74
    0x50306c100f042c0c2d07030300c01040340d07214510344019200e20420000b181d81860300b0f0145080040a600590342030686600c00074a45000303216011018070303101c404003c1180b410903034990f8003504940c22500302d145030b5004505003006c240c491501680e40c0b40041402c0c000e0603c2900c03018a040307012511080f261000c0240b924210a82d0b00c160380c440c1d000042030032440f44054030300c00d03c0151340350b5003281d4102107030f81c9060202070131440c4c2000c81405140542e072484200e01c0050401c901c0035250581c88649090701b8640254005ca180e500403048940d014078514003100d0024131945004281c02d161a560fa40052148003907403111442008158000c1100c04204000381842d150295401c644d554984141c035280d000800c07000c004416081404041d028210300c1c00f600c01c9003607080c6031001d14007001c10000c408039013289002d0f034090102003080e500c0c0100129071140301070317842d0b0b0101e040c41d0f408512405ca0180140d4244454400011080724490384802d9a00c0140380f018410034031200d00c0604010004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 862286465 1250 862285215 862285219
    0x6020a11070b0a051606060e100e0a0603032118060626060402120c03070b04140f0a0312050c1002070b09010228180f060e01020609030a050f04120f02 66
    0x1c0d0340009141a1460140ca142180d2515a02e01e004080a08098004445001103941c07541e6120089006006240c2da10311076035080c03582d12051340c100803040d018040003c040d10541810310300d003031000a40c00609c0d0705950b01e81c01603141c1080c4203070055201900100f00315510075485402c1c010240702e00380e00f08004894020140007241030a89560a000c0806e0581d04e0480354042404180141800070050041d448120203407084501078100003420652160302240408802040c28403031071098800300a101d003000c035098240f550348071001c21000041440701500004c01442001000c0740030b502100d805622003800d940c0034000e8581c2501c001c0d0016041607400350982c9000940181d0144211a403151081a00c90701d0a140342841c2d0b08585440100d110400244084055420004620317041c043d1202c150041c0695040403c010003400b0090401070440d03219806121614601200705d0300c04031100d01d81143e84102c070303e0210030a032144d64407401c141c041c064031a02c03e108401c04500403107482 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 862287715 1250 862286465 862286473
    0x3070308070804080909040f02180f1608041719020703150b1e04150e15040507050f0d060302090108010f060b040b0901050d0902150d11161104060306020a11 69
    0x1400011604002c0446000309a10401c011741d2040386822141141c2c402e00c41e074a041552074540c4e0103e401ea11401c0001c602c4e01c2580002d012128601e1031030558403130203410a0300c40c11a17022000410b1154090005030104d1280b00405807125403c808950f60707541c0345c802b542405050b001c00250340303035805c1c4010f460034000c0300c42055a0040500400c902010f00400100c5244803280000e41e1580c0e844081540c0142c0c0c0d040c1104040c2042d000140c010701c54000030000b5403400383c5006001d141040200b030311031480c000801c46040c2e00f0805481c925800b102c226500d810050003403400402c0c1e140c00103503002000100000317180005401000b414901150140107080d52007600c12020301660069255a040c14000761103154800c03c00740420305048100030130115aa82c010624050501910307180f0000001100d007a0035416008051692001c221314503d48501010182140342504000802c50603011100d140280d8a0b60030050140d50010b000b10b5031040d8444000e800d1058000c480c800c80d0003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 862288965 1250 862287715 862287721
    0xa0201050a0b010504060e0118120201030501050409021c08070602030c091e010219080d0e0717030702100e060705010c1805220510030c0608040605221b1703070308 72
    0x401d60042850416043c3c5800342020b08019040e540c100d481c050990411108840440c0c82c0303120200d003072004004241c1c0940c2ca059560000400307488050304505c1c00349040c45c0c41c900c0183c44105044a20f00c1101c0c02030300300c1245526104885106034130024000c0ea0000c800d01c142c904200d001014070302c2c421190315010803d03803c00380d071100303c1142017140581c00680c44205032204400b50741c40750b20312640c003881c0352000b60403507201115940d424040107540000010300c05c11141000d001074015140d401181009010340c001036620b50a040c1d40310030800d854500c1c4140392135608c250707035059510000030305c26081d0001f40200301d210960a102c1400c0b075041c1d40058142080c01e4071211040302c058104a25101000c05107010340002b0307000300740a09030500000049544d041c0014050141030380c0344501e074101410420259000604408070400f000d5190840c41040000100c00c01e550100441c050070044240000c01300d007160f40a5895118034083c98255901c01000a010340c40c4a62280d0040b62 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 862290215 1250 862288965 862288981
    0x30f03060117130b06060405031e01111903270f05160b12150604121104050903271005070501060b0f0403172109120c0325050f030a020105 61
    0xc0003d540f071103c1d101445030a1400301d0502d0340015803010025000070325080d91040070030318000e00000c00b0840ba00c0d4821031003950500c280590300c00300744941407042c104481c1e008020360f07554040000c10103060342c820b03400244c003020100000d0f581e42525425103810495040080d49281d901d07008603030500544003040d0a841c40d20704407805540c2c0044009003842202800322080c00005840120581c2070115101c5843e6140c000030009003035058200d030407505151078845400801c1c4071010b44614201020040d00300400029540c080380442460700703280883e4000c0d1500c0c0f000c44804190860015140070003000c0d0000004c0154520840c020040290340d514034000f235005440844000480400040001c5898036100b0342c41003441d032442625045600042ca0400c5198138201c1e001d1907a07500030007501140a2000040071403200008514107207044102c141c89120300700342c2c00071140103100c80031030f1b4680004c0041101075000007203940c0c1640b100e051540e640c01001d0844015030030100028041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 862291465 1250 862290215 862290257
    0xa17030403030501060f05070b150a240f0c02040b0d021002010605010e0609030a240612030e0a0b0a05070f0606030308060a14030a080d1e0f1103060d081b030f030601 73
    0x11b2002c80d6a00b6050003120360358034854450103805039440c2000d00d1109185aa12410810000c0c0314401c076685004681c0c600703014000c000d601e03e880c14411a00c010355210f940005c000c2d512035034103d60000742e442c0d10070f00203180d0789580303140030350084400c0c150492100d80541c001c0085c0c030000d88070074034085052010401244030b0b0304001038060304408403000000350305209164014044003640c5024010b0a82c22034203c03000c60340f2150a050702501484103050300000f043d1250401904d610803454205030b003000031481469482c03000c120001402e1014404100c00e190543c5520000c00d204030380ea00c2c10000c081d0310043d0745c124800e20f03c0c113800281040640d0304c901c0c00620090090140d036032058864400c19000740030010130803519042107a01d940d04e600e54812021301010000a180666070201c0011a21200c0d000604800c040062028a9035011660380e2001e50103c0c21640d2001c44501c2c01100000118032880d04d803001103032120905a140c4007841c07083c08203984150b5848048030f400902 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 862292715 1250 862291465 862291487
    0xd0f0510090b060a110f0a06140601083108040807050108060618090402010c0f0c0303080106020d0e120304050901060504090b091302090601140f0d0501080619020304050a1703040303050106 83
    0x1003e042041003400640c0100000308220b4000d0342542e00d03000101c500346081250020301160b400344d40d440d882d501415410400c0343c00c81d1003032030070417202d00c1c1c600a9620b01181c02c0300c021040c01d0040003804600002c0c0c104010481d81c2c03003201a03443c3c503034074107041e42d441c0c100d4054180861072410005401c0e060003020307203109400910b0300b40d0801c14080140481490081c3c0140c3c1040340040680000c1819072851842c4c440c410828400142d2175820000e24115060b000b10085420540641d2840c0d60704c140c048080920840703d0420350011864428a180705540c0103c0c1c00207801e00000070000d1308a4003400484092120900c0654045030410180040480341428070502c90b0a401d0054280045005c1e4422410b042214800e04601089800c07504105040b0411220010307004424244c1d5001d510300600c0070100170032140c14081c0c1145a503041208241007480e602000290922008009103006039401074619080e042b001c1c019013000368411241600440d091400000d0068030032448625 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 862293965 1250 862292715 862292719
    0x910080124270f12020103050f07025a01140106111501150e10081b0919060f08060609040e0a02150423060406030f020d0f0510090b 58
    0xb035040d510700400b510080e0380b1554003000c1400800818545520100302c0081d02010000854480c020305c001820f840d401800784140b940400284070556800040c2e44040307801420f4480c1d124106524030000203c101c00c807010581900700c14299096222525256801103003003904628a0201c9020901762252035880b044008400740040107030900c941101102400601d00350b40d44404000104021400283c000342c240001d00d5841107900d5800c202c061240b020252209680c0c9841e41038094610200104642c91511800030000f8000c3c0081045030403001000344030340b204014844414a00c0640c0d0b0182902140740030700c29000ba58081d144542c0310b1030000307003400d28110384403003403001401c04281201d070184a01401200103030303180050100b5030803c01442c6a02c071807810040c0422000508842441007880300040d2840707482c0e01c41120181c80b09420302141c12400761140c0e000034482d0300d860b801c0d154513101c1d0384100b600722500b180c1e00a12207a004c014800d5100c8580404840c04154030341c0d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 862295215 1250 862293965 862293977
    0x4150c050405060903030c0f070923061504080601120605070206091e030706180203160e060906011106090a11040b1c0305040b120402040c08060102100b03030910080124 74
    0x540c94000024403601c1c00117400d49080c1a2103100c42031074030161042c180d02c80d411660307040c07041d035107680700344031180c5480c40080700040c08010340d845064801800c80da014005c0541da500b400c00b106000c030307002400c004d4211403030b540e03550503035840340034001c0c108485d014142030104594906c0080d030b140c0202d60310005040d075030340700261a511010f41c0c0005c2d0308550009004500101d526442034450359940300c1c1c500d400300305061041605103070305030000381081c040001081c42203040c101d001a50112054482c40c00607280c0c200181e98903001d100d1400386034407a0034100003030400702041c0b03200036078030800b0404002c05041003040151032600f841c145c0c01c400d085210742c01c03c200200c03044c09014001d0912500d0507440d000c00d900d032580408034840c0c5804004c01440110308283c03040f40d45d80450b41c9403040f1113040c0300d40001c0d01c4030042d0414240c1d050300c1e080300c004c05503801e00403150302100060844415020086010703210040c01d12032100028644448054404000c0318030380c0d5954000c0e9900c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 862296465 1250 862295215 862295219
    0x30903030417070b07230c0f10050c030708040f0204050406091b0501020307080d0212070c1202010b0904080901020c090a0b040b09010312081b0a091e27022104150c0504 74
    0x115205550300c00300c03040c6c0f0011010101e8072641c3c210f001304200c2568502400d034001d12040e405291140c0010001c0f04940751408101c4c10300060300980381c0100c1c0c2c0349840c81554a842c101900c481e03001d94400ba41c424a01b50500c000c001241d07105188280c450542c0c41003102c22080c80c4410203241d449010b01581040181d0000144004020910b22000d858014140b2480d44c0e510031026200300d400c0c0c8045900400c40c2c000340300e80c4691070b62550f41244000d1099003414804140d440e403020303000a0400c400450a00307400c1e030007480100384640700509802d0041c5403019080d0040c2070344802007801289440318840c81e50606016150680b40c00c0604008800c07807103a021195040000e28500034054a06403038428203180c140105000e51140e03603000c8149040041034544286801038014110106a501708802c0c06004030b810f9400c00c0c075022243c5000321040740c1c88041d121345406007140e40580c041e411104410040c80c18020383c01841000c2e4020000740c094411101580800008070300c080c082 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 862297715 1250 862296465 862296467
    0xb0d05031902070f15110c0a060e2710050114070b04020d0b01062a02180702010f0203010314011d0319090302092503020412080717030903030417070b07 67
    0x5a05101c9030510444151a513140c1481001c481a50086013424020002041065600500c106085007110002c0d21060314442d0000d0302d602c2ca10b10800301409040c0741c0418556694045004660b0749901924101da00c0040c00d0244880c012a42800780450385180807a255100380c400425100290a000d80703400c003a42c8400350300950081c401c030f80c4100072001c428006000401da1500908268444206840034522103030041c5900e07101c1105545006000100542d884e0311582c0705807010101e00007403544900c030b012030240c0000350100701658000000041040310000402400144140003040140c0300150b054148142a12a40e45240d105006101d00c0400030482d0403480c8046081c50701113195668042060b501044828080c8041310400580281c5000c10310b41c03d01c04d110340f404500d480c0c103184061601c50704c1040c0146c036056000c5400e408000148800d40d42c0004048000741c0c40f858841c03100c0b552a40211401c0b10001c008030106000c1c2c0c2e508406a40700181e03c40052112139a40c404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 862298965 1250 862297715 862297747
    0xe1b1306320309120c03032d0402090405011808091f05030a0b030a12020102180108010f14030a06060f08010c17041202011506030b01020705030706080610030b0406090504060b0d0503 80
    0x8402a40d80c01244c01c000c0300c0f641c4d040020014290240302454503480d01060708901c600070035144030307890303c141d60b1142c4080c104600601d9005030f04a41090307645d22642803650040801301041101102406015014011154043d21203540111404522101d410f20400080c910100b03050317003c558103002142c4556450380005455101c05002c651001140740c03254103000610301801c1c0c0150358001064001c50028031440c1000300d40a00b080b07640ca502d00020500c0f001964070803140ca1454144110525a0341403001810440e00030ba014804a62960100c5d080c0050911641c0c2c2c01d91320701036841e04024000c543d081c4442e40801c80001c03031f903034441e01c4500c00b10200c4510b840440d50b070f1703407540728185c00b141903000083c2c8255540050f03440540000a454141550801c40c4290310100b001c01045a1241059034444020b451807003110801c448180d000e0305072018200ea1080c00c045001c580301000b5484284240c1c020f510a0044d103030100140305003050381507400342154004000840a50340160 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 862300215 1250 862298965 862298971
    0x16030209090f300310090c02010501080d0c060e0d1e020a0203031903021b07080d02011407030903090f0618050409120f0e03011109040b0a06090e1b13063203 69
    0x18080c9000704007100b0a40b0f0349079100b19a2004120403042c000d10081c3c08602c00c51403001c50360b0000300015414000c01c1641c0346140c004120401050740e140c0c1d001c02000d43c0280022000c0700c0112000c480d202c0c080909101146040090003062400b040b1101c1c45c8001159442c035074010300a1031801c40154040c10f1107101110800c000d00d9000c100122500b02181600e43c100d0103980064482da5051001581c10450741d16820411a03050841c0a2040c50304500d46a030030600906000448014501d81902c000c80c165009160360115414005503240c1c004041c40f0340c0407001c40c00190703175035220f000300400c540c400c02000c0c1c07007401701821501c00280210320200b00c08200d410101c9100702014002800e640c200c00c1480000b10004c540c3c80001c0c1480d0088494004003241c844440720b0418030002e205805600c240f07c080308540000c50110807898000400032640806050356500301da95151320704102c1d9114600002c0d095400020789100070200c42e8010b4007c10321040041d200030703030b082e82081e0009 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 862301465 1250 862300215 862300273
    0xc090f100c06090614090a021c0b01090207061b030212010609060206042607110901050402070503180105070f0506070e01090b0a051e160b0c0301052b0516030209090f 73
    0x1490510554045e0200591150103004c0061541202c00c1c814841d903544003040900307001900d034440b0800507180c10709060659100381e1740162561107034102000070700350340501280305403817064180203416070580040011841c8010411500d90380c508080301c58450600c20b0000507003104002c41e001401d20780395185000d440040074562641c5044403d44c1e2540003d401315000925011040310300d04090000c6401001d089504604181840d21856101d214640c1c890309181564000c0e40c007240e0042040c3d546c003940141559030703490414900656a12800d94640011401c42c81c2207640662180d01d4840648809503249400c0c882420010303661500000c4030f428280013400d920500c252a0720024080324003c03c9991586824681804092003102405d0310064140c100010300c80c54440700c070340391000b540311580759100c000710603032000c00d0404141d4014030300c0c000c0c03001d05035090b11f03840504d0040e85e000f1650f1242680381c2c801d44607641d01c200d54545403503070006c460f03414418000b019109542070b55 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 862302715 1250 862301465 862301471
    0x4020f130b030601090c090f062a06050a0509011b050409090201050f0c0606011b080909060d020307030b070e0405040506011e15080103030f0302070c09020f0708030c090f100c060906 80
    0x44400043d04143d42600a440038596070b03da4039810682c40310a180040c00d403034038039881c6582051401800c180640b19984007405039407149283d1030070203041c040c20301500803100700818142038808801a14042c0d80307402480d801d160010310f0084044190503085242d98541e645414980140751001c1c04409038160305100c01400b401d51135425003001451159144030107001246001000074151680e416079910030100b2001c0320300009a4514215811940121026039841e520380000552345025160300a41501a80ea0000100280c2c07183c0c0f54000d25035525501111004401403004907002140c018107154454001000b622070504044c06851004c0080640c3c0c158030382c3d01c041100e500101c84400000c180800410505920112502222180c1c1c43e09600e0103181d0348880b2003184072402010344039139000666603c9818034030100c1e80d407640d0004d482500e030704d49002111055085a940c0500450841000304c540e49452840030101078000d458001c000305103501c84200803c608039084401c1d9036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 862303965 1250 862302715 862302731
    0x5070216081f0e0c13050402040608030301030c0b1b1015050d05030304020f010e0d1439041d10110a020a03030f0209330903070302040f06091514060304020f13 70
    0x11802c14580c91798490400c08036680c24203105000440700d4682c01300c0415001440144009050202c1c01403c48000c040783c00d40b00c518500700c2d40d4115850185c140c1c0584a06c80c0c5c0300b04d005100b17400407044e54940c1001c24601c2941e42084c800c40307904011009110740c10800024006140038800d80d00c1070b910603d0240c0101c1c2c0f0207408960500c14410007600c1884c1c4074401025443c004110f69503491540c5224105d040603040681107456a2661210510705404c40c17004039203403181d0340282c221031078415070300035082c1820950b1602c03030140f8603a040b126802c0004031004030220a08a81a60001e81d00400039801c01d038a045005000c942c070408417268003000340c03104942d2403c00090b00042c5141440f0005000081401c07601045028011700c010014000561990380208400040700d03015035012039181224003000009040e950044810546440802c00000e0855202242138500004a400092150504100e1039010441c4e00a506c50440e00485030396040c11046800e00101c011408102c0003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 862305215 1250 862303965 862303969
    0x924190308250b04050708012a0e0a1e0b040506030c0a030228030510030c1809050609010203090708060c0f071103010e0f010c080c0405010807110105070216081f0e0c 73
    0x80c110342c0b0143c40000d9000c1c140400d1000902c80a8018070501c0020000400e024042d10305800151000c008c500810368544650a070080301710401088005100900654480e84003102d484d149003c85000c2021f00707100442c249503202d04583c286e64000f0030090441d03459543c00d802c071b54000e8505401309602401003640f0b9088021407103440c00c05114003a036601c1800c4c0700080407218002c102c256400c0c2c6008040020480788001002940c81e40d0114100036200c0c40e044101604a00c070004041e4480c02c81001100607040d8040c0d1b01560f04103080e150343c0e03030b55040516a90102a0f50b0086224001c00c189580c40c080040100501031081d840400e0040c2850006400c40d00c01225400c800c0c0c11100103c6050a000e03c01c105151885040c04030780360511a0408416001302d00415041c0301703c44d004900c1890180258030009003818009001500e042d001c0203440d00500d410203880302c80054000b00b9103d00204601c441c100c4507170044941c0c4401902ca100c05051450010030350382c0100c582c03448090f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 862306465 1250 862305215 862305277
    0x350601020f16030b0609251103131d04110402070f020607030924120c020102041208090a0e131106040f0b1804050702060a0213050924190308 62
    0x80c0107010401d010b91851030030b200c400340000030602849400c215041284166001c0307a030341d02c070780c0320002c40780040c407081c0e0025907064000841c0d00c4103c0c400070501954101c2c8030f00c940c5096034000290711451b60014060004080d500392001488080c541d2514011400c080d409044594051020000e2a040c90780204a05500041080e0005106010140320340c40a904550080c92052807400d00854046200204002051a02807030119110020348104504c00d4043c0c03030150451600d10784480c490381c5400c0b4800d9005042480c0030f0000c1031000145034102c20349041c4507000500f130b018044c02803555001000540001c03c03a41c04a001c1c0320206000c035042c00110060010b0b1180a079a44601c201a8104400081e009034482c03801e1004010705180d0102d000b94010714043c801584401212024130300d507441c66088190001c0c03802c070420220740c8e00e0b605940ca0f64001540c2e1603044c501814144604d41180d00540005140585010070028810a0080060305491003091003954218485c2c6024 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 862307715 1250 862306465 862306483
    0xc031205090901050a0b0f090a0506040806040b09011a1c060e010204030c0b070804030201110a02030607030515033012100e01080607120c050c060f07350601020f 71
    0xc001140c0489103080801c0024050001115003030940c0e85410b5654410b4451620b0b44e50803402c010540d0800c44d15641288006030000800803915681c0340c07c4550b80d5040102c0301a11100c2032030001c21021034040c480e41c802c0d0406c0001680403040c1050600500e41c000140900c80256520348150200b80a48070b80440d4200440025940e2441d608050940084039001840481030420800c8002500b03007007286c0c1200d90a0810807040304130400d403541403040012000c0d400d0b0103080100154030394554840d03481850300100280c1140c40850500d0340c0d607240c0300c1c0034020060b0307846e4480c0000c1e54032003580040800c03940050340c50070840310480980c01c1025183c0503240c1450b580140014109010030794050309401c8000d0006c2e26251030005d0000c100007507850950b5903a849002c100700c2c8144e08982c0c2d203c0c51881100c0e01c9040c445105c450105044030316900044003005110301041c140c0081d5810000d00901d14428050034000c0794000c0007001e024581507103e550344400c00c040c003d00160351 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 862308965 1250 862307715 862307717
    0x807030f23070602070b040b041e08250e040314130302033a0c030e040209041d0d0c030c021e1003150501030207081909051305150105071e0c0312 64
    0x141503e040400381c640f410036040701c0600f00060000b44034501d401ca09440c1104e41c2500b0494031071001013003261360071445800c1458035025040c2d16690034003101c0301d6982c2460701c480001205650b196030541c9601c41c10344c4d0040000304220500c103400100300000d00340c8240c1505819030250f680e540024580f140500302c050110400b5580b00041c0a2940075030f81c920201c85400d456500c4507050000d10b1a04428401014447c0d514200c00c90342d2220703030564842c00302c0a0000c000072410b40202810340300840d820103800388940d6200d101d14521808000320220303032503160203403644241c0c0c0c00c01c0341901ca41c0450311107900c840981c00350580c1e280d800403c04001039480000741d0f14803586000d560180540c1185041c140100440780002c2c88a00480c2d10f0b0051500790518190002e00c0100c401010a51100f64030070b1a89152070100c2c802d030780c0444d01580c10310b1184d145182c3c1040040d030ba030b4028904050943c0c01c40032021700345410711500480302c2c41c0c0303c0d041d010700b03154407656201d441d40c0d40c00d18110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 862310215 1250 862308965 862308973
    0x181127010806070c03080c07050709020a050c0f07152007180501050a050a0308071106030c04050405010815060d0503190816080405030406050a0c060603061b03060807030f23 76
    0x240745040c84215002140c41c034003040380c0da5032614040c00c42072000d01243c40502d80040e00c2c400b4010140301e440042c0c06603600966960800c075000401b41d03001200c4084c114012482d09401e86400050760008440c0031006006407013881c007400b511000d0703a00b1070031602c0740340440200c0c401031420300030303070300507140c050402c0d40c0807000d25861030111007058000600546900c4403c0c80a0741d40d10101008480c1d21844195a65580c2c0c50050000c0c02c07201159508104003006000e4070341d15030030107401958030590b020050380e03903962000750b82c8e072910386510078020030103001160f00b50900c980200340850141040b42d1426100425840c101c041010f6203600107464042400b8000c02c3c01261100100194907207603800d81041d03214141c0b28411032140009014000640440d103601440c049a0155007101040000743e95908019000d00b081ca6441901100090035140609000348150411703a0b9000380240a42c50460351001c4060020741070507030368404580301c0726130301e1580300c40502c811445803c050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 862311465 1250 862310215 862310219
    0x330f0a0b07030203040f17070b0f071208011703030c0a03020c070e01030c031a04020f01030b0a050a09090c05031b040504060609050907060f1412060f030f010e0d0318112701 76
    0x1929402d01d1640203611480c0f87e2004141c00640006406015510b81011041e901c02c00b0f07481c0340e50790340308911006291060700c42d002103050350010050b6049074019154a030006d01451407a80d22480226040010103005102801c0720038869400740c1400d8901c1811640c80d240c0b100c1c2c5000700c20100740e10480d07803100c84140a10800c41007100c800301004040001e00c000e81480c3c0d0005611003a06025170741015612850442c040d5103182d40354005010140c07100a03441d4481c444000503000c0c420059450b10140c0000141d5070a000403c00800d000b0019140e240c0c400301410080a003070041c100740e45442d1104030100796100148a21801000f0540080c800710340f5000000e00303164101c1c3d046009000900079010203904a00c0d00300c401101204900020640e54240042c5a4104411030340790148102ca6200796400c20551141000769010700c00c8031348034072001a049040d54030a405041901c00081061000a80000d01030003940034024400141a00381d804200010a4040700c0710105070070304001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 862312715 1250 862311465 862311479
    0x7080105040314030c0730030b0906030d02060103060e1e0102070309060306060507151103100f240302031503100c0305010902091f020a020306010e330f0a0b0703020304 74
    0x2c4a036031003120040703681540392117641c00100d1701911001a040d10b1407010b64601f000f42c001d100003d00344004a1440706d0341c08100c002801004038120050040a66801107012850002900c600b800d01e2640145150f070b003141e0305d0f140a4032007428000401d11520086c00031a0941c038070303000600c8482c03800044c0c450390b0350f040082032400b2651040003854070700b280903c50030381c2c41b0b000c9560701038000c0002c00640440c00c40500090140f18002c00c6407030303004400e01044040e0b441c45101154881aa0f0004080c0c0b2490780e075189007891003858821020745514400d509010307401559000060f03045078080418400c0100c0d06004081d250549042c1c1d07200c4003400544d07014810b107405488003120850520500c1000b01d14942c28611020500c040f80c56800417a59100700490311141b42c1c09420b4422950f59013010754070000d0f0a5910403800b404c21001f040440e41c5812207a0706400301e00d88018003c44200d800c0c0410489903000c0503402c9000d8601c04503000034110010411144258011962503103400c072 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 862313965 1250 862312715 862312727
    0xb150901031401240203040e0403090302091602030a2007030b220c09021e0d0209090c0a0e22050f0105010801080d0801090216050a0b0106020f0706020714010c05070801050403 77
    0x4058915040a88014002444401c0382c0d000310400d05000c84d1440c81c0180b80607840c5000302e9000c0d4815010744000c0208040e40140e00900304c034826500c012880d101c11082e500568a60540100142e1003801160300191140c03013210408035181919440104441019508280050304140e0301c0d2002441030210340400000340c95555026046c0a41c0c1124407aa907480c6500d00340d02c60403402c1030b008203a0a41081b1100440818802108403d40d80c42001101800117900003814503403060200c04005000101c0041c221110103400e9529043e03034076102c2d8200320071260144803000d5170407058a03c0070503025076881040d004140030b060f130354007a600d8180010540c100580190185030403000c05002034540286815064407030080f80582c952060141d8240624103502c0d018000d840707400300c0202409002d02c101c1d4140c424907800d490051041d00c030f065507200c500b032086000603840600208011114031202220080052504024a11254a030071b4500755803500045c1a5035036030000c0c00109a0461 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 862315215 1250 862313965 862313981
    0x110d0f0506060103090c0b0f130f03021f080609040305040812040311060708030a0c030231090e03040b18040203070f1e0e010e01020109050313140a05031c030b15090103 74
    0x4039017481400c2459840030f103046164410032011280103d0142c60704429881650000802c20403090811540d499906082c84a144800e0740196070300401c00031200403001400142c0d1845884015080e12404140308072000d004200350304001b820b22001c200380d003052144078441007948019070307116070a606003000610b00640c10a03208100412604000a80394020303aa407110401d100000d91240001003907000e0b115140011018100ea0143c400c061001300300d0007ca9030000300d196000840c2c45218603030440e100c94a02341c415a1050004001c5000c05900802500d18402191040c110562001c10266002982c031a80803c0e4040403c450b015071015031024508541c1420400381311000c20b0151120500143c0c0c207040101c00ca44000943e4000d4104900d01c5600074102c5e85d0302c000891050880d80380c00c2c05103203060025032003042c00501d0007240310b10a4500040203040c5220102e4111b038201a90181040241078035100140c6681d5561440c020034145418405d80d0b40320100307000141103810070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 862316465 1250 862315215 862315217
    0x5130305120c12040806070804051507030c02010e01060b04120204180b010e0901090c06110a0c1502210a030c1103030106020309131a130f05091c0801060507020904110d0f05060601 79
    0x1440108070145c40002d202da04880582440c5049464070b0810074203090104140803580c00d200401d0040d00d60785680300f8606061543e00810898020700c040600781c0e0400d00c1200a0b6076400e000500c4004501e021000c40340b8402400010007624882e0070f8210b80c00c0400040e600440381c8001080a4511a0f070f581c1d40c400d4094000304a01840380e5548100000c03980102c0081220383c114402c504101000400403503a04201c0d00040c066441850107154084092540018040c1d42908030000b0004c40d02c000c0c145a031241c401d401e084000e0400c0700200652800e100c1000303840519034640c8001030004501074410350f4059560781100c20140001041841e04003400f1601e400a0341d50030401c2c09c2007400301d40500304c48864481041b0344034800540489a40e000d03180d440c020900c0281d07040002c82042c2c1034107a0911358440120340e5401e481402c402d2107a10042030080204a0040c50022201940a88078800f189550000302021513189051000d0072101016510090014041c04001059100d003007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 862317715 1250 862316465 862316467
    0x18010b010503010e0c03100305010e0a05120903061603060b0a020a060501062c040b13061701050106021009080f03130605012330030720090705130305120c12 69
    0x50484d0710b02d0f000e54000c01012105001102041110503560200070055800c50024081c1d88084605a1b4a40c88030400469082c03048480860b600c210b41420b0319003d6400074040c0c0703542c2e07880f02c90b864400000c8480c24020199503240204444403c8809000d03607241d030307600400741c030104c501d040006c86006070010010300c40100c103c07028170718145190b581124450f0302e0040b00940d0784408030707001d03003d101845a40680302200c0780c401c05400344d001e0012a04170a00759660403111518003801c80301d00303000ea4030058000c002100f8800711141c01c00344095102cae50240d440e040c0101810f8246070000e0744d851040d009500c44030001d12005008803409080d0b100b07410002102d40003d03400d5400090245140121800144003202c4c2121481c00700b818690a05806c0f4a0301e011117499840c0da0002c40d0460b1030b101902c0c2c640341c03441e030b0241a252131090007400e0300c046512001419075a640200d01c1900340c1101803480480040d8051000300c1800900404071030b00c075400c64031550309100100580c0780820030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 862318965 1250 862317715 862317719
    0x2132c010f1b110c060c0d02060f0624040506040e0106110d0801121a04050705100504080c010c0f1416050105070825050d080f0604091112011418010b01050301 70
    0x1c000c4405a0125050f07091940c5001c81c0407000324286048107081c07583c0081c0200f40080c25020100c0c0d102400141a801d807506640d80804801c0e0701307981600c8503900201c5103501c1403001c440540210700c50480b907103006801c0990741c800040103030388a900700c210b0800c0b0b0400101b040a800001415150840c5000b03072203060200f000041c032800c1d05114455403600790180002c02e03c200006050000007030b401d4122040d18041c02c20941e21541807040a01170721815a4110315540b0a40a44098a001d5406000010180001142d42181c00039042d503201c030040d010100012034140443c800901300c4c0c00601840c10400c0202d1107144079944c841410b00c80c0c208050300c00904041c04440e031140b10000c0c0f035007000c1d81840d5040356039000c24000410078410010b404240c10340060a4500c07400710300480c100c1641d2041d0a02003070780c040d03880c0180004a00d2000805900d44540c6c441c0785512480c1c000261925124100d140d029000d840c400a00c81c032518088540c001c00b80075030700c00780e8000e0030014a194 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 862320215 1250 862318965 862318991
    0xa0c060525080a091703010e1803030c0a1b0c06021207080f03130803070c0618030512090115031a0106031b0f0c0f0614060a1202132c010f 61
    0x80c090840e10001c00610500140440c8a583e00c0800e0250f007042401110107081d405a20030343c3d00a00a20300c0da80c180e5000162902e001274507040c01002540c0246045440e158916585904400d145405000050007038451604406580c4503130702e4043c0c5604c65605261280190612100c6c2800560020080240c3d0001c00e590340226401e040b402040c442e581d80c0c81182c184284128510000d00c0e8007800014002625404001411028018442006600407801800340041c16410340100460400d000e40482c0041c405011a40490144000720310100d820180070000d100c0c81d08201c6070300200003000520a00700046442c003422007420100000184000000c1d9524a40f044032740c10031405403402c0561911689150361029405031410440040768036022010300b600c40903041d030020132100013514610700f007910f04080351044801c5c2502581d0796000d2220349120301d42c5e250606038448150035500c4803085181161002e88003019019200e400c1c07803c0c2d0940c0c0744042009401ca0030000022480 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 862321465 1250 862320215 862320271
    0x2190306090b010507030c15020316030605041e0f0b040c030204080114090a0f0309082a0d02060d090515070503063a030e030a0809030f06040c090509120a0c0605 71
    0x241c0d4240c00c140344107d07071910340329040c5079921000800701800807081c084020a0003d001ca0840c2c081c0d1002c0c04800d840d07000788811500c66180070251b0715883c0342c0102403c2840d0b40000c41042d862600401c01030800340108065440001c0c1c40400a940040c00700b180d15030a00c2a80f9041c80710908007261401c00d000c1103a915040c09402816044002207210201030248a0490090008106803007882c100a400c20040202e43c824821810000050700026442c1400700c0d000915030080800d800d0481c002c115200400d4020012142807040b410207000c0d8410b00310380140704841903510703259603207420f8050018101382d014080d0104080340300402c0580700e1981ea0146d2035500040711189003501810200c1d8100c1894095070b070035000781710407441403140000040901c4403058049641c4d5110b138145d52556030380112000f41c1003148840781440030154a0300003541040541045807071602d030f4141d0075009544600b04080c003042c0011030003030070010a40659035203c0144480b030019901e9005c410707121 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 862322715 1250 862321465 862321477
    0xb1f0f0303030c0c1b050109080609120d0605090a0504020f0a06050909040213091421040512070812030a0507050a020c090601020f03070c170105070c06020c03040902190306090b0105 80
    0x3850b40b562110015944503414407110580c0200b450740c0c0d620171950101c00310700c2060180350b000411900300807070042c1c80000d1950003451150700801c4c102c00d00d1000b00060742c02c041ca10b8100c041d2944c10025890f901d01c141c00340255105000012a82082c0c810040c42034a2540780310701a0054034001c100a42e0004180c0b1014441511100b00550362840029954204d0100c0d4030070b407602d0a903c1009001c0004520380c4040040b01c102d0303500007007909201400b503030032070090707001000c08120500003801d08540115140103004210f4003800d884080440c1007850510640f80710030004802c1010b40d031014080c0c07581080882c01c21130301c2d10340c20000c02034480000b410340900407000321002c116164401c100300345004607450180d90302c0740014a0700d40000800c074803c9040003c5100f1400d0401070301882514010b264a03140c620181c03d259547c44069081404290b100d0f0105100c0000e0035041070004085501303680206600d10240148090304860300d580210110601e801842c440a07600074040b00c035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 862323965 1250 862322715 862322717
    0x20c0d03052a0d020105090102040f181508100b150706020918010902210c040302091504091a0a1a040f020d0e1c0c0506070809030c0106030b1f0f0303 66
    0x99608070b45021000410007005040400080d50180b41481c100049030098010903964028081c60f21145102800c2c0c8c0120f020b01e030300400c54804104001c44800c0142051150010b001040c1140042d4010015920550102a4540000d5184900c0702d00522488000303070400c590101655440c11030b08420313802040c0005044950001d92240140e588441e201046a030b20102c50445603142c0c811b142c081d4120110402c40c4508150b40c0c552498060400300e4440c841c140852070506285408000c3c00d1080901458036603080000c0c5010a40c4840c0074286401c0e0040d000500c130340d6490701d00c201000b64003c00c6500010316000d40c100701c0068683c100c80c020041102c02040d00010b201c0c4501c001e01ca4503001c10f080d58982085401d00380401b05155104110240042140c4915240256003001d8000f800502581004000811403405500440d0304169048201c03400c0000240c0c10500b1600c49400a6612140000c10004c211a1580d4003070b0749200101d9555455074600b0034105000c00040c04010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 862325215 1250 862323965 862323967
    0x11012d02120c09041b03020d0e1b04150305060c0318010e070611010b0d1b15170a060e07020a12020c0a09050a0b0603010f030506070c050d08060f13050f07020c0d0305 73
    0x1043d96a90740016400b645c150303111001c1c04120f003001034020351010045a044508000b54000000c4001c00c101044080d0390704006030424001c82040300500c40500031001c035031a0700002101007841044110701c1034880404a80e0f99082c44006280a14841841411903a04051041d5151040400c1d8102102d900c1d0078050b02c121402d41d40c043c003503c022805140c00071017500c103a40602c000c01107008078000100070210000d40c0c94000c5070f1120356420040c180480c0c0306100546600c605410f6590f44916a80c3c00010181d85a51504203021400d965000c010b038001a044401d1003000d002000d0900818001030480303d0b11540400c0b8407200c0c5100302c000c182e41e550002401c1c070071140c20541010340020046a540c2da190b07801c605045400f800199000c2c458440010030260103500342c080d8040c1c000780100000760392181c00b101c0c4010010400c0e40c001409039076000c0b890300c0e580c25403140314076076030030202d400e25100f43c0f001200c2e28003c14103411540302008040041d100c1001035485c080d0145841 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 862326465 1250 862325215 862325227
    0x510080a0e030d1b08040215071b031209060e0a03020d0c080319080a0507080109020d0f0f02070219060801060f05091f12050c030c0a11012d02120c 65
    0x200208a8030950352042d020015581c24119001d91291507440d80d440e41e842da054100040441e04030742e085038000c0d001021707910031030742e42c08040028041ea01e102d2303415560b542e4101c01185212050aa1085400302c1c5c1d41c038000c603005a0018038950180ac11454014126444000000c4900a0910019004e04540c16a000074070840c4011040500300c0b103412070369541420454007004881c100c4c140700010341c01e10301140300c12101c3e019450041080e40d403100c01d00e90034001070b90b0080d03001e0101e081280e80c4e40c50301d04410703440500900000000a04005071100b80a0040c824810300c0d012117280400e01e5000d05100360703034210880d40d0541d40545809144000c00a406650911070600003d40c401e007017801d07034603600010b00c6c030007900c5130010f0f550042150030540d072982c26100c0944004881c50030920010b001d500c0c010002e002c1c079402e6482c04150400c0314540c060300315000070441c0c07413418224800d02060780000e140c0030003024141c26821032602502244611041c1c0000c1c2c85050309020000d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 862327715 1250 862326465 862326481
    0xa110409020613080d09140102060604180f060b150f0a0804031b050106030c0b0a020703030e061b0d020c030a0302030409050606041e0e0105030a080d02450a051008 72
    0x83d14590110f0b5401c0046013074442003226a103212034541800000c1e103030500800c101003030305401d94040406800400d078035100e44003040301500d0010700c452581c0c0403481c1d0350030114038500725907040c49015080010300e440032a401c3c810074006100d400d0500720820410145500c4400c0210f540000b03240c42d1028503a01c0340c1c80c00301ca001c6011102d941304098901c408200f07100046d40300c541180d00c98043e18024075540d00c0e0394845401041d030660b000d40c100719000c00101e130080140f00000480180380d07916049800d181c03c11800d000ea0820f0041e130b40041d20350380f0116010070202c10348a00c02c4004200050f1039640c000c2da60310581c080e0500c1103407168045920ba448000568000c1c040c800500105100094100080c2107a40d00c5903810741288400001001c1c140400c004402c1c2d5001481103250500102824000c0e60090300c03802c480301e12140240c1100c00090b00303460000b0100b8045000d1700344901d01301d90701c0700805501c0944a0001041708014991f0f8904105181096609012099030f5603265 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 862328965 1250 862327715 862327717
    0x1103010b09010e071805090703090309180e010c08010e150301020d0c02010b010e06031003080c19050d02120412030305090c090108010b01140a05030f0903131d090a1104090206 77
    0x11140d50800140301c000315400708002000340c0f04d40b603565201301d0b18001e001c103910b01d01003003482100d400c18081c034041030501e88240c00c00c04160f4043d0400311849070396800421000960f4546500c82c0c04ea44140c01941001c083c01000c00020040c074140d4001d5040c07104450481002030b1400410048803a0444c040e52002c1d0140d82d01c3d103110381c00402100244404c007902070113040d0840c03400901d0f2000c14880e2072078050141c0c0d0140d244002c1c0d240b41d66045031755080c850703480b43d0401c1c04c5a119140341001407813030305a040c4281512540c0900b000d6140040040c0c58810840010740b440c0c18140300600c20118200b51810f0002e81614000c10310b5200c40c400c060501c0044800b540d04580c0710310002c21201015084200c480b1403eaa5406400c2c2c0d20028003071260041c003000c1000608208049800d140d0301054140d001041c0c04242c0e80b82c10b180d4140f00101c0e240923405a03c94460312880003068079a076007945035000c24442c000e013130450602d51b54440040203e10465110b156904032aa095480e940 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 862330215 1250 862328965 862328981
    0x4060f03060b13360b0307170304081207020d111c080301051017040b09100603050607120902010c2015030a390521041b0e04110301 58
    0x2e008107580d19188140c490003042c40d40140c2e800c0c400900c68001e1020310043c50b114004010a2080700c3d0045265044400340000742c4050303030700d44201800402c011008280c00c05a00e40440b00079942c992800c0c2c035442c01c1c802d940300303592000c01f402d010329005a01c400e4602c2c1c05032a40105050310f000100360009054141008051403080b142d00003640400c00580011416200304940710132485400d501d00300c0ea2000540521503891441401060000d4912060650003100040a84410010500212046507501e43c0309480d194090300030f02c50f0359a084401610a11274524084c403a54070190006400021a140000c24450385800404003500050041525848008040009407800c1030310f829a00c1d08140e07002c4884900d025048000703403854804850343e4132103242c401604400e0f900308030209440c0714813492042c4101000010f42d04003450003504131155039985425164100381c1080419000c03035242d401001d544808040c0503580700c8844072548142d000551400309604000841d014002803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 862331465 1250 862330215 862330229
    0x509130210090909031701051014070c08030a0503060406052d040213090e060c090d08030429070e030d050d05180a050303152b06140903070303060f05010504060f0306 73
    0x10074082019406100c0444d030106d03040c010801030b44c80388200300000c2e04065046020441c03041c01d50200d0070504014000e518040c400110030203560f140440d08641c082c021a9000410010820480e440c1600c6038002a0078261422021504030318003608826450359006001c0c07803a060703031848880e0b40c0e5804a80646020b5405000c8059803002030001410351414a5540340c010840040d035150000c0090710707030210740141010080e401c152181035169201074030981c3d1150403008000c60403034100340c151241580541943e5064074014400906013103080040c01e22a0300103101600305141d21001b6158420342d030040c005419100e5400200e01441900d00c0116240120040081030001c040051441030200100b046d143d6078103c42040398120604115000000e0140b2044240362604202042114415100050440030054510722464400c07101310003e41d00c0082c1c5c1d2000c02d607040c099a0020140310303a445001c00e05150028100740030310f0103071400300b100b030b21100005144642c0041e030003400341d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 862332715 1250 862331465 862331471
    0x3060d0f02220e1915110304120e0102010b1e0a090f0608060702030702090109050c1204060204060f0201060509010e0705040b030a0f1109031e01140f040204050105091302100909 78
    0x451100540606403002001e45510f1401c00c1c407102d501c801040d0100000a0907104040d141050341c0c80d44c80030490b480e103900c07003d507440d0703880c50001203184003c5006500802010400820602c4000c00c503a0340ca02a2a0459040008440743c0d5104c06c07140700d450f4200101e41b4411a414000807482007501a80441129818a00c0120941481e50b11070410341d518403040d0750340da03503481105a0707803840b80400c000d400c82c07400c4004000d12106980090f4104125810032454080b5010088da845035081c2c0741a2642a40001e04014964105035091042e01c0b41e40028001c507480d00d0000342c00d110b014414414940345240002d42080d100307038126406491064001c0b910307400c00d110701070010600300d0207420b2802e01c0c0c060f00a0017020301c6e9054907401c14004004140041703d103601600c02489054680d40d40d0340d01c9010703501c0019050103166214000440380001c0903d00b6004002c183c41046c2c2c851406600b6400c180070481616800e0189801e030142d031800e49440502c482240c031411258070018074589 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 862333965 1250 862332715 862332739
    0x10b030a0f021c0513051c03110a08090601060c0507210506010602070e0117060a0908041505270303040b09011704141006181d01110c0d0201090803060d0f02 69
    0x142d21802202403c026100300802e9071105400c42030340e548448090720650280c5000c0614524620740c41c0011021031802182e030405d41c1c1034109094200d000f44402184d04d2200300702161204108a600401a52914046504440e00d171592a108503001e840001c2c0d440061240c1e42280a10704126510351020403070310b46685da00c4e002515070020340540d20003000b41700000182280100625002040c000c0040c040c3c0e5140d12241000900c03851104894107038041c403000990600001c001c400724043e03625a103545240348610720100c80d008194001191442252104042d10000291826140e158001e569101d5030707500141c4030034141e250f0117014106004104010072001c43c60000100441900300c070211802600c0d41001e9521a00480e81106240c00000c0301a20b82c5410992990141c1c01c030402c0080020030185080d05d80030941d80f02c02440000d40c0402101040152108400303052008110554060391110194800035141c64428043c0c410320a0600c40070310441d0342041d50040c0400f64601d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 862335215 1250 862333965 862333987
    0x703171e041109010e0f130804150207030b15030c040903050430080a080709030b070c1401050108070503070f1203050c010f0c030b01020c09040b0705030910062301020c09010b030a0f02 81
    0xe5030440c2d061b142028590b01180c0d8003a03013146070141d00d03544100184d080c141002001d00310321406003e09070031480340180c0000458501c400c9280140c0d5008100243e030403140c81494504840c0c0c01985000e2803401c8000e00100768814141d8040e200d0710340518142d11070b101d0040c02400c5880e085d0b000040340440601e0100003844005100320f000076160355100d41d6802200703440e03a82281c80090010015440041e00451040580c5100303071384107010480703201c0b210119a80c21110240c109184642c8a4803041c003451500b00a0b6200030319000c3c0c44c004c0c01c2400c0c8447c0b011800c0b4224401014000c0100d0a030091000030340000100b014480344c100500150840000c000c0d00c00891140e001d030240b0b4507101080e0600d01c1c812845290019070708401a1100c1034200c88550004011604c54018000207100c1185580504802008ac44195402c1100c0740c088522481034280c51850555001040e40310182d150130340541c1c11034801c45415526680d076200010047d0009001d00b9804602c00070b0080100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 862336465 1250 862335215 862335239
    0x705010e061009020306180c0c0106080c01091203021903030207020402160c08070302011b08040f06050423090a0c03020904020a050c010e0609030f090a0b040303050703171e04110901 80
    0x1441814050b4150507994003880040f4881610059007041c0083c040d40030b100309003a41d540d040f511450010746012015141d46d0300310303403541d00044ca6a0b00800480345d420746c1c0c8009818003410303c0580091170890341f958080d64030664441510580301c51710390b05900f81740c000e130f060b91406034018000b550b903107100d01076502036070710911400c55071068806030210b4801c00000751641502c3d41030b11944e02400b903428180c1c52440540c00120780c9a0380c20000400c01c00d174442520380040c0030641301c0549550902461240c0318070f90641c2840440102c14080d41c0340d542d03030340c130087d00001426800a0004100d4400318068440c01f00b005800c1800010007010b1b040d4460010800043e000d0020845404078075421038032058142c40c0c80721780d9801480b4244400607440000e2091540003814901c002d5510201240c250300030798070a80101304085401c01c24560401609101500d404043c2e50341407500d000004002002521800e030709010707040004003000800c0322107c01f0404020400d05403507a4814a0100c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 862337715 1250 862336465 862336471
    0xc0a09050a05100f060503040c0906062102070b0c091203040618170a08030a0f05010321110316050c060d020a02070807140f0f090718050306010e0c0f0705010e06 71
    0x200c92404001440d602e452140c0c0d030342610310000454088905d0903400311002e0b000a4030070380b100d110740c02001800340d00070310402009019039110300703540f5580e07181001801c20203003000c88042130040211b2400101207441c441d07445a1903044503602e40c40d034840400c0142d6160100204a84000103001c2412504211580c4100c19032140c01c4002c1a01c90554105100328004803d60aa20444e4a040002d8440002c1d44d030208414070005103c140804c4a4001ea81e002e9000f500d00b150362000d100992041041e8039103001e1000c1c00c0003250b690303540f03001070341d40e2140b050300550000c9400c28800030041c081c040b0843c590001444140c4030281042c60b940254060070038040076124016002030800408101081100d810300d0000c849100c4007014007200f144640421b55008000000c20406950383c100824013507e07143d0b0310029840c5070708910318258507858000f03e2180e44844010082c203440b540d2400e601c4908903044580b1100911641605800b03040b50080441d400e0031244843e084c800120288 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 862338965 1250 862337715 862337731
    0x21905030d02120a0509060f12072c060a091e0504140705040308070c050616061503020306040210020f120a08060904030c11060d0f140109020c0d0e030c0a0905 70
    0x44000c100300c01079a585041c090904004402404105010350060300a403003801b40c090045032402140d01020041c40c1c0c04440314070180c02c940014070401c6c80d03000300e003280c03101c9280c5d44500d00e980d031101d030041d00c288403a821715100704030000390108003921490b1941300a15070714101c1d5422000f0f08288908031400350241d80d01031850144410445032441c2c02d05409900a5242e0340c0c42c10341507450b2250240d11405007900d0002e001c2600150700e4664030018040034041f60090745070110145450b1098503440b44002c401c14044010078405641c01189060300558111079031604103e810905905140c0b14048444982c040e184107240000c400340010701d650b202c1581c61003100d50b00c1e8020084801d005a40190015030725005c207800003000d900d6007600a400c020680c5051000d05054842a42d42e022031113803181e0f4640300c1070200c050601c1c50f41409440440c4003541000b803560107a540d9804849201000c10003c1d0903615500d46061080145180d03003e00151f4030b0a4079107030b80c00301915003520104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 862340215 1250 862338965 862338973
    0x4060f1202040b010e1c060221060a0816060c0501060305060906040c05032b12051501080a200f0d110a110d0503011a04090c090f0909020a180902190503 67
    0x381c03c3e40c4a280310301c4102c0d00c0200221914070f00080290345e4048241000c40c0c1c1c00b81c1c2000265101a10b840c01c04112100203034800b002450500c0c05d100e13041150f40e10030051a480044900043d60b58031030040180c600b00e242c40402c000407810b00034003500c9107500c05000c40c0a00070900c181060b002c030304940300c2c42c090034003003003990ba0b10000d165a8400a1500654030f900088001242c04006500040200500d14141010707002c02110035003103505c1075400b441090442c115005455030401c180b541d10508103802001181d0480910400e1490000005201c403100000c400c10b050301e421069900310b03414044200315640390701c0b01c0341c3d10755404051100040ba001c1065000b00d204005000e02c8aa6000d5480909592a0180403074011001c442a642c0b280001d001c0031800f01214403480b4904a1a5620200300f1b074500700245c008621f507900701d055800d04140100e800350320b40000050403112406120520440c18100c150000c141d03949009500818080b141405000181c10700030958808406603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 862341465 1250 862340215 862340231
    0x50f0f0721020303040221010501080d02010c020102130618030c0608010e010b0a0e060c071802042108040e060616050a0b0109090312110c0a0302061017060f040204060f120204 77
    0x403280701d2140040c44070040e8010800140142051849801c2103042c0c0060b1030a0074803d4044a03081d51003d800402d025801120400d111540c24051140c94110703d000841c900f0300d882000365591b0f0643e02800b424801d5a4035a0344040140004403401542c000400d9034a194484100134460682032085240d62480900042240c90707860b4119010000300da00e540c18208199020702903250001c424120160142010000c0e5440303440020214a11928070016500c500f0501000341c100360040b415031102c3e0700c0600300700c00a5801d800301d50544840e00b40503084c2c0e030b48280000b40c0c288590200948615042d40d007000411000240300d00016214003405280e680c0c803074103000c040395802d40024002515030100c141c207070101a881009a4180e2101880c034140f0f205941e030303140065440f030490059000f1010003c029180c1220f0f20080c103c00c0250340701100e50481e00c2c41c1c3e510b001401c00d12140d0700b84000300e011076a03943d100304000c140003141c0703180c129555890b075041c060312020107030f0190f801c004071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 862342715 1250 862341465 862341503
    0x1090e150321191403040201030e0f07060e2137030f02010f02030606040506090604080a0305070c1401090308090301240602121204140c0307030609031115070e01050f0f07 75
    0x7510304d00e440f840304114110341d141d8004401500301100141ca0030701549107035015100003404100064502611a1050030034014107001c5243c4c6030308070a001072002c2c0c070080380c410701c404602d4020903c1c20007920081c0103028442c0070200c1c440007280c031000b843c800c14070508142d00701640741d110403020340080140180c2d041c1803109920080310f50f564403040403c030034401483d180d00a0803017280c02400c440d042c1529040c0c0c09190240f450804d40c0820703030200e186020815014004c0d005400d09109000c0610b00c640000b9290a030036004c020503407030340481c1c118116242503102c00701c980d03d2600c95120a603c1c0080d120b8406c6294042c107401806016600c00b1540c03848070440c0d0802010100705105a9180d40b11807086c851550250000c40c014113074000b52507542008003002450140d00c000030350342c5492402030a0184900f80e00070721908600c100c0007a5104010125611402500f0003d1044225400481e1244501190082d1880010803043c1585c0703518409810038500c6450406031642110132 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 862343965 1250 862342715 862342727
    0xf09071e17180c0607050f0706030e0708030705030723100e010b270903040906080606011e0c0201180b1305040b03070f1401030e010e010905010b01090e15032119 71
    0xa5002c40c10360100c4500b505a0070030200410340103000e9000c2da000c2c40241c02d04c080c00d200e4154048030000c0d41303944404c1110740c0203011207001071180c440110305e8140f0950b90103440f402401006030000f04410004140815a90345404040d6052001d550140a03201d201400520754412168010740ca00460340413242082d500300c1c80c0301300d40c140010028a00b0b2a243d58500b03100100102c48038041407200003034000c6240511006080f1080141019151032000100a00c071100c15820702c140804180440c1d44e50080205c007286e40d02840c08080000c15011409040f282d00c3d80a0300e1b02090004003d4003402500c42e12005a0740115010b0108400708020035540e0b000b035018826490203811001c22512510024890b8502c4040c1404a20031290030400303400c60742c08031035031003907039450f10132103001c014003849840120309090134400c108604208040301c0000d40200710355072400c1040350030038856404000314039075a05002c3c2d65185100c500c00540210340c00005130500aa41d40c41003003401a40140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 862345215 1250 862343965 862344001
    0x402250b0411030c1c140f0c01030f0203151504120605092e0e01090c031401050604061413022a07050a0308030703051503010c02031201050f0f09071e17 67
    0xc1c07030102d17400b00054907668060b980f810b0032034169011619003560f0311014860b444a4041c1400a820b40718080b60024040c1c83c0f0148401c04918810010400e00d40281340e512240140259800042d0180d441c203013010340c0c4155080180514904c5a40320100569500f01c284500080350980c2d800d135401030700109803c80c91002c14140b10860060700303030700c01d81d950780000442c04030400081842c0d00d8a07103900f0201d1516410a82d03e10391601d2049408100c01d0094a41000c001d40301000424540b0301a128004042c00c4802d104581205000c0d0b18070361160140c58012840c03201e0401c086161040c1d0f90002c402810b414107450080c405c0c0080c503481c02402200840307030080340c2580745503181a0300320000c0c54010174082550b514480c2c1107940740c03801d104007102e13030405400660355598208140f402d040702c168005032040c1030380d031000d802a441d84049104500c205a4151071030380c6404100b030381d2161980c510079507001c5000110214580d80250001c00caa58030840308201c83d140d810301c00c5a0201c0f00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 862346465 1250 862345215 862345219
    0x5281401082a0310082506052208030c060c13030605180f0105010807080f0c0d0f0b2a090117100e16110703030c020402250b0411030c 59
    0xe000240031036101c11400c1c002c0110410980c60020681560440150800d46040781e08100d6214280000e060400c58284544103241c500034210310f81000e0080d50701d01034014070003003000104001d03071030110074a0403641200c0302c400031110b02c648580d82d9503034a4102d021404014030415020400d5218035100710b5550084009a100c0c03142d08644403040070304000f40c003182e810700d40420103001c00d91080c080d0040910342200082043e515000186150006c55000304409400107950130082100004400100d00000d4803000c0b541111400d01a40e25003040501410340020b800c10840d0108070f4003080c007040c003a00d905420406003407074040100c90047c07842c1c0c4c1d408298079008404120100c280503a500c0000c0244c0c4820007612080c03c081c41c1c15069809843c03010091075a141c050b41c0140148600c020010002c1500b940b454070018070a000310030022b401180d00160b00d02404010010710b0342800d02000714061142020319060195070340488058803114401104600180f03004600c400c006080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 862347715 1250 862346465 862346477
    0x7150b011704021e1e0405011a071b0302060c0d0201060f03260d1d0c090709090f0f02031302041104150e040f050c03160206131101030605281401 64
    0x580d402d00201e07503d18422144138888048420810365244d1035000580107112a240303210005442c14081920010703008120034051403102040d20365004010740d03018a1304403006d1b444c4a00c50782456900c00500750006034101e040081c10301c0c04590009102040060640d001308003c555481400d0f0002c00300d4000141615150140d01c4038884807001c00c100d9090844c0d07a55440e24020418140c119040850710008090303c02201e003030b540006022640402d501941e511205140c0300a000b000344160b805009036065545800c26840a42503000141c15005500215564102150000015205410120701c150b007000f005140140708002035074111844c04030034410b0a04a80030544000403100b0100d078100b07030741b5020640040b0950203202d000703500d0003030065074a05148a1310310b09603803010944015584500b0500c0101c200c16040302d05240e40184070281d242c82e203032004030064041765100f039501050201300420780b4002504960710300c96980300402080d940c2c8081405116402200c19404110 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 862348965 1250 862347715 862347721
    0x3020f071410050a030b0909010903030506040c1709030d1a0f0a03030806010311070b0a0606020f0a05060c1c0c02030405010327020f03191110030e0a0212011107150b0117 75
    0x40030303030050004000d00382408548641d5406c0031610f1031401303e43d001002d07912084480207160b09031140ea0740020098a00740180a1460005080c0c01c0c0c0240e0315800d1410b031500043c1c03200d8014026200c00c2010460184604012070304815100d4140d000310900c0f0705090007103c0607918020341ca020481e40d0640303966920307a503081e006400400c900405001c0c80d020405c5481d0000300500c50042c8203034000400001c07001e0601d00000c1c84c2030720603001d11000ba448060300e1408110001845503100240305032459940d10300804d8120030030081c105440c00c15003000000245035802001400650320281c1e010803c9568500c4500381d03641c1d10785892018182c4500c2a2005410400103c1c030111401804036079068400f220300c06420b66039044141c1d1f4010194061000c1441e003801d6020107160b151506002c8401450602512075840110081c0710341c4e50140d06640c0c0c86d41c00c8d000180540c0b0010040b5868503400c2c00c041c440c4030762900711605014a0624400000c0d07020321807018000903030a40e01c84c0155 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 862350215 1250 862348965 862348967
    0x606220305300a140d1d0307061508100b0409050f010b01141c0207050a0b010906030b06060a0503161e0207030606091104060c0203070b0d0e0c010305071b0204060803040303020f071410 81
    0x45d010b1010562000e85510b400c103c03d000e4a01005c200b42c00810003140e495406080c40001c84e4603030100c2260400781d60500b04424907001510b1420030300c000c2c0c8001482c0140e200098010b1410a000810b50701072400001460101940f25600c0e0490030303241c85001c4425800320301c0440c45030b074180404810030906001180712566000e04812032240c0201c4444410381c2c1c44150b4085001d80c0100344443c0c5491050040041d000c601980284060310319a040402c000409051400300500300080c0104107605585020310901000d01c40006181c50a407040794035440003911004039002c01c0c2d44d078a05028001070708404a00c00d41c062510454000d80c10035041c074508070783c000792000302039900d131041e0329011580d03a80f44002041d00900864000400a0b95500170310700b080303982c04080e41414a40070401039942c0e04510aa00308041c7e84542d0408010340e840050028081d83d0002c40c000d04c4003080c04001c042d00010095001c03003800b0122078109907920725000fa5a90380140c0030350001080e000c644002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 862351465 1250 862350215 862350217
    0x506010e010e06121e040b0114150301140f100228030f080901090519030e03070302010801050d020406080303040b0403110d020d08070314090717060606220305300a14 73
    0x40040301030305c10b810405580150020341010340c1c1c01d9841d40705a01c0100003401000f841069540c60079900801e061422450303898090005110341031500a0003844034030355036075407000050356060060242890a14429000f0b540e9030381d280711110414208601c21800718145960260019070540e1402c03c42048840201c501050140c42c0109541d2160410790014000348041050303407070300d9211000c03403501e03600703008220780003445100b4001e070008802800581d9000c190b07031f070650341c0540b0710900304280c0d4800f080090403590301455060001200344030800516503040c5008601a41c0c0304001c0a415911040d15014810b0180001d44d00240c1c50028043c0100340c0b40c2e500000d6424009181c01b099100a904d058046503135003115049190140064590300c0a14101020303020001c101e9460000c000c106c4c548928066030b820381c05e0a0b41c809010748404610000078581c00030564801e2140c005100701e1408014090174602c3c016401d08450b035500318010740e03107803030190b80c0c41e0001414101d00540131 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 862352715 1250 862351465 862351471
    0x10c110f011110150b1e030603150a0902120d0e09060406170c10170103020d02060c0d0c060c0c120827030705010b01020715050a090314010506010e010e0612 69
    0x10b2182068a1180c0070308207100e03150b912004400d020641d4494420010040011508a6089404140110010242d1a022184400714000d10082d0303603488040c0024600740d070020700518840300c440d040007620f01c410707049041c00d1403023030780c1618040d4403804505403907004420308100010480d03c016106031400f0982c45401480c00340002a62a40700e1543d500c4d2102240c1071000141d01c007070b034120600c0c1000f00d5035158000c610301c3c0c01140d560030b540c0c542c2119030062002038801c0c2d03c0030032503105550340c6104880d025082002254075031080044080c20781c144002094404030b00e40348030804003070300440e08101c0c1258050400015140300d0102601c3d8008042c001101034124200700411403003091400ca41100301c400011f544801e0a40b0b89142507031072044106045401c608c1d8204070300d8040c90104001e0340441e09101e600e0b0700c42e40e8800c940380000ca5101401000c1c41250040c1c06503410b41c4514043c1d08287e0ba0719080f0070f0444015600034880d0f0803507680000081101c0b14a44101c8104103030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 862353965 1250 862352715 862352717
    0x61a0a0c14012910050906130f06020d0309083a09050c1e12010f1104050f04050709150302090d050610082d0c03070f05010e010c110f01 60
    0x11824015120122049880e25115015a5541801194406071141d000f90504030348154140c1c1483c400010a9900d000d910f1a00c050201c0800d05640598400c020345200424940032500116036448014940c0c505500c292800741c091b42902e014601d1090180f005c19642040440d4504811400440d800c09420782880c101d15181c5940204e080b51054604d10f00501442400303e008403050a00b941824044040684600280a803040e960028224001c2003182c0454103000036000480303116002d040c140d1201c2c41c4092412002c2c0d2140301c086400342c400d460090b0303405250100304600348003c8400613982100418443c01040043c000901142c146044071458098100744800002c20004511550211600d411400410003148100341c03003074000301a058001d1030300e1140020769421403040914500307160304840d203c2c80300e0481c3c100030000c1d600502400f21a0781a42d42d4502040000c0d81e4000d0350300180305111510443e40c03160343d010511641200d844004049000104a6220140c600881c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 862355215 1250 862353965 862353977
    0x50f0702120a05030c1e090f03210c16030b041203020c06010504181a16020a031d040605060a110c06090105040504090201170a0203070f0f020c04050c0d060602030c010c03061a0a 78
    0x4810a8280c020030340440c100111b071b9844490507020464800c00c1c1c150b2050080c1d000348000040303002c0e108140004e0314580400c00b5560039508003d1400c1c604107080d0100382d6136004200000f04044550142d00c00d60140240070550103102070101c040e8490340e4080303100369007ca001480300e4605a80a0b042e42015a0326142e00408190346078102c112080000f42c004500040400c041e078101c03884e10190451961001e00381404d81c6540160429880c10000740c4002110340500841d510b441d4000c102800001f41540e0300c0f0605068010004881d80c2505003407401400c00d24116410036000343c03080312005031500c8d42410705000c00d202c01080304401c140e04000b0003000100c0301e0342c0b00d2420349001d81084c1001503664500050b0240c5032100038800d400812140010710f42c0c80030f41c04204140c03041c2d8115400310703e50300ea82039000e1450080d0400b0949040c6041000585150004000c1c0355045242e4024013021843e400d0540c1107541a2264900400d400f080c03070070058a400004000c048101e09200c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 862356465 1250 862355215 862355227
    0x61816140d0f020322020d0303050c091309021906020d0c0515011d0105060708070b070c051c02160e010b0f1e03150f1302070609080c01050f0702120a05030c 69
    0x81016900c1820b01d00c040b40f6030010901960141d031920410049030000e070f011008003039560105a890002c58000b40404d903451003c905404111011506c590600a0400b0b254241e02003000008108011089204103a044940804140b540110701d003181d80d183c0180c450b040207840191007100184904840034001d6000541c0b4800c255074009018100c03000050400d0b44002841208080041e003060b40315143c244004000070303006008440c01907078030420b41646521801d2041e991941c00c00c1d001450340c02240b14001801003110710481a0030084d90840d80c843d0350007000c0d03c03401d09075802210001c0042c1e130014803c0c814a0402844601005403081d468107541400d0032540151101052440ea0f0002041c0320001320303017211071703c410030303084440e0450300c251940001d8220130b2981d600e0f042640c010808509004403030740038051030380d0412001545c1c1c2880c1110300e40200001c0303d240050001d00c034081400a40b0000d450910f03409000402440d24803100c9040c4c400f80c1000308044a044801c00c5030b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 862357715 1250 862356465 862356487
    0x1209110d1119081b100c030c020307140f04020702130b1908071a09220b0402070807060c080c030604050c04120606060306080c060f070305090a080606181614 69
    0xa80c590060b805118441e520704005009007420054040665031000409a804a07507445020500c64074a03a410103075920781007490283e07100100e56001a515020302a40000e40d4811407000c02c07544401211203031070030102c40d000c210481c0140d68019421401000300100d269050f54040400d1100041240307c100301c503084880003551058005a0464004d00020003107080c1e0101d041030a201003a05e0305007400621408501602041409005a10780c800c00f2007000b10840d03841070303103a01009041903507280c486007000d1400d03030700c0078000b254518a031107000c1070b01c1c6200e81440f5019001000d501071541d100e075802c002c007400700501458800503040100027001c801910304000e40c035210314000301d1800e107455000340c200d81c07141d44007107541d4014413010b90842d503521080359000c09000380c0480d1510011f0800303c580e402054100c81e0003000885022903121000280f992142e90101c85032080300c4000312142c0c0d04e401e01962030207080d50808034181031a0b80954115121402d070002c00701e04050450342c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 862358965 1250 862357715 862357729
    0x90f0402040f1d070c0f060f020d180b0907030f0b1b0d09170c07031401060b0c07151704110d0507140f0301140f0c13090c1209110d11 59
    0x2228900c41140ca81443c01400390114440c0d50009480c10040c404060648520003611000390000303200365590f860400124006505403011641c19030000c2080404003020710681c40c024000903551400b9070b100148003102c00140070800d42e940003441d00100801c90f56403c3c1d041c0800740c051a00c40c0102103040b040440a50003a00000100140115995055085c02a0b44945804000242c4a0104081c03042d08100007030100440343d011401d0300144a03010030f410b00501d40d0341c1100c3c00050000a4040c0744100c00200001518014021203500540e00d02050703580d40017184041c6481e1701d8010018011500c098102c0c481090040c01c0c60b07254058681d1014101b01c001e400032501181d5540306800d160034654a010703d0981c2c1a0000c01040207840c0780c520107540020510910381c4816030014910312100002c3c0d0b066001c410f51141c8503103444500070070182090f01d0000f000201c0c01024800c4a0300782d8050022600e8202c0c0340c918814038082c043c08141c41042c0340030b84240718404020100764079445 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 862360215 1250 862358965 862358969
    0x81e03040e1e160f0f110604030c0c1202031e150903030a0605031b0d081306021f0b2404030f0506070f020304061d010c051504140111090f0402040f 65
    0x841084a5030b84458021100e04405810a410f25200750f10054101d03030070950320641503510307081240404001440846210400c01121442070042c00180320400d6040b44242015a01c244400050b55032540d10b800701303c00b04601c0107503055205c0c04010080c040c844401c04811181d807015101c0d4500381410701d410500341511480b00c0790f8000000c0083c00c02080c8120000340c40210044c140d0712450081c50300b404284000040e02c41c225110300c0004000c007460444201e100f503800320020160fa601341c00382d02c51503003011fa01003001d60f1400713542145881d803048122050005040d0201c407001085000480c504d030041128619004100200104032140120f04586218400414030707490b1500008040b840c0a00480007075600610040c0b10140c2c000c1c0450916007260340c1e440c68030011280040715180c4440002070100c0c0a100207410080d8030b400e95951007280504000181001c0c0d8450903802c94007410b20903500407606000e1500c484c9846483c18502e418001d2016091031740312000311482016036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 862361465 1250 862360215 862360231
    0x70e0c040902131509050f060405011413050d1407060e01051e04050d0521040807060e06131d06300309030d26040c050607030c0b01080d110304081e03040e 68
    0xe01b00800d217810300213a00e1300c080c142c400c5d50400380303000006480c06c13003501c40007401c061020905ea840700300000c0c0b54000604009247d605030300881c2c1440100c4d8030f82115168020b024022011989034001c00e041c004001d0181d4456103000000148107030802c2c14014800b04468081200284940e1440c01c0013081501501c0070305448418884080120420b8246110000c0b0043c4000c00521201003140422192182410300c07440c45048001000f62064085000941c00040d2000c142406c0306401c581268650015402e41500c440c400c200c10180d0a0810b02d114840c840c2d044800c451b241d603148124000d815048030f04014800c2d0000c2c2c100a24480468000740d40c012182103c072217082d903406001100142c64691504140d201c00c00310300310500803180180e40010f20102014403501c1148201c58114200d207170956150a1501d49076903a401e0301e04000744601c5d4284045100201c1298110b6445074020201814002d0800003500d220303510541440c081880300190310507444000510807040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 862362715 1250 862361465 862361477
    0x1b020a08010c030513050a0308040507050a0e01140415091d0307050c0306070c020102060411011106090609120309061501180f05120102030f0c090409150509070e0c0409021315 77
    0x102981c02404c490000300200341c005200d0f44101c012401c0851264012034040c6000d00301907699007040c52518266030701880e08500f440000245107001e04080c181601d0420a0104440505504000559858442050401c00c0f0888200820b651641c0420030000c881e07030302009102d05109003142550080382d01501c103504001a04940f503d414050307141d11002a0408848100054000030750319000207100500361482055000c0090780151112008540c13481c040310300070311301040d80544074101900c10482c18459801c0320070300c008641044d20b02c500300984c01401e40d503880d104050300384081c600c0242d05012010340700c955400d2610701a00094407806258030000c03442c0c24103010001d144011001c0c0c1036403041c024840b08056605203240c2004840c0c00d03445e220311100e000500146102c1400800d8a203101690b40043c0c806078000500c1200c41c181900c80c016684c0520003108282152030359007280c01003105002c1d0f0100f640c060007a89002d0820000000d0329510640040a00504550040f4403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 862363965 1250 862362715 862362731
    0x3070c031112030a0513080d030f05131a130506010608010e31170d1406030316031b02100221090a0b0d020d0216060c0801030f031b020a0801 62
    0x110780800d095036400545540c100700c01d65480c802d45034044c1d1804002000f100203048030b80800c0b0035001c10302409201c02503840200c0b07071480140003404c01440400c00d0078140340002e99440149082d6580c81500502003109540007280c6626141078020a0140290320b030bd140c04021800070407840f03010304406e880710106941480480641c02d10000c0c180100d4541c0c0b401d0301c00c40030940c55200181a07030001c21403a40301c0700301d14042d032103501900700141c105031020620140c10202600100c5407881c24485001c02d070303183c10041c55182d114400c104840c07110410381c0d50300005e02c1401700d40903000f0082480366403104942d0009119804541e000e8005a001007000c0c004c52122110000b00061051400d83c50040c1c0f080206441031040e1041d0400d140f80403c21003d43d0740300380c0413140303040342c0800110b5480510510100c04006286001d030f1307100d4034000c0f103d10389501a0300854107a80e0485000c401414480c0c1e420ac401415500d20004110301010b00d00006072569000c020250501c1d000100e9859 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 862365215 1250 862363965 862363973
    0x51813020f0d0608030f0720090a0f1505030c01050304030302041d0405010c17070c02010c050f0303160804020a09091113020309250509090f030c0c0f220b011103070c03 74
    0x1940c5034000004e241c20800c0900300d41d0060f9400ca0300074940c000d400f05644650110b41c102c42a9a0708141e5802668820400c000e845e210340c8804034580c0d09100030080c4600400ca8961580c880c0d004554056200307100001c22980100d01455009100e4035001d490281c0350f214111182d2040c989103000c1042e500d0510041007420701031000c01c82c41d90301e0508051403180310100311800000c2e0070384007031140320404501503900c40c070030202c24a5041004c0714044217413001541c8d40c035801201e5110082e40c40a0820703128500c0b403116180900c2d0020440070045007400d03100001040da05400721007448441d0201c400c0c036290319048075030555986000580340e1402e166640d081074a003141e01004058020707106000d0001c050700810030f890050712810410707610181000d250240da141c0200446c400416007801d041c0000034005140c0074166494003003982c0320f07010302203d1150300d8440a021900c81da010b003d801615445031314460414074204174441a90607006045500003001a10f00d80801d0000340240 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 862366465 1250 862365215 862365221
    0x1b0c030a020604110910061b0b1503060606030103080f030a1d060a050604020c210c15071706010c060e0c040603080d0b060c0a11030c060c0d09080607051813020f0d 72
    0x200005442c0340c140c85c900341d0803c454444050181c0e41c103001c81100200c65823040101607100302680500c04902c18101a5042c3c000f106100400c03920920800c8001134542c01d01406a0f030489034480c0c0c1c103600300a11810080c00c02d400007087d491900e035882e08085012070134075500b510f000b0a1600079103481d042000e080303c00d4500007403249001390b004015680e62030200241405058030822403050f00721540785900040c0c0d2181c41090072040c4280c03648114801c1c24605200c0c000e0440b61502043d0310102448442e9020007200c0842c04540e0201040e00411500c2d040400025a0381041c0c8414440d608001421682c458005594191022426030204c04052040c2581381904603443c0d81003981c0e01400556421500e40001d110b11440c078120481501c00308040c0600e0440240b00c1c40e190010750204a03903c464080d10071000030100800090011b4002c1405409040c082e5185450f001140703c0a01096003e080030702e81040103070a1000e12281135101502403401024981542c1d814500b07541d0081d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 862367715 1250 862366465 862366493
    0xb19060902090a0317090405071205060301061211150315040b040504120c0602090d03030b041a01020d050c070504060609080609060106120c020309040e0f21031b0c030a020604 77
    0x2a03a10402950805540314400c40040303036440b11300d105903000450984059402080c45541e005070038481404601d5030070001901d103a42d400e280c03c100d103071b48070b804040c26074000b8030070f80052810f0b5000950220f550b444917403c80743c402800c402c001e0099280f42c040150300c01c45842c6008164043c00090f245413900030110640302c01c840512590070039486100e0700c40b901140a0341030055107401c110801c0900c0d0180c070000400240310802200c45824041c000d05040503089108901c0c180c00440d0034000321142e18460341303040e03000f0880e01c40c0900080d02c0541c406107401401d84a40c080c00a00750341d65018000180c10f41c0c0ea94175a030107103130410340c1e840c1503405044c2102d583c2102006024040c1c1c000b8054114140407600442c2d1403d6202069007180309130003880e41c10905140102d0710442c400621100180d80c19400c03164041c80031001242c5c50b05441c0341000c070703c81c02000800c0020019080900c1c01d00d040c2c12105141c59100700c11503156070700c004d02e1400560000010030050000c01240014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 862368965 1250 862367715 862367729
    0xd021e03040b0a08270a02010801120512130e0423060f130f02041d070611060a0213050a030501060f0f030201020d1409040f02040e090c06040905090a0b1906 69
    0xc281802d1801030381c280e000e040411010010280002140300c03410314500068102c40304400020f0401c0c0208042e100da16002080e03001c503182d0400045c0b018684405041c0d0307150044040d144500e0f04401103089540708999140b0328080a450106800c160840b0050040d4410841e804040c00d40d045181d030741d1000182440c806030041e104000080180040180d800520b9000e0801e0004003490510542c0c1c04907a4044e4000d45406e05c1c40544106a410344c1030400b44030300c12581c140ba50745800b100c3c000114000300800740c0004012890500150b0003600821000c0201109415107a01c0850828240d40d070054503983e44803401000201d0540342c8032400303083d00790446a0b43c203003540c00103907175034000843d080200900c2854012007803607071109440714010014400e009804402072a8000b0b07400500955030f4807403240d00440d40000340080c034403c0804018224a0a0915003881040106001070041d081d5018510840e80010344031110030f40718040c0000001c20700502c13803088404440081e01301d80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 862370215 1250 862368965 862368967
    0x905060a050601141e04060f120510091d0d0f08060a0302010e130605040501090605190509010e071419021e1e031c0b0319020d0b040f050d021e03 64
    0x400503036480780c21080c9480d050404180d8801d17402404040710514100b82d039a4102c408100401c060f64486041c01c0700145035580d140c0c8000318820040100e50f0280d2381d03880352a201042c104031700140d40c0c100703001015800700d5001c10403010224607810104840040e078001101401036400c01c54005c118160010019228a201e60f070031980060320114a942c81244500306a40f4030b8030720400325400400161001900901565030f49a44200141059004051007031000b0481001d403814951a0401140d034001c0800d13003240d280904d090f94404019100388104080d50360885648034000000340a5140c0c004001e6400c000820342c002c0c04d01d24451580c0d460100b01600700a403080000400e428011095850b1400b0400c4030403945145101742c3d111519030549480101c40b600320654007103074000c142542a00e1105845800140100036910002588069100b0903480032450b40080f407a446071085d890043d8040094032414506009110220016401508401e1a850500d540d1a440107a800011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 862371465 1250 862370215 862370221
    0x61517010e04021516080306030f01020c060103030f02030f0f13090e0d35090d020303090a0305071a041407060e130b0102070e0c09150a020a030807030b03100905060a05 74
    0x584081c890103403010b846421012400d03101d40610008488070000d603450480c0c460000743c5021046030300102d42461090241006083c1001d0040c02100c5000604002810b101d80c00c50ba41905c004440248003000c602c414004003825106840080500d5000200450f0710f410301d07076403c0c0406070440c1c1c11424149003400920645008002080c140c1120542054000064882d1403014400703a501e03802c90740c2211004030b108503850104801c84c094180c0f501035034415041100281da80780f000355a03540d0103521001c402e0010a1241010b0030710b15102d1940242d1360124150f4a086c2484c06903401d0303030185012182d01c0d0230035804001940051405052607040f006c59407000443c502d1007480402081c2c0d465000517070308cd84c800d1110f40050007403200d01c10740c00c0c106140034030002d0b08035000c030034001c00d500c00100000c03030810002d0380c4800c41d040d8010008000c3d6564111030307a2002808180902da05e408054a5030358040c01991400786064200088505c014141703d45481e0b4007600446120340382c81c4c00c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 862372715 1250 862371465 862371479
    0xc27130e03031b131805130b010e04260a020706080705180d02030a050a05010c02030301033f051215031c0e090103060b27060d02060c0106151701 64
    0x1a00c3e4405900d41080d05003411100710200c5a128215004040985005003c50681d20314880c280320014000400c103d9030340d0f42181d020207a003400d040502024034441c0104080c00c10001c1c00d9a12038070810240e10361048296520301200240d040c02810a00080384c40501c6030740c1042a00000c240da845d000c52a400d01400240c0305114590700e40071440c07185071030a01b0b20340b40c0040d015026070740a0100c900440081c2480368480d05801812103065081a600c1c0501da440002981e069981003c040b0880080000c00b4100003c040340c45001c0305800a00c0c00d2f0382e40c402c00c4000049091180d11419076070542898480b4004074001c0805035480401e210b0480503032070005003040075030402c003110110040340c507000b03a5564014003d82640010040008810400b00750045d170442c5070b080c1c61912500e45220110040b960b074542c00208003103041b10014520346040d130009014240060f10032407401c60381200d000c0c2907034900d800c401040c510341c00a0040380303a804482c1f0b595200585003900029410208 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 862373965 1250 862372715 862372717
    0x60102010e07210203190303140108030301140402070f0f03030203010614070f0308041a0907260a020103150b1908070c11090a020d0f0c081303170c27130e03 69
    0x50740c3e000d580b0705000d50004540307082012030450340d9014071980480009140087c00781909903200c03041e0802c220000101c03031000000f0340c5e0698003201d01140040c2d50410502c00290000351040c0c0c2c06d4105076444002003180e0540703101240303020383c0d0003580d40d44c1000c0c0040c00c460303003440011407590402c03c043d1011039180d084002c00190b0500c6d0040302038440c4c0c240306091046101e29000724400480030311843d000005002c2c1c0c220b81d110126100303161400310300b045c4c855903219070404050304580300d0100198882d40c08108020004840300700081e4940c06070981940100d8008200300d011000a40d0900b034103c03038100d80c0a5150304d010f910003180d5660703610070700c110b40b1400d501500c00e510125030f00c00c20346d406481084103d100100808100c0c1896100a40460032074003000c1220b09c0d010601917910001901a000e0b00744d1644013480b064508150540c200c02006840c400ba018840d00d02004800954050801c41544000b010f04c0da07031804000c0c01d1395a50803d4154145482c40341030040764080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 862375215 1250 862373965 862373999
    0x90f060516030522030c050a060507020f04110a110610050607060c050f0f0a1d0307030308090a080c061602030a120c02010e1204060311030402030a2315060102010e07 73
    0x201108505080300d14055446010b180c4c942c10010000f06410b07185003680c240510704880c05003803111809607480041c00301406043c007417000000c43c1048140c026040510440c86480070241001421000382200c00e02140c0081c01c0f401c0c001081c0c0800031591440400c01c0a81181d018601504002d02d4200020a035200743c3c48001d21281d01e4940940c2041d000c0c60070340742000c0707609807501d0790744001264119099200d4001040414682030000c1003000b0031850205142030058000c001e205d0070b68400361902c120051603494248074040c1d070703c0001001c9401608400300ea0b42c1c000c0c081401c221050b01d41400001103214119030091121400550b400165059003070149400094964103040f0101d01509117451120f0a9214004a40c500c2c0c1748110014803c451880d601000704104a07011040d252105440295056010042c09404103e0191064110b11550705250200e0b0b500d0840180c20800000c000100042002e820422556028003c549440c16840040d102c068100b580c0340e10160340031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 862376465 1250 862375215 862375237
    0x7172d0a02070c080714120f0304062d050a03090204020714010209013504030e1509040f0204080303271204050f040b03060117030c01020f04060f0906080a0b210c01090f0605 76
    0x4016200140c4a00b8481c440c1d02310f00c900c040d079964a4440c54003821403403494400c4040a1f0074440030740e0000d040410407402041080d40c4142c900030600804401802c2c070070340c2c16a03205500308400c0e0000b0b1007010115000051000003d81c90340280400501000c603202e010041c962641041041c0c401d000c601d0000c2545030b080f41940581e202c504084664803020540103801040064419481d40402c80c042c0540d51002c031030612914865002030801c0e0300452050800c10350007800030a05c140303800d82d10000038014030044c02130b110280c000103e140070003060341039285d030301d0011303060255080003140c69400791000d030f500f0301900381e01c107002c25036a20051180440700f000380f42410950a02c180121801d994101000703545503040a001c004096100d48100000300d62401c45014000e80580f98660848986481e0882d523942d6586000780903008114000ea8400e62041c0c0d203030240002c2403244c1036412803404c0286812000840054110074a0740c000012000b22450300f04001c0381d0101c121440c80c80c0b0b07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 862377715 1250 862376465 862376479
    0x110108091b09040311150610021501030b071404030b01080105100311040f02091002060117010c0210020a0912030c150b030d05090f04060e040b07172d0a02070c080714 73
    0x11400c4c00c4500503ca00e010001e07501800201405a42d03414004500071070044070308104101161005903510241008042c6980e54407800400104502c1c8210aa02411600f8109603880401044585542c46034004440c1c010036000140140ba400340300b00e40c2e002c0594100500307010b0658403113100d07407190301c02e903244110b03201d404001c0488400e40585a05980181041c1d0000741503000c00394440100340503407620802a00c91a0040303010501a60300302010341d8000e041000352042e1060080c0d404040703800203119070307007100154840c04400c082c290301e8040e607030300703075850b6050314100c1340f400030b141454404981850010411658003040f0070309406002c3c00d2666545512402290240403510001c83d0700c00c1c54140d0004041030205005072159111707010300081c6907503c21043c0c0b2010581c003080c00141003a50005851054441d101e0000c204001c13100c840102c101c60058660420201d8001c0601500440e04000300a004481707040030b030048038080c200c502e0401405420584405074a0345c803801d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 862378965 1250 862377715 862377721
    0x312030c0e04150b18120c0a03032d030f0c0c020a050112090f0507080d05180d0303090b0a15050609031011072001080601080f0c0a1101020403110108091b09 69
    0x507500182c00040c001440c1540c0c0b17407028800c030003014816480c00700313018102070031502010a80c04550181065401445414004d0a54604030f50030b000c00d00e41800301d004501c0c0d130700ca103c030101d0360643c07221800f654010a080340780c030b0b18400c01c5d165076511032000d100700000d40b4801607903407258000a940080ca0040215041c64886801401da80c440252010300c011140a0601070f000c100201566404803c4685007c03c4000881d064490f0904074201010840c81c0768459140c103c020f100306c14001c2c038010980341026104d24075401400c1d03800d00d2503140d071a030540b440323030000c0504600208422901c0034148170319400071903103419a154801c40416656020060350310303440000e58961710b41044c801e1144201c02c020305034003405504081800b05003454000b0303a4540c80b42404d1485042d030305002c0c02c000d0300d50a100d40c40541140f0302c220203100031545400d80c5003000b440544011030007890b0403580d05c2c4110001420b202d02c06011085980c0003c101102c4100d01920b016400c0391041d944a80345603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 862380215 1250 862378965 862378991
    0x20301240f11190f050c09090303220816020a1706060603101701020405012c0d0302011b08040c0611191b06050d0608010c0e011b0b100312030c0e04 65
    0x70608405910442c80283c01c040c0300e07031940b450600384d218000300c403028002c3c44208090707000c04507000d000d558400c0002900321810410b101c0000d102030020420f14000136a601d40c00340d000b018070308803100c0104c3d407100306520f040c4030f904004000c484484a100060398401035100c003c0185041d008420000204260f0300d01000e081d001014421515034244e40aa03403c64040d510a104250000b0b00003044025140c0009100308512050031018107914030107203051003003484200c9400d03025035507188000c0320041c0000081114540c0c0a90350101c0a24003850800c120141d15040a810030402d00d44840300e0200019030242015062b03440314006220500d08509808112a02e8049640e055a00003c01540001c090075071900a0842400402d17101c00c29182206d183d401d01200240d484540c1103125409078041c0340503c0e1040305500c3c1c4881c4252079182c3e1038181a10f00d601e064844510400601069911010b002022441c0501c40031108071401401c1c0802c049006100755500d01444c001c070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 862381465 1250 862380215 862380223
    0x4180b040807050303040b010f0504020a050a0c03030e011d060c031b0f1309020912123112051e060a1a040507120c21020304150e01020301240f11 64
    0x750f44401101d03982d103814500810300740e4080c440c12120700d0b00b41c0000f143c24030b0329009960a0800681c0c4603418000040d10071596607807585015000c0c19a00c08004642240130301807001c4c9480e10392083c2c11220040781c0d0743c5241c403900030840c000c408020b20901100080148010010200c203080c1e06848030b80c1900750456510070500000e00d001103c0d2800104000d981c2c02410074140700721641040d044000149070786135141d00110300b1440808204070060400241e400f10a0055210901c03400c000ca000c0040b029802d040e00195184110304c076120082040c10041445003686100301d20781c54558202a80c2da4401000e084c00e00f25944903c2c03202100b205080b0301000e0490b0040090090341002a00070300f0002c01200b85408290800e4080c8200500500558001c00c40440c003441e9044003120740d48009400c0580104c0d41c504080904040007146c1d4001d00400301c040800040e0f507949484824600c802c1923040031404117041d280c0856080d504004110f40421060a00c0f404040160304040c3c10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 862382715 1250 862381465 862381477
    0x717250309081603020f0103020a0539031207180302060c010b0a051008010501030c0c050d12060609120f0602041203180f030209060d030e0604091d07050a09180b0f1504180b0408 78
    0x30020080d05c10040d1883c0c000080462010841c0c04cd00425041c0300c40c4517242d114901442001d090100040703040c003442140100e9641e0308000311000c200b0b4a07075002078a190f0000d120355216a4440f9030030300c1549000c0342c42d030000786012500d050100304084005418800140301e0141415070b254804c0403500d00402404111f6a4407034151103040d90144809400c1d2419040303800182032a0a1004c58010300540c0c0550684801d10940d401c0910306603510510586009800c035025502031200256041250400011544c441c0d102c1d1062810085036000100e162503003c1300300300358140307020005038a032201160b412100907218030f400d11b4000d003030507100222000410703034109000103400241543d65502070441c200303d000b6800b084040f003203c040ea5440e20f81c059182e0003210f04400b044964103541c0109610103801c1c0a421031800583c41da00181700c01107403070004021410707080046001c0050a80f41c07064008480400803210744040c090704038070704004000c2c4540180b40114051241500550311 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 862383965 1250 862382715 862382737
    0x41809080d2c01061d090a0b070c050f07050a17010b120a05060114090c030703060f06030c1803171c02070f0b0c0717250309081603020f0103020a05 65
    0x4070b6006482450001c0100c03018a140307800b514180e216100c104180580e004441583c1c801c038000c48030f1000d860440c2c42014040300040d1241040002c001040244214410b07500c03078170790380040225410414281454135981c141d058100ba4014400e0b95108500301090314000e1038131048049000070b00798010420346c007075543d1082c0c19000c1641e40890015201c1801d91041c800d61f11513984e100080c0f1004952030000c4c9511412400002c2c1ca41104400039540c0800180740209400e5910100d9803034244150b0007140000c1d480340d0303101c030210360003404241c952004c0b43c020306010b52440d00ca580c00801102c0d4807034001d1f43c0c001410081c4421444a02200e01d110700349c21540d03004946462401c2c100032480031900c1412107000640641440c1c4151f51032a81c0100115000c0458640340e0641c0f5880216001c00300e480030111114144002007044855521a46400040340e0403c214140741621600011441d04580c44d07080c00180c5400c1043d900411013800e0145e185c2c10b2000702950140a0309003802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 862385215 1250 862383965 862383971
    0x303090d06050a0f0506100503070912080304020103111e1e0d0f1514011b0b16180605040909051f0204030b0a0c0e1504050406091a010302041809080d 66
    0x1807100300da10203401144415810440b07945100c00b15070031742c1c804507051a0312130306090300d00b250540100000d550000b0b20346451020251500c0c42034512403102a000e0f6982c07075000c0100403c558140c491b003031a081c18850520704081a81030380841c01c003c00091004482c202080d45a6000122101c06d91503039400411261a1944c02d01000020310b054040c0c1021103040a100b68070500000b60a41d0680740076040080506200303100541d01e05190140030030302c1030306d4128200b020540140b240c80c05100c0c5140b51780c03c1c008940800800c010140c03508624200b400404c100400d540040403103003221490078012440c501507040580c2440e80d9442c640380520f8140301224032140c9a64010300c2540c0c82050889101d4a075041260122060428100c010236584050074002d1b18000c14280f800c0e00000d14080d280039200c0001c40c0c00d56140d64003a151254071805620b541888030120700f003804a0a1a04504040c68034022140540d003100750241542e40d02c03510b650512242d07600b21800c9000c0e446081c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 862386465 1250 862385215 862385239
    0xd2a0215160501060905010e010605180d080702100807120e07120f0b01090b0d020402130801020f1206091003031805040207150b09040c1403030705070303020705090916090b030309 79
    0x7050000040011903195103420700100c0c80015610459050314810b01c005031050703090040070380d050b90040c0d5040d980e00510705801e0046554880c07620041e148225a00764a8094500c10f22159042c2c5e50800da00788820001041112070344107000c084803142d03010001c0340a000642e1140e00b045495000716000c1880d8540f42000e11100b00300d00140140701c0c07802031440784c0c1c1e81c0c49550226000e10300165406840c0308032480240c5059005040050041301c02002c03065a40d991380e60032a4001c0769a40c00e0010301041444601c00070003d5682d00c9032040e20b54041074a400d610954408407180030003402e001945400c5045014100040c0340500b5020b003085588400a003080020912241541d412950402c0c03007807403d40c00c4c5209003070301855214480d150024100380c0701e00f2120000071510354252006020510215108001040085009402500c6494180f01c01c2c44030001c0c0003050000c041c2d01254848442150000d078680840b0f07030966001411000031b50009003580309070b0302c41c654441c0c21a40c0c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 862387715 1250 862386465 862386487
    0xf0f05090a03050c010815030c0d05031c05150f03031926041104090c0b0913090b0109050f040f20030610060f112d030d0903020d2a0215 60
    0x5100130461090302c91101598404511320310340d5070702c003542c95003640151b02200701c0c50600016001e1580e1140e0180c070f050401f40520102060a01d24038802041c0c3c4070001e004d2001444c280081d0150b0781a03460404da441d5450100c1d940b40b00d0480144070381c4103020740e000035807441800c2940c00b5621400584d030342d061003101001d0030b0700019507042e80c409042d5040201c051800d80724840030300d035100c4001c501c40e501d0048400c0d46508000d074125046005400b00368200c808500c03908401502c2001d0100c03d9504002c040340440d80010b280b849410218000d00000c64245030388030341c409900001200e0380d1a80540c20501407031790403e010390540300320700c14411800074081d440300a645159079140c18140418100715080d00c50f2800486150b003280500d0161a140403248880001c0015001e03130260711400c2da014590341c000070541103480d40c1c44445400b010f0f03050007050b180190034900040b03c4c0c0300116000e03168014800345845101c0c0000449021901c1e14600368030608240b207041d42d251108905 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 862388965 1250 862387715 862387723
    0x1801090212010f0e0403121104080f010507140f0a02010207200321040e06030c0d030207031b0e0a2301090c0219030503070c060f09062a0f0f05090a0305 67
    0x241103900d01c07040000324840c2c200307030007607421551104052291074507903481c2694071416042d000241b04c7c0d15141020440200e40c40104000c0102c4c2c4018480e002014020070308644025088100f046034800d21009052407003c00e460500503841200d50340c3d02c4907140c06034024801c01320014040000310007668500d0000d03048e0350307a080c0030640a1b180c0c400224446540704020642040300389080610062000c12000801c1c40c0c1c0c080340103003c490741c00c0032140c0024031105111104500607403000c0b00500800001084503010b109040691076600303400d2210401d4004070050038440216039403640722908052050070b4120004001462100658585003108080d284900d91180540b00b082105910b070450980034000d601e4259942d10f085890f120800c9401000c80c50043c1c4004c2e032105c8000200e402c0301e1007460600351040030002900a04400c4c0c0703c000060748039241e203182f180e150302660400e80240008440e2000c03898281005124a003040d03d69014030314600b5004154601d0110405c28001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 862390215 1250 862388965 862388977
    0x1d030a0b0603061e221403070309080d0e040e0102070c08161202100c0f06051603060b090a14220603050c030d0c03121e150501030b0303070803040218010902 69
    0x90240c1d0007559544c8903800ca413003103240140c60300042810008000c3e05254400c040f6002d04c0b51000ca0074042a61200c0407000a11041c080782ca81002078000b04041d00550314600809002024012f04264948054441e00600400f240115103440088090141c20740c11039030890342c844220550140c640301c20320359030080301040c031703010700d100c62004030b803143d262000e52209960040103001042ca03540c1e822038062001c0071007140c21039014401e01001521a00030644280441c0306120150040034800805a803856407084501e08010440402d41d40c07030b0b80c240001650560004ac0c4400307608000031604071020f076004c00c0c28207045110f041056034926000740c01124040e40840e9190341e041000c00d42c881034400303240d601044c0d062040340002405244203140c0f81c85880380024000040c0144c0c4011880241c141c47d0845690340700005100301082c019402800e028038041140c8407a05021036502c0c480c2d8003011b440144003000082c02c5650f1010090b800405c003148000481d40d6031450540690042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 862391465 1250 862390215 862390219
    0x15020c030c011d121605070e040803060f0d08030f1b0c0708010609150326160201080702071d090109020d052b12050a201e191d030a0b06 60
    0x1c0303c044848440c000350716a0000e00241e44c8a141c04410400403055014540d021100d5004410000407000c085014451056004504c3e442c0d03203141c404100031300c4215641c40c5610480c4412091b6010030040d00950340d010403909140010350b01c030038051440402400b400d07640280b07800214030306001d5001c140602140d03030315002070184917102d14000054400300686d2625100460f2810004148200c4001501055025803200320340400600300c080e40c0c0c04040038120130f48016a000c0110750b405090702d039101d591803014240050502d1880310a155507000c1154245444102040d8015030079404a0002d50380100142c0c9407010900e030103612412006000c0c0c4411000d0400c007038031150320098004407410503650340e402024442c10120000c01020b042c0c1c00e003865070740c0140c140000020465550114101d02041d8135001640c0b5031002c0001d0400c010809504181310218030035841028413500813115082004e00021150821000540803800096140c0b0840e14040705011080c40028014401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 862392715 1250 862391465 862391501
    0x2060f120a021e0a0e130207030206070e060a0f090b040303170901020c030d02160b0c0405040c0306080c012102030c09040c020319030527030a0905090f010315020c030c01 75
    0x8010759901280100e21154000c0c54001d981c02090006400041800507000e0030030b0f400009442001c100d0140b90400d00640007036000840a05054042200d15440b0783c0714075041d848000d40b100030070080d0041000600520162800101d8098060060741c00030b81106820680c9440d0b4a0800528a20003801c140180031045004140401c5042c000c0340e501485a1005501d000d8404200c40c0080d03002540000c20707042081e0210780001e4085002500603003841340440e40b21424101007000300c0301c0b00214030303061516001d0100090003005c9114504c0320800d090800e01171819207007109092000c003040485952001041040d0000300001400307030030606650401060002c4c0340c2c140ea1328824200000018222110781e402564400c3e005681d0281c1c840709000d65060b4500c1140713400c001901c03c4070340ba940000c201005841d0340000510003d040031500003006042140107840700c0700c0107010141000d06640320200740c4132101e0301101c0000d00b40c0f01c11039689480c10754240e4003c20308141004000d100e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 862393965 1250 862392715 862392721
    0x29121008030304030903111215060103050105011d100c12030912050f12040c12031205100b1b03090a08060f070302090303091c1a160f0f0e0a0302060f12 67
    0x31000094a00c102d5041d15613100c650305644628080407441c504080c0e2000341140032401c0f0700c00500c0543c803845200d0f81d81a00c241459000074080c0c0c0e0058114504210084900c0c400000c81034444405003241600d01208296605404031100b4034584000740205046d0f0780e40820580d03159101e0101036009200e40d8000130f01e01c103001c540d984241d403402094060140b11295943d1400c0b8480c42e0071510600c40358004a0b50340080c0d104402181e1416000704441d0b118131591024180511640140e4a09404040e182008082040d07405900b40340308017880008a141e44000302002125801c03200140180c4c100c03540d8400103a5500c00c104caa00541201080c041000303e4041e00aa5182020040c095030404031004203000e90492010301c1081c8800c400f01c18100420004042c140d080b4580f0701405200d807034112586003c0340c1c41c0c442c05000700060107010300d0391580e100102c01403182c1c0625101c803205c5101c10008511064a402c065400071000610010b40e28070113000f0b240d211089066440255 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 862395215 1250 862393965 862393979
    0x10f021606050a110720040c050c01151a0310120b01031a010303080c0906070c06090305070f050f0103020904020c060a0219030b1507050f0f01020418020a09291210 72
    0x28031001541a401507080c0007000c00030b00c0702000d01e024020324561030303002d0046c3d02d00080d060f5041c0d0424000441c1c4000b90751912003500b0b0055294100e50028054422490015075112005006c400046040c1000c004514905a1106240c008140e182c01800c103451540c01c00c034800c40d00a1004032104c0b040b080d01408500b2181c0d01f101c5c1280e80640714100c0503983d0f07420b40b8410760300001c0403075031101c4d040005074001095032010102904859992880703a9085141240c9042c40981100304101c5180c0c03002c1240e6034800c078001841e0309081ca4050380f1903c001d400325000e401a04c00d042010700445081120036031080c2d0141228086040342d26828540d040029411140c103000002c0d04541c2852243c00b030018564002e08007140304200320345840406444103418201100c100303040701c2c1d4000508001445904980702c1081100d401c0c11441c0003640d96000c0e1451080d0311800107540440d10800d480c103242074a5030741d036402043c4401e41d42c0320078500082c60031000032607d510001650284c0801c0d90 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 862396465 1250 862395215 862395221
    0x60206101d01050f03010b04140402150712030902041b1805220e0c0306101d06060702040c0e0307030b010e0c190804020a050a15090e07140903010f021606050a 70
    0x1281c07606403002590811007444440703d001512a60559295050b0045a407500d1042d03219411042c1c002c0e5090341000e00c100030416502500304043c410003808a40041007803112008482100c43c10002505056031020502520030040250303508048000700300e030300c01d030014403002413035980300504265030b41c645081015042c3c080d410303100c81c00c02d4115680d101d1440c5501688100003c80103d030702040d112000a4940030088400702c81d00b0f40c1000c410052544003441c016a0403110301c80001d1079141100105806001d8010302070310568842c903111640c0707070007801100c16500c800b905581985850b1300703290600e00f100784906030049207840001040d901101c0162500c4001d0404000c004004003141113403d031038040d00c01d0383d1004401c40002070581e40c10394904001c0000c41c0890501c0c00c0310036005002c50003075034081c1c01c902c2500303010004e4569000e282c4011111000c00b02c15107c407001ba001c2401040020140c80e5030910010304c040c5550300c2166114200c1c3d12505c410b0165a450050184c1a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 862397715 1250 862396465 862396499
    0x19060b030f0718120614040c150503060d1b08102004060e22020307030e0d0c030906051e03010815010603140c070503090306190b010c050d0f02100606020610 69
    0x103241d0301488180142c0300c0c542200070b04c29008000101d0134080c0b44070041041001a6422504111011030030441c050100143c1c407c50302485c01c080d401d500e0030b030012404a200008004000d68001e120820b40d002c0320700300c8440501542d07400c80d1000034031000d40000501c1d400c4031280801041e0f00c41d8a003020425003c84040ea5596a50003010032030381020301000500c982640d401252090f0f98581c90800944003039403140815a83c00700e1064030280c001410aa100d410400030030140105a00200b40c0004c80c500498040e40b030540c0d130b510810440350b58105000c00910303111980000000072050000144a004072008248181075a6030380d200c240c0455100003540150f52840c17200080c80034040c5005041094090800d45e4031f4100302000180c10050f088030119103081705284085590b440600c03603628074410a08002d50a01d4070fa0b202c00365148040c2408404108140403800d0f10746100744822a80303500d45101c103201040c1c8940010b91205401c45071541640029640016000050904900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 862398965 1250 862397715 862397747
    0xe04050c010807110d021b040b0d0b1306060308030403030c0504060e01140d09060905010c0311092b080415140d0e2401031208040206040e19060b030f07 67
    0x31035510140c0c010b580100009100d601032118004030b01241e41420b00441c1e040320040e81c040d16810151380c0d08112080010744030300c0e008038a8a8404a291f40f20180c5100707a0a030030081503981ca5a51030f90380380007140702c184014855810044c00008100003200a107001c3c038825142440640000c580489860040d40714410024980c00c0c0074103241e50191300e000b01c00b51a0003005920b00403002503103a040d90b0310f07002c0840e00a0b42d5005800c09008007032040740b03c0142149018440100b14101c209110301500c00d0603441016500c1203401c80c2d03800c8900da030140450450b00d20700082c501d414117017500d402c030344940d6417070580025201410030310868540400c1707441c09210070f00f8622503901081c0101092842c41456103e0031014140c0c00c41403405040c08420a0301900d0b48642c15440c10030000480d654440302481080f07024400165102c600340d90640c0e401c0800c50030583e40d0036000741c00c000f20041708211000d241c1500403548049001c0114481c650900082000303031504e9404440c644044810f0725 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 862400215 1250 862398965 862398973
    0xf140f1b030309030604082a0a030207050405060d030e0f090705030f01060206010f1721091e061204051507031b0c020618032802240f0309100903090f0e0405 69
    0x1c000031f20701006400fa20000306407020381b4043d596a4549070042e001e007640c0065020701c8642c4101581084402e028007001c1d40d00b4840e5040070710124138904840388009040c0001040e0301c0680e615442104d038a881802050b174406400c02042c060f2040e4416107548803c1c6041000100e007150002800754129500090143c00b0b40b441d0964007071551718039020701e14250040144004004070024040d4003d122440201070703841030381008001411410950310340ca6807070501e0507440702d070791020240c5017031039526140d2854540c0c0300d240007824200445850030315188440c041c000c4050741076009501907050251400340703070414003c0a03203951207030100007940b040080003104840100901660308911000c3c048404540e840920580c0200080681c000388548002e044000d525120500a580c800080e200203003204a41e130b50000c4510030302c00503540a09000011688ca100204640b1001c0001e08400300080d60300c80c503004119081c5807091200c09404d2110103d00d41c8141001c80e4050b42e8400020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 862401465 1250 862400215 862400221
    0x705010c060513021801050307090501080a020d02011803060b0a0b1e0a0917150f010b040b03040201050d021201140f030715020a022710030f0f140f1b0303090306 71
    0x141c1c00703071000414102069890b80d16800040c0c07a480c801603002c10517921031042c59030500c1c050510300340749030784240d03903807070901c0010801c3d0078010070b16100d040c0c2c06075040058500f0038001a103001070b003e10b514003e01038840303000003403020552045681d220229890b540f00c40d50f503c80f000950103959140c2d201071071b5403103c44007100c0231080103001c0034a16080103101c0325a81c1240450812400c5040d1700a03070403244080980030048280f00c0c0d0300510340a01c811655040180d00311507030107a4082d03c2180c2500001140c1560700600a4550060b41c41c00c065594502c0d8624a2650910a01c1020f81c1c1e8144102d0000c0030380350440300484e000c200603005150041c501440046503140c045a13100650258010356005038a0703002d400d449403100c8001c40300b42010341d0800d81081c400c0c01401416081645002840021103064505100c650071062281148481c4d050505080310b6214501009200b003612446500c040441c040e0b41d0340c0c02c80d4661740c45c401d51641c28161a8403e1085d0982e06401c20000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 862402715 1250 862401465 862401473
    0x100c05090f030705030109030210321b04140103270602030a0e250b07081b070807080a030e09010b1e0d02120906370f020412020109080705010c 63
    0x30794441910003030444402d42d941d000130a00b121402d0030f00f0390058012a0340d07102200c1c1180a00b15009080001e20074250203498072404007161501d003407680c2610464040381000340d4075010052487c9140600a075500c2e42d682101d104105d0091300c0a010070b041c5188400c481c0c460340701b103050ba08039180c141e00395400c4a55800c40294030080400340da40340d40c0d4103170400102d010041e450508a4620740701505101003800b4100c6186141c0c00a10380c2c1c4801c228000c0061a00c1061300d422240360241003030202c8002104034280303c80c50304480020b200d01040090760701030008010000c40e0180d00d8280300c0c41e03040c1080c004441000d005402c0f11070010000c508040f5104440302802c0041914034600300720080c088401a81d1040b00c90207002440c1d01d061100414050014035040100c606100328001c4501c848101ca03034140e0803080f082860401c03507160310140c0301d8110852280300024119561034960740e071400c040c0503d1038242d0000e0259880464024000240c1d00d043da40c058555140d403401943e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 862403965 1250 862402715 862402729
    0x11a03030d0f24031a0103050d03090609021008100b0f0703180e0c07060f050f06040c090b130806070216181103090a0605070f090509090708031902100c0509 69
    0x594000040e41c5024580408210342c0c4102e8103da585107508410500d10b0030808945054142c4d100340c0d45894000410024100040d80c0000ca581800c0c0403441c074a10703003400e000805242c08065040840058204140d96012030100d11071142c004503248102d4507010b654000d40079144091854000030003011010901801407030b0b441e04502d00c00c540c070058586000a80c80707442078800000070007000c1817030801c11146000721045980b11500401c40c5180c10680c408402c40090003450156654180e0019801d10a44042014046019006581e04031051503140c0c1e00925101d02955401040081003c1c64408907440f002d41c050070180340f80540c01e208080003c4041000d09051075a5134895260b048001500690f01c1121002c2c06030030001514209101500c1004203500c08004400741a01445900256800c00f9190262100ca010f80e80b110320441c6050001d4200c4800c510010464100c03010300918101d0010a00303909860743ca0024030942c0d0b043e18002106a00400d6082c4524519828000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 862405215 1250 862403965 862403981
    0x160c0e0f090123190213240c0b040f0c080a08030a05070903080d050601020118060c02060709050a0e06032b090f030b0f04020a030c06030209150901021e03070507140102011a03030d 79
    0x1a0010301d014140e203808400c6e400f0030750010740d82450b107141061a00045810482080c4e41d0b508064840d10b480e075603481900301f030041000b0019003070260643d062104c49603400024106560454100c1c08160800043e00d403c126010780d1903904140c0040c0c0c4082c070401c8d01404032540461003c0c00c10941d00700c0c14014010007000c160440d942c61542d8101401e01e04d80050500c3c2c014000024500d04800c0d00900b005002400c1c1070034440300d03030401c2050f40c03100c3d0350842c00c84180100d4400d151321541700181c1002c1c0e1305d52200340b02007140500072960002c4070011103040304103a100d02144540d11b12050b0840c40091101422990002c40003402182c80c400c80c0545c06480204040e151075141d40d259800c2d00520341007040000d50100f40140c01c3d0812417200c40d0515000c2d20a41c0c14075200c580001d654148941045020b0b01c1500d4105a000302c041080c2c80740b09600c1819207a074261219078007000e441209031745900642c20140d032080f0640704080900b85102026000e145000f24070950382001d44241 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 862406465 1250 862405215 862405261
    0x6030f0405160e0406290f0423220201020714060706050c030601020f0a0c0306110418020d0b100e15070605250206070203160c0e0f090123 61
    0x50b2102400c241d00610741c24015115042c000301d440d00307060404800f101c0140c040640e17a140c0d10581c699410100d12401d15004408844050083c0102c0c00850003038104403106013002c80d40070804072002104128260b1040c0c00c0f211143d9803060701d1200f592155522400007a0260300100814012503040120a0b01c80d000064841468103010ba52101c040301c1d42103404040744c40c004014010a0740e814084800d0b801d1840c030041001403030310b45030342440f503040d807100402c5a035565060781488500c11040d0340003415000f80c075400c2444550601000383d84101c40001ea03551800c02562400e24103000303c0da05001c202ea0300c21070000407881c14030400151281300c0540b01c1505004102c0044c5003400341a11803591840c855040040b0705203111a440a1140100203540012003040000c50380081a141100511607498005030300302c1c14080d03440d504130b4100da680203e066041112040910141b00e01a010080080100e42502e18406500054088504110301c10346001704408503c0014215840900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 862407715 1250 862406465 862406473
    0x11406071e14010606050f0d021b0304080102040302091b0a110c190807050303040b0316140f03040b0a02031e0901060806100e07020601060903060c030b0316091a06030f0405 76
    0x112104000510000e0101103445034074002490100c0d039004c0c01880e009040ba41001c1e400e141e050103544209005904421407c2e907408550882080401200c580c441403894043e69540c0b80c030f0b6402a4084e50003800164001c000314004286981514100e62038a0b9000900142c2080c0c00448110b5400c080a07482001034403404580705015a00c9001114140781e1180d0445209480e11000a042107482d50207203201e50014401002a000003104480d80003810107929094440303901805e94404413007840d5201481004a0340c0c4800d4802480198015401074840300c0480e0394414440c0c0681c0700480c0c40c04d13086041302c0c041041c11215000c07400d03040043e0a00101d229600c0c3e201540c41e10004841408a88004030410011059140562900518144098003856040200180c00c0d1410740c400140003650b180c2e0f6103191188243d0040000020003402c2d51a08006410340e0404c0e03480600910003803074a031540401d52840c40e40f0310100e0314100035003100d08507600c2107c0546858401032003501c05001d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 862408965 1250 862407715 862407743
    0x1021b0f151903180201090533181509040f090b070203070b0f010608130302010914060711030301150c051203091f0b0a090c0512040501091a01140607 66
    0x300c6880a00b40d034080014021400b1800b012004090341c4445801a9459482d2000680544d0344040501e043c2c40b000c0d42d2881d0800520718140288410b4040000d08640c1c1030132013000a242000010b002040b070351420340707080c09407a00070003442003401034200201080c104500d45403418a41c0091520005400c000030300340c4190b031582c070000c80c811510940140c200140900400a00c2010b06401100b13082491b40300358104100900702080142c010004a43e10520300307000c02d4401d402c02074040b1b601040f40b92214600703140180c0d88036803d507400c50100d05c903014402111003001090341d040b6a080f0050b41c6010702e10610075070392002040e0081e03030203000325202381c60058549801580148445001450b04208030f03140244200292592851510308155a2030340325650750311000140c5003068400514034002c07500a98091103425000b8407040000380c100020b221041d0303c00140070b4040c20320010f0700001404660030480d424000da12002641d00c0703080003a03041c51005003000070300c6044852078002c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 862410071 1106 862408965 862408999
    0x60215090c010c0602270102060105040e0715050c070303080601080c0a170c091005031f050109090207050a1a060a05150d0e0712080d0b01021b0f 64
    0x80b0440070f0350000c0c400301d90f048484000a11809405020326600c8118000390461304541c0940103840001840741000d020700c0912442401c042c0083c02d0800c4500321914441b00c4020b030800c2028450300c00300d03440402044010b0360103916080785600d06903000414460008041c006140000d103c4040e0858120103140414100348030755a610750b9071490451094040e00300031030b5000c41c11880914106400000560140f00c1407500000e58203440c02401c030441c0c1462181a000651150041204402550140540301d00c21001d0302d6440714141c0300c529800f201e2506088911640c0014003865103400105c1000400c2e094800152400000c01d0380080ca0255201481400b0b48491201e08400c03002c2c4406005802c0c82607810812000300c0c00c114442d40c01041a000d186494151b050030b80398000241881446503544603d1505040c10741408075001c4070050941d004010500301440c0c1c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 862230215 862410071 := by
  have h0 := BRFrame.cov_init 862230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 862230215 ≤ n) (h2 : n < 862410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
