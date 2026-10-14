-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0318
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:10:57.850051+00:00
-- url     : https://prove2.me/submissions/cc57c53b-2865-4e33-b779-2b222a3fc6f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 57014391 ≤ n < 57194248 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 57015641 1250 57014391 57014411
    0xe040804230102030315040902030316120302031005010c030201021c06090b0114090f130c0e01080c07020d1e020604090911030601060f0c2102010b0a09110403020d110d0303 76
    0x18500d540310414014007140c2a48041400103944d0703200140020a454201030394401c0380ba500e5030407000d5040d81c05070960b40c40d143c0d26100344a0090550904030340400440079800407803403280c800e032807103250760030211014245810b00644142c04095003d5003103540130448030507400d40d49654030a41c0440880c1c00100780d460030245400726210038040a041050808080c4072020015003540c2c68184111141d03ea130840b074400180003401901102d250142c1490040100141c12007540c1c8140002030302d5020042c3e80701e0b0210b507101d208110b0700a5000142c0079100000c00c280f00d6800d84003000240c140f200001807a00050941d0704154050910036440b283d024003008101c90003c03038078140580050000c0c1d4105100605100b0505110000300509400d12900380a06014100c481d110214000981c1030b88003d070007800f07803080f10082c40c0141c0c0249000103240309503101d003144c038618501400b0708150541e400c1000d2441c0754101030b03c817501d074403809404a55a24402098961003034074001094001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 57016891 1250 57015641 57015659
    0x90603150b07210f050904270602070b0105090405030703111e03030406060501050408100c0c020604061e0801080c090405100606080f010504020f0316170907050a0e071e090e040804 79
    0x30208100c2004544001c0d10384d0203801c5000e40b40303800800c031b4001c10300000c46640d0302d00001c203081035024124002412103007413200c40d50003440100d0158440200d181c1c0c9550a02108102c00d03940140700e540104a0140464810700903c01040d440c403054804401c1c0c001202482110f402140c030240f0b0f040042440100607070f92258600070b0600303007800c0b400c052900301d04136200d02e8036a0f030544070107440c1c0700d000c80210b06c10400c00341400d60042c80c60307171203a0312101c0051055083d0381e140c000200e141c0070f0741940c039401817103071074100d0f0700103001001c03241c00104c240f0141900160040b5090300c40c20380014200b82d580e0143c50080e1080eaa100015840c0c00741001d604e100c01a40000d00442c810001e1404400324141225401408010115040169048100e41c8221005900c5005070028010700022401c08282203084036003c03502c000819880b102e080c0c00c913120644199006c2140380701c2c0301601e4020044601d8502249003400b070b04c0f40742d0b181407104168000710741c100c410352000034007400380041c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 57018141 1250 57016891 57016943
    0x708070806010e0402151e160501050f041101141e0a02060c07030906052b022101050a1e0f09050601030f020703020a02041e06080604050c030d090603150b07 69
    0x3034803c503103045041c150081090808080a040c4070414009034140d0030319078450300b005d8441980742245a075128181400d441c036401561044843d5420700011505807440d00240318027850b007010884202004c04c500643c0e528104180c0d80e00014000d00020f0038440d0148400b41003129075032030450799461990380007400c0c1100101384000601083c4060b00100754050405020f40c0c0c1103083c641d030f403021480161000e11140c0d10a0108004503280c1841107c62241c01903c0c4070002d200140480c91a815102c400c20042400303202c0d00200880001c0000c044403800da18041e1038118012103a0035150144d0303201c070700c000b80c00180030681c44205028055916200710680d0030003107801103041c040150b80080d126a14100301a101e00d44901c000c00c1a07103507c0700d08158468007010304203c419686c80c2c07120303152881103a0a84090050301c9607040701d8240420708004e110429503495040320300301903080d001400300e1088a1000002d008001c1030030b03c0c0314001001002c2c0600c00082450b244469002da400c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 57019391 1250 57018141 57018149
    0x190e070c0b0a05011d0106170a020708070c03030f030b0303030c0a0c290606070b0612030405061210080304030c060305040f0209090c031e070501030e010e060c04030605060301020a050a1107030203070807080601 92
    0x1000060040007e682d00080440c1c15400c0c080d040c0d003072502c2c2c1c007803494003038040d50702d014040d210001400d5042001029000d81143c0c0310b80c44500c400040d8880a80440d140000b0752501a0003c00c00101d9180543d07000b0201400c65081600c036950642d1200b0307004001c00f07000f5900e9810340b40c01d00d0300040e615180e181d921280480303040785041d90355501c060030b00300003420840c025a110030750040080713424400d4a001d40300c05051503803155102c0040000b000c0c2c05451200740d1141b141030110300080003104540580350480b250903a0070713182100c110000c0400a2040d202c1110880c68400140d8401000d94003540000e802414014030107001c2500305a0f02d044240b01d18440c441e02403d400c20702080751310445409090018810368494219030250110074100c01d25802801304100520204001400a480c05400c081003d641c0301e405140c201c0c440d0444060110b242441004446440b40e1130710103800c4400310a81e1407a6a47e035012900d001c065402000c07143e003100a00384042030f41048464010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 57020641 1250 57019391 57019439
    0x50c03040605061c0f02130c0e010e12072904030602090108070c03021903020a06061e0605090d0b06061c0c030e07032a080f030901030506190e070c0b0a0501 69
    0xb040c101d04d00d0b03603000460090042003041944500c83c25960360524604070441d0054044c003107405001d400418204003000032902003003664103108610b041005c0c0b1003542404500003015120308100b4188408a17810265a80d41502d84901a50122a58003d80000e5128550140c1c854032144005000c021004060500708940e507c46807000c26030024040b440304c0505120755000f1807242c102242032502004000d400142003010001d40c44100e000d4010398034030079108284081d40c9564046465100f2610810f034404544144140400c2050010b00c1e004140201014941301c07807450300d02d990b0b2061400500801e036840700040508dd40600031012141c80d100c0250602c0360035944c031400030300c0944078008400600c41c41018030f60f01c454013103e400b0b080d12600311510404441d80b2595a94005040c10b80000d05180c04580681001695134469248543d042d80a0320300300310040320b01c018000d01000412084c2801074011400352050340380504042c0c2030110704c43d0b0525800c1204001080310240c90 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 57021891 1250 57020641 57020659
    0x10209090a0b09041412030114010e0d080f09060403050d0c0c0b0403030203180109052112120403120b040f020717210405120c0f0706030c020a0201110a06050c0304060506 75
    0x1083c2e0352000e1940d84103605c40c0004401140f041ca6940c985500300c000c201070f5150010000c9a054556111040c58000998400050345140014007804984900c002007900000f480701c0202c10107803c003c4c0c1210540a082c1c103041a40c0c9403a03651800d000c0c200e481000c10840303000b50062101e0055440080c20981103114139052455500a54034401c940d000d0182088a410007007083c1c0c41154441c009000040c031021308046889460b03e804001881d50280a200e081e008010030b035048010f4400d61341502204120300d0b607841c1c905031012209804540c1d050350f40c40540b24016540c078840c0810495080c2001600e03a0b0705841d007240c1e0f81d55034419064526406010f8221300740440d4008040c5038241000c81000c9880301d00e4103514290345e070045070500c0100403510004c032160005040c07492100b408200e03440aa59000e082e02151141c2150a0040e0410001c29000d540500c90503405c076120314040781d820548a441d071400311141035803c0c403091100013080c44280302c040e000703007500700704112202d40f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 57023141 1250 57021891 57021911
    0x1a011d030304050409110406170114070f050a1403090a1a0c09010c0804050405150f09010e060d081308010c0f03060b04030f1103060406020a1d030303150a0b0a02010209090a 76
    0x41e0720700403403041d58852600d13a080441042440303070a40c0c080ca00090b005121158840803248100b07102d80d41004015840d02804c2c00400c0c04ca44c00d17440c01582681c07a078043c02d07064880100d41a40c498112038041c44030950101c122401c5440095100380c030031401403e248501da1512000e03040c58080300310382c0c0009003010700c08000c15020440e06000424204a2040c020a143c94109800b50340d0083d6030042c07900c402c11404071034009601c00304110841d20300c15911080780070004048400e0082e0807a00182c0d000181182c144201c0c0e80784054002d00d041d41c1010440e44401c01c4440042c0c105161594540c01000b0290b074202e51000d081c02460b040a1085034200050104103018900c0060420900c442642c03090040040c0f010f542504050242c031418603090620030701070b42c05402020300140e035001e442c02c1c4500200b208001e920b1401000b0310301d0760f10750000111380d070465400d25a5100010302d1f0000b50301c001403001441300020603000507803600e1a00342041080c1100510803074605040c604515 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 57024391 1250 57023141 57023143
    0x614030411061606060303050307030b120d080907050a0f08012a031512060b0306010801090b04020d0302010b0307180606030b010203120a0b0607050c03010606050a0503010e060d061a011d03 83
    0x1c50040780c10385001d074841032840c90780030280300c0400d000340c200f500e4160003106040d8030400070b5228528540b0240103010305202884601c43e131001841d2a6a00300c0c281940207184a0844030760003040000c21101503540b0380c800101c06030300b903601145031000c040b00100828002030140c4007441859004044891404206c10b03ca190360302005113081594408601420075203441002014005251900c070122507540b8010b4002c2a40c0b2990a10a208502c00024001014040d1249559000c03a4400545d1a03e80c01e01c00c00c16a07a0740210255500c8240c0c0d04502d46041001000900380c0d02c1040d0a07404021980310200e500e44e40021041508049400180341d80001c1180d4650701012005000c5954010400004021307400280390b2211001600c1418072200080c907507900403048008000150b6a0101650b19101f202105c1001c1034090004001e4500b00c40f40701640200050402d440e480e285507a1001142c0c413805000c01040024003500c1c407596403040d41c4690030220402c40140c1011020006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 57025641 1250 57024391 57024413
    0x11040509060c131a0d1a03151b0705061501020c150705070f0902040e010e0403090b0a03020906030a0c0e030c13020c1c11100501030c0501050a03090c060906140304 72
    0x802c01a200000d110740c0000510200364018080046181003210754400c103030481c0e90000340341540950402440d181c42c84124000060050760050013068840040110304120140003010030b4192500c10004050b12a090402000c1b20742c890005000ca81c500b544003842080d5156045c6811540050b0002005464456000d070104441c4400704c1c1e00c0b2401031034030502d0041e13143c200d0341d50703c41c200b00e0014030900a600903000390703140c2030724034040c07aa04e80540110074002203401a00090710080c08203e849a05ea000b821607000515015142140e19008246141c0c400d41e000c1c09800e41d00d039514031910344d02103050301c0d50003002c0b00a0401c1b00414000103c03501505007144918580c0000d5100c462002001420151a440726504601d8200000050701c480001080703080c450090784680d0f21000c000d031150506036640b0401c90f42c100350a2100441c0c882c1c2110300c401d03080c075542d43e46140104900c14101002017a1075a0780c14031444c140240184919000d031030b1480801c0c814014880090050300c10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 57026891 1250 57025641 57025651
    0x504050d021306240203090a05060f07080708070c15020d110a0b040803100f03150903031103090c040f020903030405120312010806070e0d0201020a060902060d0e03071104050906 78
    0x24509198214000a512a020010096502ca2404400248160100d50f45503103840c034845200300c20180c071980aa071603119807000315600040c503000500241c0303417502c00b8006104c10441203a050480f580e07100c25042e4807075841620030300f10214209040111042e04400034180256800c0100606620301035030700e10300e403145c2d50148074808030901031100080005400c040d801070088480c0341800d05000500350b1040e2034000e02c047c0044008603d01405400035001c0703d521140f6603a00c1c2c00307000c0002000340703110f843c2107041545426103000c00d000031201450040300303040090000102c804040004841000600100e030500610145100d60760100c00d0310212141038400b9100d800403420702a0442c0f15a00e80c0000d606048000804c2c0070b030000403902d226540341c0e101c00e41c4821041041100182171214000c0c0160300c000955000104c5907000f11960501c05003030307507080207600c54030740c0c090307516074028030980350b03c042003031001d01941140d1241e03c00000d607410003040c20000a010b80300c0c403000302 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 57028141 1250 57026891 57026899
    0x30f03080c0c0304030b0609060909060f10090501060e040506091003081e0c0a0c060507020d06020904090501021801090e0103080405010503040503070b01030609020f0406080705100507021203030f0a060501050405 93
    0xc1c52072052000300d9841c10b9210040e0ba83c0c560720303403402441c18501602c0d024019003541c40015510304120900360300480c0c286004141701e40d144408404d803101c006090840317040075640d0014a18a503030068038003a121580301d0003210114034041c0011a007004006502c81c00040e401c3c030265070b01c10b00242c07054030340181983d50f40e5814241c4205e8200e50404c0105041c0034005812407030900082003400381248190003a900056076100101c40d40c2c059014040c0d030200307482d810203000a0003540200081e18002d0400b0514056503154a42242c1000c003242410461200c6e03103020944e030040702d41002c0c14041e2084000c0d9410b540720054180a0b900179241131020000c04902480700403c00d55a0440d8001c411048075038407483d11a002c2c0c001c0074000c82c0200e03c218681812440e10f40181c00c00d0310614001004160300d032100f00b084140f44400301b02c042c02000c002e03410241c1c544041c0804000c80040040d42d1743d08003000d10610b2541c0c01400d414085140280a1003544e80c080102c80c21103400326 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 57029391 1250 57028141 57028157
    0x30d050c03092a011b022106090f0c01080a1e020a090b040815091e2b0806010e0d0501050f0709060f02101d01090c14030c030703080c031b0303010915030f03 69
    0x8491206034031034005c0103548004405c04c480d40240c40c000302008056106010f891407a1195900b00b90b45664203000028990018094152070394421040c06512010804000c02c0318083e04051038500c0325041c000000741034000459100450300503801e14020490001210315240c50004515140c2030382c60200074410b005a804552403950807c0384100220110310303006400740f9040e2100daa1032000c241000481a1030301002241004805c0701540a030600e0b80320081250384010046403129030060503140d0041140c030408004c1002440340d684105031401c0e58010034100404090003109c5964083d00c00c0002c5190400d0040e40e01050340d90710706090441c041a04486e07a0208500301d2549a0407a190350710380f144041c00d011510030804100c800702206003481d65903040a140e214078900c100c5c20b40683c09884100002219240146685015482503904244984008411410081c03502c10850351011005102d070041c00e1144e0000326042d082140011459a6101c5e1074442602c00041d050110740 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 57030641 1250 57029391 57029417
    0x304150615020f060106050304080712140d02070c05030703020d1214160314030105031e0102070204020307090f060906080f070903060612060501080d0c1202030d050c03092a01 77
    0x5410100c060400340520108680c01c4140c02035a030302d214007440700c2600c00e0000000c1d08a0152044070b0003580c000490915060340c42d1106019070304d030903002c0820821400d130813580d0a0080320280655444844015a41c0c40450a0001074a80c45402040c4030b07401c072103170420051742c8803d00a61401da0101c8800c0030480c05540c10756075a589000c0700100403000003030104907550350800c0a41318511030703281d21400c55507640c540b49050000b4050b454066110111450074008103a56084000c54854000342c0b03013541c0caa002c202030303030410740c0d014000c110098418841d0010045207030014018070326000090b42d1070b10700300500000002d055415041c824202081c14a44200309280c0a503030000d605100655032032204d00005010180160b4400b45804008900e80038081401481100166201c50078000a515030b411800907264550081d88410460300403e0319260086074840d0504201860f240e2403e21013580c00c3c101201003c61201d02ca1021142c03240c500e803a0240001d4800b171074119152410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 57031891 1250 57030641 57030683
    0xd0b03071d040f0c09050a05090706050d2f04030b0106020307030e040504020607051507110318040510091503150207021f0203040f170d0c111e0d030c020306011401050304 75
    0x80c8078400b41c000131340c0700404148480030350401070080340c02070002c00040c0c0e55805c020741c4a14a5004200000d4010040f8200b50081900995141c4000002c2c1c028401c030386121140c40901d031514090000400031030104140f0990621107401010700d030025500c0c044a907900204661210048e49204e20395030408203095485280945025550040480b54940c81030044840d401008440280000305a2071000e00700301d4000c4107440402070122004081c0d80e250504000107004010520100108070900002e580c0301c850080042c48004510350358161402c2d030400b400805d40b07541c00c07a040c00b030040102d000103846d00c2d40c09076000031030788920314600303501681d00300d003584221f500081e0ba02c2c0c80e048011a0058000140620381c08040040359854a50b00078185e03600420105c0142c900840711180c06481d080084c0b40005911070509d003d80074402c20300c0050b40940e45c40c001500080c20515210013141020041c86014185941e4120714140058000800c03a2000500040054403509601d0a030101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 57033141 1250 57031891 57031913
    0x1080c07170d02030a0e060606040501080f0601020a05031902070603020f0d0903030b040c0216050a081005060a0b0403120806030c0d02040f06030c030803070314130807021503010b0d0b03071d04 85
    0x1900702d0055650b410000785503400381c1004003200f4070900643c004034100e45401c100700d40c100c5106844188203952003900316503600e80c1c0204054150300400c04040c000034010b02c014071500b21903841030300d80b002058030700910302103e40c0c20030014948104241d8041c8452601624469007003d20041247e210038036048014100742e0320015041424050041e49240e0003060030104012142c0c04d0b041d103155240c00f007002113640307407281100a40100242d86501d20701a00081c2d4408030180000700d8680d51103851490b1039101781e0054801407440032003000b415510800940d04400210014203840306200000b910900d0a194003d02c22555507020000e80c0c0c000b43c03c094002c6401c0440c604c07055172349050070000c5a108856110000e4070305000d11800c41520088107004501c000705141120f81c6a0f0703110711a0b54000081680d0200803451039507103080c6040020741c080c2c44035551207030310b4030300c0c5100d108281e40034181030904c00d0304907601c140140001c1d400104450900c0040f00c1c555074590741441110f9103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 57034391 1250 57033141 57033157
    0xc03050d14070f02040b0a0f05040f0903050306091008030417060a09170d23090d0929190e030d0c08031b0408010c0e0a08060402030d180e0405010605090601080c0717 73
    0x42c01150300192230100320070b0300c20488800ba40c00307021191030b0161100c00c803124564000c020032000c6c07021440c0790038040861035119007444e0000048548520040b803a42c1c03c0741d8000080008040341c0044084820710103030350020b0000000b0302501c0020782c2c404c40f1010f410b2148000c031a0010500d216040341503081022903039940070701001407501c4e800d403401001d032046074035400520602d810415110304c0b80c20b1041c1200c9421014074101002c0414240e02450303200e0300d13a10060800c0c00300e100c1400a007541072a9480c0ea6484a0b002150f02e241423508042c400820340d420300c042080702c00d010880c0501100d41c03011071504d0b03900102e641000800114095a003240407590301e4158501101a00f01d42d540b43d405004507002c0000964030b2944a594200c01c450003074140c0c0212000c1c80c1c244d03009000803001c07000a00035500125403141d82c1681082070460302070301c0702d070344810701001907050400c80150030141c00c2c03812003004d00d403010204146c0d120f030350401401c15a0480c881100c03055844d003560031b10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 57035641 1250 57034391 57034399
    0x5040204142107030206030604020d0c08100801020a05030c1308030c100518031605100e100c050a0c03050c24060306180a02060c0a0804030c03050d14070f02040b 71
    0x626118040c81e90103610600100d030269030002e0b058001c440d4410a85800718050400516500341143d00b070003070a0b0005410701c1e41240e001d01858003001204e00410020220642da00380c1e00d0701c0d10420000204c10640c3c0840800d0f441040222034680d440b0741201e51101c9040740a035500c400b40c411704c0605980c140c2c0510301d01e00010914600000c1c0100f03408000c402030301c0c418007103030315003030601941c0d000c0e0035618406680c070422042c0d901500c0c11510907000307401030050325007202400203804c007500c119140d10300c500e41061610070711400e01b078400c03459045d11a1510a0038940070b19809407120701c0c0c0c541c0160900c0408545036035015420842100818a100e18803103d52141c04103451071403800ba143c20380300f0b00a502c0020030903210010742a480c082c0c2c082c010240c04120760240074103640b04025905e458060b0401d00340200e45030300f000b40001d6110340c12404003e4030303506101e804d110700101a0003c0101010359850803150790400d8491441d04860f18854118052001900600d4620203203600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 57036891 1250 57035641 57035647
    0x1e2a0d020c0d09050a0b04030312110a0203070611030907030b10030501180201030c03050408090607050304030c0303020f060a060807030605070e030a200306042003190f0c0b09010c11010306050402 86
    0xc40d64002c2007401880c000381e112054510b0b100c508000b41c080d02800303000035000c0305000400200e4400d00344801881048400010400750211005490343e02c2800c444d400741c0d0001032030350100481842566001e6080307241241c21828111181501c45045100291028800b400407411300c05440110078011503120000b0002070450b010403840110684a0990100f86410101511140640034144c4926844400315140a50702c40c104004c907005903600342d03030074401800040001040c10303110700041c1d07000e60010403280b45200711151400b40c004281c0182542092020800014000390389010350754481c0700030400c0d5030340d84011101030b43e44608243d41440f503030503114144035250707284034440f40c221010b4503c1c8403491001d040c0d0721b940944000b0110b00c0c00c08101030280c44840844c05426000071300f61044c0d1603141c00e1558441804103c00e480040030b0807106030030841d400501100812070808a141410005000604005050711028002c4024100001600ea200e5030169024100050045417 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 57038141 1250 57036891 57036907
    0xc01120b151b060a05160815010318050102030108070e0112170a030b0d030909110c03040b07060603020303040308121506180f061204060b030303160f03091403031e2a0d02 75
    0x1001d458203440046d00c508525180560503807003440254400d02c9400c1250b06c451201070011002003a02c508401c8148a00501201c0000e8083c002107000b000407500030100365080c0012112100c40682c4410310214a14a085000600c40c0c041c10350404001c440340381d2520b01414066000d007620a41295001c501d0742040f004042d0051405000d449143c0010002c40070b4401c0240c0759407148980c031010317991060000304181e4001e0001411100d00c61800418080c0d07880d40428619080303030f00b044400403030200d0180840107402ca601030744060b8040054a078914a40007040c1d00340f0400d8400f8185ca940d400d05143c007030302c441c0d40300381404602030815a0f44020110381d240070700c0c1c0b00343e40840c0d8140c1070034042000b07032800100742c03400380d00c182c4403220344001084800d4681c04001c8400c84241030310780190b80c0c0881c0209010341d14000165002e10707901d107811580d40d007074542035021710300103000d0308c0c41417204061011030704640a030380640350400b04c88200b051150300c034003c2910320500d050001407071700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 57039391 1250 57038141 57038161
    0x40b0703110d02030f100503120304060e03030f04030e062511030f010902010306080114010b03090c03010f021b060103080405061309090303060602190203030304150213080c01120b151b06 82
    0x54452a40011213010700e855611b444115a0701c80c0c13040070351580c00980e103580e015503500011508030780319180000e112071000302c07450b007544c10448600304085402002c200901d50080115862a84122940b618006a030300f44149078100c0019450102c460000702841002075403c0c0004403400b00070102c8050b44031184501c0c0c040c0042c45405c13400a4100200007a00c400140a45200300444400c40c41d501d03800c054000c1500d40004221003814031480d50100000d4800303119035400c5142c0351758056603d40224941081800010403401c41d1540004010030100e6100ea00340d4094031400c4072810f55400c0202130803841d4607241d03003220910a282106c0c443c00c154055000d14100c0d48241c081d105a0180c0030402034140d00001d00c0030350150010000900010382c81103001c003080320341e13840060170f242c80340505c4540c645458010b5145540420121445503802807440414052010424002101c00902088403c100e030a040da10701040868008295508000d034901d040d043e5408485c480e26025041d6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 57040641 1250 57039391 57039397
    0x3030e1b0f040504020f060c07090e0303010e01080303090a06020d02042c0907060f08040303090f0b100f080712050a021201091a160f11100609050a020a08040b0703110d02 75
    0x18852840e50200300e440342400c0c0a03e5201c1e0313400a0031060b80080c3c51052003140e51101003546400d010340840800c2490381c0348034008009225000458680d030416100c0c4211490607000300107103038010b00822a005500045450f903041d03001d880503844003251903d21000e4042e0307820940b0329403a40b06407905c1c0c076281402202984000d4882443c050b031150005103071103240d14051800050100c2801c031518a008901c250380291007840c0029200d009610f1301009141c4d885c0c41200c04031400c1c020300010340a0510814060324034030616008051510940507500d83c00c03441040c15001e03810f4445003d000e01448140309081e0040c00000c000303980b10041034020b10044204407070f00024000d40c003c484c00140c050074860308101701c1c16076805003070440684100309900006001c200b9103a00460410b001804021801041840082141404c200c2002c1c2075400050416100030301c18030044500c1c6038000002500543c200364038040c10348602408401074010a10014050b403400201002c04405590003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 57041891 1250 57040641 57040693
    0x60d05280210030903080a0e0709020a110606010305012105070515070c0902090f0909121305011b0314130801060b0d0b0108010e011a12010602070807060809031603030e 74
    0x42e8801c0c10401006904840700d0341c0c0d015002034620000034443c004540c0c08650120b107008101c9045664812021061340c0c480d8a4480019403001d5501e030986c441000400d401800c02d0a00784180d6041c4001c41e030011650780040c07031102410300740c103805008041c040707140a4100030707005401804255460034000c5e070040d42c040b02c0e0302c012410001307510001d5200307030b070205030004103a003049a10742c1c420481c0c2103801030203e051034051418103000400140f402440324030301a04070a51001d142c00005401c1e0761505061801c9040003034801d00000c2ea12029050300340c000d5145190b26030302958115100a40c10f070300b10901961038000c01040c914080e00180903030002c10301d01408808080001143d1342075080c0304001c42d1039001e00041c88803000e41c1d0410420340080c19602401e2504068003423200c40c00a0340480e000d600304c1401401010f8040c80710300050681d50401802d2414811038090b920b02c116a4101c5401c1c5c0d8950008042621030b42050300c4541da100f007180c001e081842c640003526491030107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 57043141 1250 57041891 57041899
    0xb0f0106020601060e01020d0e060d2901080621070e0103050105040b060316060e030a020a0f0515030c0a08070c02040207030e04060f08070302091302030a1a0a090b060d052802 77
    0x200008221788541c0c0403902d80c4c1ca0607405072044211010b000d480d180c0030080b000380e00000c184000c055040591041c3e68207907800c500106c020903484600280c09020141010341000030903400c100340c0c1c0c0c65130504a01d00444900d03c1d40071b01a030010089041a180b03800c5040da00720350030000000e0110541015008a0088417088150f07240c00d810940e03101100e40520ba800304521100300021400f8030220741c4149409010740b00d15021550029801d003c298004003a11304202405105909144442210442e4014105072a50070040c10800003401601d0900041020010008032142e10030b49041001c07503800b800a544071200d40ca0080e0640d2100c01e906401503182c160002080035405401104484560002d0300e00341c2c0c11502480b00b07400b4001e10790760601c1c8440b18004010384042000000840c000c5180810135030304c1d00e450000c41c90002e0450007403503041135184030100d0380c4051700315004a0104d54110b601c0780e03e440c1403418600c8015181c1300349084c1c076200c07070100340d03951281005581c402c035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 57044391 1250 57043141 57043153
    0x904082a100f060602250801060b040e0601091a0f070f06091407050a031b05060406050a23030703090614150102060c030408091009030b01030f03080f220309030b0f010602 75
    0x1101e4642110303e68030401e0010707030280344007400a1503250080071244540d00881c1c0d00890301c1300d401c682034921a40c0304441c0e010000600308101015070280c990026000d2826095403480c0407541c0e10000011240307410340c8080000c01149101d040f90455418990004c1c01c0d0290108605210004010107002982e400c248000ca108581c9008291001592401404241c4203403e5072291017000d1301d00032400240c8440800302154513551070b005480103041554030702e80d5604000340c005028038a90503207254641400084c501c04d071060002940c1d48010f06260020b07a040081c1080c8000e0190480b5070300b54000c000e014000342001c1c85502601c404001c1c0c01301c80f031540300d03030161640c01c3c0700842d00074000240c00c4c0000e85103854548151100c200042c91701030015502d9844101c2c0c038110a900854100a80300424410190440030300356000700004084d2255240c608a650b00040c90032100310034008554140c80e0401d40114680000745400074106d0502e8036280c080c905400d0b2080c064200075101e10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 57045641 1250 57044391 57044411
    0x120a0b040507030606050a0e041103090115080703050a030302030c070c0f170c1e011701060302031b070c0501030c090306050c090103110a0c030818030a031b0903020904082a10 77
    0xa80603213011910180d965a107031600004d0100c030a51200001a070380b0540316146950300384032600c00b641c09000041c2c00001c88034280102500603084541c030241442e0030112040010030000310b030500e2025007505015a803a940c10718240c03518820a1001094180503190105698000344030000c00e4958407140d0041d1481d02c10100d41d940c40e040d030310782540320701c440d900d404603005410000d104080060500b540c021942607210a2240c10076007005000079804070408c01d2072503180200070004200880030700c0c908181070311841d040c0c098900541d8107040d1122034004400b480b07a4900700c0150341011003004641801e040030036191b4002c1c0c00c014002030070107080280040f500e408840f615200d58852502010f90f990b004c0da400031000780034000c134814070400900f01200500040c80c84200300d031383c005801e419100003604180015100c20341049189401840180ca07101c801507000303504126181d071200b01168000114041c0703070a189010740c0c10180015450a00024520440d8540349818001c9040d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 57046891 1250 57045641 57045647
    0xc1806030b1507140607030e0d0f050d0b190308070b010605040518061503040b06121606050d0b03030c0622020603010306020c070302100c03090f0e0402060c03120a0b040507 76
    0x1c000034240d40020500c209403055500d68005001043c030610b00840080c4280c0c0c4001d05000c000c495400100f51505007418216100b40410030200c9a1810516030026102000900c10b01501810130b881c1d6071348a0b10443c0694912082030300c041c200c07008aa0b01c0b9a00d0f071800b610749400c4114100c543d00800400414000d004100791001ea61000c0c0240d81400854100d02905240240401c0d81085110345400381010f294070080d4443c60048005502c0c600300b400c00e2001d8030840454168042e04818000709990354809159003c580c410302e491919646904403040042c40010311036030380b62200080740000c214010484500c14151824034000c290796550444c60148000c070402988603c0801c010310000d2000e40c05450b42980303820450704881d440780e0103d11400085880003020031034014812040680c4049600041c2072442031207403c4914280e89190503080c003410003032003000301003814003c1d040100250f41c00c0c0102603c1940f05030a025502d48010b0041c2030b01140503a0030240010a0140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 57048141 1250 57046891 57046901
    0x170c0d0e060301060e1903080304120f080603030a110705060406020601172e020903070b09040b010e0306040f0201120c0f1e0801061202040302040e031917010501031a040c180603 78
    0x21380d4803113288003d02c0d5420082003d054140401c41c1c94240c1e800071021400380b401841c407481c45403150408031414080701a00b0403170041c001c42c0412508170300b01700164a001c0140c40c498801410040740f407a031030001403030400344690031854022401250016500340c2c005421070403218000100820000e0000f02a500e541410710107441007480014185a0041806600f05404030030040c01030038226280d00281c1415016400003401032008110000c1c130b8030302881201a00b620909000c040d00c400100400c1c3c03035000003031000e401501c40d1400c503000e59014455510b90580409800c200200e100c031805411880300e295000000303840c81d44c0419221219016481c0d2200040c0c64081d4680e103030000484040c4500201003000580034000000141c40c0c9008000b11120f01070099901c801d01404040200a0100050340c01c22001d55116a40d0820020026040d03d0080c82e022030811001c81c1c40800100645c1c00c69600300d80b402c61842c454a900201601d1041c5034031070340103507456440320101e050394 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 57049391 1250 57048141 57048149
    0x91014040e030f0d050f0c07081303120207090b0a031a04050a0206160c1203020c120709020d0617070f060302130512030705060c0405130209040f060314060c03040816170c0d0e060301 80
    0xa8410440f55001c80c01c244040c0074107121154070030303010642f6a035030600c01020329000c070300150b80300180c02d10150581d0301810b008918150b40302c10400e407440c1c40d40f0101c88c03041c02218155640c000d0106050280a0000c420b40c15000b0b814940d03941070100801c0c6141c1108442a11441013a01012401c801c852078100d9406030150b0003000c0d83c40d40c07101041808044400e03200402c2c4107005001075102132900140201d620307051000100245454491480c50502c034140010a40108500340013540c1c00031413800c2907540c50f280060710360007001980100d1020a801540c0c0c0400b04101c200020007000005042c00c520400c16200c0c5501c454003c0401e0740194003e05620002d400305080b480240350740030f0140c001c4001c0020074494034240520041b07403000e030400c0d540721070800225081d0410401201d0f0300b00f5210003021b031170341c58640c5440c841070082c00400040300383c0129a280078000f840a04414060318600459a50344024150719901d07031080107a0f1000c01c0708504919010714200d8180c074101c0f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 57050641 1250 57049391 57049411
    0x3160f020a0b0f06030715020d030e01020c03030115030b0303070c140108070905190f120c080c03070302060f120f06010906020601080d11120301080703020a05091014040e030f0d050f 80
    0x6490388603030354040f000010030083e05031090a20001d1042d910402d84036241800e41c001d01078500800200500b42d654010804000c1e81c0100241c0082800000480e81114008506095440301801d000c43c090202080d1469041c031001c600f140905c0000c101c2213045400003041d03101c80280c80c80054075a800100c0c0c464000c50b0503890704210705d0900c1144907042d107441e8400200340235250302031103548000a40205030320051464440041040031043c420140c0902001000040b001400080d076681050000900803003000c1403441c0ca0a40c1001034031455406617054818501d4000c5c200321444404440c11400102c3d5000700190780c7d8004200d0606841c882d40c09040c0c0302c901850103954000c2c4280307045c0c50307900c0740c0741f000b240114002010318081c05114010f8000303039185004000700c202007900200e11a6003000288041c000d001c010f034100303c4100191040e201c060050000b0024141030702808140d0100203024910314500700300402c2d04580d0510104051303100c00140b00c0400c181180c2200007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 57051891 1250 57050641 57050663
    0x60f281107030b06030a05012909040503180a050405070e040b0607020622030c0308040503070608090a0312110f070b0705040305060c07050c10050711010f05090108100302040203160f020a 82
    0x41800c2c40c2c0f1040c0e00c6100641150b00640e0700c7d81d0b9444c00c43e0f000c1c0403107450200c0300b50003660344d1010380e1085100c228411508240607040588520740c50b84502c40001c0740d00d090041c80505a03868640640004060003881042240360840707000d40001d205241c0ca03403180f0b280510b00f43c800e20b0f04030705481d00745401600c01e5040142d041e10304d84001290350007003307410001080c00800a01141e00750b1000d0b6106440707480e02c0e50302e058145444c05003590481400d01280004000440c0c0c2c1c00141401c84a8042c40c1408016801c0541d1100601440b0891201c216000034282d00001c40100205006486441000180e9842c40000c0300c0c1802140402415074005801098030411140050f0030410300540584400745000b10008e00006100c100c02804210b000c5125420301c180015030f80c1500303100b070074017082c00038103075034001c2c03052081c60b00043c184800d25010540750032500c40705002640d4040e10441d540d0400a40050f00b44001013100c200041200300807900180c40414003122955000f060104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 57053141 1250 57051891 57051893
    0x50603070b0d02091f0c0b0705120402010804210201020c160f0302060c1005040b09010f060e0610050d05090c09010807030b0a110d090303020d06170a060209060f28110703 75
    0xe90b1000316841c5d48408030072410143c3c0b080074400c404107101e840d240e610b01c1811300d140c4095142802080c0c0d07030a114080c002e14801500c10000f682d4450390910b03014800d5038603490802424000e00304610781620552041c010000d8055008140c80000a021185190802031403c0c1540e01d0368001d0345008040301c0300070401400c05801500d1444100c1e01680c0c40c3c3c44a40c3c80d4442101c3d000c807415200d0401c2442400071025080c0b007003901003128400180038031401d200d680c40032068003401e075174003c500307642e800711080d1320540546000d003c100c1e1042c00717207081140e034096071002c005807101d2080648100006654500142240031a6448940740881c4d55441c80c0400c000d03d030002640c0f0340d1030000c10070300c1089a1a03101d1403a003940309460058855400108030011907846c1d0b00112050301f20103040390640100003074541050b560016015941d900003030301040e018020b91101d0282c4c3c03940451051070080030481c5410b44001f85451110000361401c804959180c10541c04041e00c1d00329440504c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 57054391 1250 57053141 57053167
    0xe0303030c04050d0201020f0a050303060a081501030b100305120409060e010f03170930010b0325120303020403060507030c0f111609050603060106050c100509191401050603070b 78
    0x2404c2a00500513a441c00001101c01802c041403c2401c403019000002004a0740c42c0040c1e281000c0d05041000703242651110680c0007101c00180406041641004c00140c946002e800700c800c05954000d003900c100030023041c400c0c02141c00a010340c0da0b4680c00c0020114641c5285680c0303504171400501d40800c80c07442c680301c4603000a0b00035032a5100e51000c00c07490609032a0120707004511745041c00201c1900846600c004a55852090800741c540d041c11f0a10a055400195618584000034800054540004022100c0042c244c1c400915001428040b10038113406601a00883e400380d0750074030603540c601400f2022550074020450100e001e826417010340c50b1045021150040d018400c03910300ca01400640b0203009156807020030581c0e1540c00300030182c141440114010300d00360828908102d6401c802c01d46071071140700d80004460741d9030001800300e0020402901d07015a105c0807468200b045092040200d4200314109001c0e42c00c00300800d050341000150071003105e822014150600704030310030036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 57055641 1250 57054391 57054409
    0x902090c0c030d06060e042a050904090506040b09010c0f080103060207061103090c24030f04050c0409120e010c0206030c130801060906050109090b0f010e060d05090d0e0303030c0405 80
    0x240110320081c00601180c03000b900c980340143c051a241c804403042d19078200000c0e545080301080f088e0000c000c9440f07080e29640140304108607541091a1500e04890110b0010640f9003800f038240d00c1003d040c00f0900401c0003001d4054001c0c94001d1203600340036603080c0d480400302032034180084d034054010000319200e41c0c06403c0702d521076500852161701c41160905503400980324200b150b0070030f4504071300c41d2401e840c0742e1080c05d40c110000c0003120148800c0c1d15440c00020494140641008005010008144014071150600900810000c15103040c95403c881a0340020008a40c15500d0000c041d030107103188101b00c0e60700405041c550340d29401581c007a50002c20305120a5000e002011411403001e000d810041c02c039603100028818a043d0004000c103070560b001c260254034192080700305440d01100c00304005420708040d00e40200c003c01203025442041da48441d554685800d01c824020302142e41100c1e0681e940d03991160030064010180c43c2e00c402c4d00c1c161100e207420070003002603003811004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 57056891 1250 57055641 57055657
    0x503040302031207080603160f0909020109031b030c0e0f0703020a020a0b041412040815131a0108010516020601140105040b0d050f011a120606040504020a020c040f0902090c 76
    0x503203041c03c0c0c140402c80100322080c0c1da5075010071803110400c00303c3e04042042110021a4502c2c00400758034041c02c00c000c10b00c06000d0400c2076038940c41a9000e5900a8080c0c20007158800c803000100700402405402c8130300c16003c201c480c0700d2054000101d0b130f14150281400b03084014441d5000f40c440100a400070b600100c50207080d4040c00c000790000c1001c0c0001e06108600030700800328500242c800a0381000d404001520031990140414403103440000340c0c40b41030281721400700302c43d9152143d68841982d903040b4001c28050b58040d1034145030080c054000d0481320b80200a220a80311039003039000c46a00c041c180c40043e400b41004002000c021205c80e0349502e0181015480d02d92941840c1016038010360b83c0800d450340310020321241f0040b83e90350500401591860100783c10381c00d20300c01c0d02c903c42d500220945000400106216550b04400c481c003c000c02002117641d0311403030070080c5d1604401100240b18030b01d00901416601d240d07024295032070740d00030301010030303650b60586d80390b0345410a0513 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 57058141 1250 57056891 57056893
    0x10f0c0803180106051003020c010c080f0718050603090f01200f0f041a1305010503010f0b03090c060c010b03060112020a060f110d0305061306060e0609040b10031d07050d030503040302 81
    0x100003036240c0b1a0506c2c2e010034211a0b071f0141ea21400c80d4106800d50b076400f000303001005800420448010140340d103c6801c804e5901d044095040d082c030303032594000032355004583d002c0030000c02e0203071200001541e4090400084000e004903a072001003401401400714928040150403c541c0700142c550b03400400907280e816071404d00b010f44612023000c2507a003082c480f0b0407440300002c102e00f0746004c071030b6001c3c0100001d2070660300c0e40d8140294600454058880d034a074800c40032021070300050040c0045207442101406044d121469080004d0203000380300e218034042d02503040081003160056155442458001e0001e4403160700d8180200c60703900f4019035a00802c590440d885030003034000d0192100d542200da030041761a003450030801040c3c28010840124035403402c1d0081041513003040041c08403403001c4406549a800c04800325002d071400310742c2941c1c4140003100400704103403d0750000d284010164810800303c00071103001503031458140601a4440b00c005142030000e88100021980180b0a03c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 57059391 1250 57058141 57058151
    0xa0c02060d0c080f0c03010b09040c02010e060f01060f0e060414011701080d090603020304020f0f0a050a03080301140a03110d0609080c0f0c0303040e13030c0c0b09010f0c08031801 79
    0x451002103511075a01d07030300002c080c40c09010007181e070020400d410240c4585c1441c50f40d4940405820f0500c41c0c0700000d801142c0790f441304003216000303502c041c440f101c3e2a0142c030114a401560141404c0c001d0141c82d0210355030200d06031065100d81c260603000b48001d402d2924090810481807852040502041e042025600c2034504603200010010300a1800340000c000c0100640e00c06045c60000d034004038105841807040201507542c007000101c3c4d62005980014044081c1c0d004141c3c82c040c1904500c1e0450041c1d88000301b0041c4c044002c504881a42010160503080d21003004403041d1684000f60002100d00c001c182640707020f826030000320340714040004101980c0c3d51071003555008001e000d981398002c400c10890a138000d10029160316021405507280c07900b021026410f1070005000003961014403503c0348109401a0303800c862030764002c1c032440715441c0ea44901c001c0c0c9a1003030fa0a68005003400035020007440c0100211010a0391002800b030440d81d96011107001e180c10344503103042d036648230 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 57060641 1250 57059391 57059407
    0x10306060318020904112e05091e012c09010b03060a030b0c0d09080901030c03021905071a040b040510060e0c07170c010614030a0c0312230a02060f06060a0c0206 71
    0xb8014115100f001400e00f160742c0300c10130345035044520707611981c4010700c003040184008594030000e02123441c01040c08e28100c000d141c040101c0ccc203c0f240c50740c400c50307030414907241001d0915290009448010100c1c0c580381103030303281c0402c2d52060200780c5082e03410840342c03801440000c0342d410f8920b40c031000d03865a5908140d002074003030041e10030840c81503a204400080b10b0f00c0e00d59050184c14000c3c1c0441c1070a40c5000ca00704250098090099911030810201103020b45c100702c00c1180607154024040824221810a820718440c01c08090760112014404c43c0402d000f803484d1809014204c40041c030f2140c41a944000720710701180d1145804540c02405160750000301c0da03614000e040d500090100005015007030090351071040491200c01032103503004d0131003000040d06e407180e00304c19a40d004007068004070b80ca55040d40c6043d0605100950307002100c80d03885410b88041d0291180301030980c21200203859074801194004015103041d80c101030100070001c1c900d800350051540c46031000c1c010038900110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 57061891 1250 57060641 57060649
    0xf0a14010f090b030c0f0103020f09060301080706020f0105071b0203150a0b0307080c0d0602160503160210030506010906050c07080303090105090c0117190f0c080601030606031802090411 82
    0x1090300901d0300c03000381c18030500104040d44207102c030118081e0005c041400b40303800010a440d154485503410560001003807010a0680820b940b0303213070f01c0607222548a584900d25161101c501307008850061240b00c0282c544c6503014090980900800c2d00d44007079902c1d5007841060f040701c440000b41c1e014403a41200d2508080d800da0f07442e202e10301031100060b031048450109420314040da0700114803a48541c402d0030803640e410703c404c0e1981d544290010780d90007960544604211030000701a000303020100d0003100c040d19056004c0b0f40170b0310840e40c108a01680100580443ea01aa06180003642d074100070f0003142d005000030008015002c08641c100c0d039440e140d0910b503034011598010665111014001440c60030412240c0c1ea00302401c000c1c4c03081d8000ba0603000d070345000800001d09a042c990b9100d400388801d50041c1c100c820603a5051104404880c005042c3d02801d0710810300107841c200001074550b00c0b81c4140b644050040b104844650415003c00c50285805442a501507411741140d0b00240c0e5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 57063141 1250 57061891 57061931
    0x1e0a050c0403151d070308030c030601021f050603060f130f0302030c0304090b210d0810030204020304030c0201110303131709030604031e020111030a09050a050714041104050303030f0a 81
    0x2141c84000c00c002800b02984500d075001300401280c85c1e44240003d00003c3c00800c1625404004110840c1d1265143c00040b40340511031120300302c15140702e01c0c03400850802e079009140b00f420b054003110341684503020a4040aa4222208003d003901c0c0040480051408445610114000e10485e820050708410050659020b0b80c0710180055555402654034200280c412804001d0961100843c1141405c00c035100c0f0360072600700080203110000148031071080c0000b003000d190041d1046403245028940a08200d64140c2c00340e01069078a05000b400c1c5400004680c42100e084036500e40e0b0084507950315036144090700724200346075424415400c0035181082424440c40c0240d8500000c040c509844244106002c1c407008216410848034030300b69400e03a421250400034a403000140c501050400c2810441d0418005000d801014030003e081014912403140c070381c4044800b001480310f070401c0410203106511802e40c0507082400003d040e90221038001e03602012000020031034800c420b880d25400c41c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 57064391 1250 57063141 57063173
    0xd021003020c012406020120090d03110a0308180a020a090207020d02030d0305060913030f0e060d06090c1101020c06010501030e0304090f0203040303052415040b0d020705061e0a050c0403 82
    0x134010300c0c0200040703a42402021a07004260040c128400c0c0c1075084c010031486150b221a0040e89203510b000e0030944a040c00a0741d104281c4103403130303900c1001d140080a2034400c1d948000000401080380c000f80e032020865501d01c40d8010010b442c0e55240c00e8808010f5006010240d900221080009000d40c0301401a03030a24603540d94005211f1621f0000c00c2481080900700311004518048400c00123504010100c02c1d60304141068850003502000085942c4185400140d0107800e010001460140d90b03041035a1a040701e8860545015500c54100e080340510004025a507108000401695000350310030f000020f01d850590f46050346840003001034400c54200110f107603031300204000c00e065046c403e4a4201c419041140c5601c41d1640c00010080c0c00380c07615030310400a1410290230b050502044400520711012100d8a070312808141500a4200d013005803010702901001620070085000f80e100d035905038601141d80c9860f5041034100818009040d900c40c00300c2000088003048000144550309 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 57065641 1250 57064391 57064451
    0xf0204031103010c0507080a080604020702120c10020102070302100c020708060106121a010804060c0201021603020f0d0924031806022d16020a0e040302060106030b0d021003020c01 79
    0x2021222040c50f086608102d8030364100001401640001038200c030031540d006000c0c0c604100c480e21b41e200010000d02c15928029445a071350b01180030f0425010401076084003088480405e201c08402c01a0b00b40d01c01d4041c0140142c0000d1720070108001c1d6540320165003010b520484460700c1d1105400c07440d201c1c0a801800100707250f0032200c04240590b00825140c644451812299070a02000182c9005006400140034645400c00650954400d42c19607100d03104c181c10703000480d802810081d4a41c00c610a405503075005081c6240303903a034001e030380d520101c030f100d0240d801165913400d0301c0121207404075501d0820103490340c0c0e4850080020a03071a00300c0328018080181d80e0210f81c070390103540d00021110812007501298824100e050801e0982d9000c1d40c21951900d0650703a9440040c40d0803190b900810607007c1c2c4041804145035000034814142e0350b039501d0400c2040c5840040115100310305200942c0700c00408818503881e8880c1e0041c1811141034800850100155040d180118802c002101d500d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 57066891 1250 57065641 57065663
    0x5040501030305030f0702030702010e01030209010311160b090c1018080d0914150a0c0206270a06090509131103060712060902070f0b04080c12090a270507030f020403 73
    0x140142d017910a401640f18001585040c010781d002800202004c40101c4c1415804107407120f0741d0f40250800f9505403854644299503070761900405800200c816401e40d09103844d440003a00c0c2c18400543c4294103200280700750b0040d6060842225002c1c00140b04c1c1c01301d807226640001e101d4204000710000100c0b40c3e00ca007101141000c0d05a039900540d9803040d841811003131101e14110400c80e04030f40c454002c51900c1c200d020720a0020803120320540c08200c2001c0c80140d00c0590f6100a10030021400b40219800900c05aa89400b214400d030325001e4190300c544000c0205404200120803080b000f4820214610100f2802001a04240d0201c441102182c1c0038450703220741e2002031042c030015101d41c02d000c60500395644c80707802d0000303145072004140010500204062000c00c01c143c801001c0d9490440d1080718026810f010190030a00d0100d016246031200400c411020b0b0b40050200e540c44510300e000f81010511420103403202919080034140e40e00d1200080c0c2131140014000786000b440c500c14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 57068141 1250 57066891 57066901
    0xc0503070308010612140106050d02090d0609020108010e01080d030b0f040504050a0501110a020705040209011710030209010902031608041b030503070507210303020702060909040506040303051b04061103040504050103030503 98
    0xa21040f040c05d03660541c60178800c0022811641c4220703040d60880c2ca4250380342d034110501c52000b4450460203a9004803121060000c01400350004c00149100703a03585503450741d0f1b0fa2102098010203016070020360300107070720500505120341e001e2808404010000e146026100011604a4005542c15681e03074000028075020300c0024010341252100c803442c1913103018007040c0e001391922418014a4030840c0c00090340035450784a91095002c41c2120030540809081c0240d80100c800181d1204074003c40100d000081d60034803078401d480c030400340e1a9047c03d655203550012641c09000134002c41d036110300001c522800d08807080c0c80ba00074600c1140150758034642e5041451a224444d0300c05081c13401c0801172004d40c180b0003440110115814200940c40c0c00e41440011424011308842e590030401c3c4204100078050005000c0d802640280c508014903100c015106c1300300b149154a281e5200c0d000c01080002d41e01c07030b1046d261001e0300da02c02d49040030b40710b100040640d80e0a92084d0005140441481 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 57069391 1250 57068141 57068147
    0xd030509030c010504050a0b1303061506030b0109030b04080702030a0503030a0c1106040201090b1b0105070527061b100218010219020d03030b03010f0e030414010305060d0b070c05030703080106 85
    0x48030b14102400e145007885d1038540003803030115890042100070070b00840c07680040e81a414115014590003542405400d41c014100206254144216400203040902031203183d4002e0409100350303030b08440c8683c0703250380c0d030340362742c942548100c070200d81503c1061012408244180040d50103642c401d40c0c0404c3c0c00c40a500c0041140e0780303400318560103030403840030311005070703000309400d012582c03401302c6542c8410300641d201600e088038100201c0c49508040401101c154420024190b031949803a00c3c541f0340480301c2c1d1a100c4c0710302c800c4849420007010040c400d0040030042008400050342c904440c0185044110601030b600403804805055004074011406907806010403400b0b182c40c4824214502043c0c3c00050204660750005824103684004045140d00c2c2900600c45e00711015005002c41e4086100f00d6a580e4840e11030002941c01c9200000750a40c8a80203241c000c080040c502c070000743c0340d900c1d1f49005440c0580781c181400021242c810004505101400a42c0e000e51192042da603d8a0406 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 57070641 1250 57069391 57069403
    0x152c0f1509010e0f04150614130e0c12030c01140412020a030206070503040c0302060a1e0309020619020106050a090204050a0e0609040f0c090906020309010608070308040b03150d03050903 82
    0x501d208041450052000d0103014032680c0d80000e050024094544850601100282080e0050700c0030f03504040022560740040100446047c105540007027030a07500303110701b4007141c0b080b6003100741542241303c60210924040440202200c4410140ca1800520032062400c403100c02509088100c01e440400040c8010842442c00384140350015100c40555954001c0d1507440003803030201031010201c0420180206032003000301942c0d015042d0785e603583d40808041c00100c2240003000710300042c801c1582c0c00920a004103210703ea4003505540c24540c42000605802c960f0002c003804640d41c904001440c0e65034802c4050040801181c0169240e04010500c0140300013508016641042001804402e88628215aa21540040400c07101921074a016a540c0d50144e005040032030808110a051121580c011030068040780020032001da03881c80210340b2151588030280500c0014402040403407070240c000d680c08128104501088132998000808000c50a01e042c0d0000342c01189002c05c5090800c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 57071891 1250 57070641 57070681
    0xa110d0e0d05090102030301030807110a030302010f0615090302060f09060703110d080709030f020f211504051c03090f06060e060a03020a05010c1b0905090709152c0f 73
    0x4210315044800f0000b0b540ca11061000074440e8100013a64028480410b006614850008054800c02c56403410300a01a0104032140d00c590391411300006029130140c0590105d40803207884d540107551441d000c020154001207210300c3c500c1d82c10403010b03450b50750354001031840358400c0d10740b08046c41c0c02c2c049036450400171050b48801d04c001041840751094118108008496008001e070b80c02422070b202140070381081c1132242c1d4001d07603d40d2207058400c06411002d821010b00c00100c81508103034074141c5414100030b6401a24a41190f0302c0d0392100c60200d0040100801642030105a10710180c1e90660381079103005080d41c8142d6180010b10512800f241080c1d04202c084407204085030a5400040782c08802e4031529050041c0c0381048020048060124010b90396070149040300c8564031001d40c0082c00b8115001b4104e40143c1c10302096040d01c42c0f00d010707a42070340c0a01201c000ca040a60b07a20445e0404181c04c0403190022002d100c0030107003035501310712030b1054100540040c18107000346002080c090321 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 57073141 1250 57071891 57071897
    0xd0c030f02030c0c040b04090203010c09080c01080115050a11070806041203290a05060c030702180c0405040b01171015020304050609100e03030706051504061d0a110d0e0d 75
    0x1101458080011003c0c090341d0112000106d10051800080042c41000350080d015420000c004440b20b42002088040f00e0440c019101072080e10001100c0d4078900340500c064003180c070125514114440c501a007080300d15410009070038030561030300307518002c0c842d403044801d54031080400041050800580c000e0b401207045c1401144038206100c5010f0702918101aa040c64010182d1070a44c0e614072007400500d805032040350785090b44544980ca03075020304020381c01103c400c141d4641d0481e15400240c814034000300300604040c105000c21011b004040ea481e41002028610b401c017181c1100303803660140036128045180b803480c24008d070b040100110308560664000780302c20082c070b4540038200c424440c4200c540400503482c0c10310544941007907a90064142c030003c0350402c1045071991203a0b000e100521160341d21000b012040009841c0b090290048000049158580680c510021640c10000001d40450000e142d010211020b80005070b4003054a604d42e408100350341410b001d1030660015900e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 57074391 1250 57073141 57073147
    0xa090f0f0302160b031303021606021506010507030503180102070812040b07021c030e0304080304080708060a1a06091f0e0a090905190305040b0f030a0f0902031e0703050d0c030f0203 80
    0x1e044c0720180402080d40669004203841c03034040501c01c1c0f100403c810301d43d00d100f9114644824000b540c5200300c541070320010810f000803501943c020001c0d21209607056486030716542d00c100f40a031014080219101d1b480d1740a00401000a43d0b0300f018250201c01c81c002d9401c5840e25041c1648006005400ea0040d504008000500014400f079421206030040c1800300d40d054801a81a00c0c5202d9a400840c0900000c0350220362400041030640449103400100c0b15a51500541482103405a1510b45880c4030f08241c04803650411034050240f448000b8140a000b4019207160003c01034070040c011b002030340300750f400007240c60701911200182000f0030040007650000e40d117050340c1c1c041c11051501c2c0b00c2c0309600e802e0300300f41c4104110b1b000f030256590021344035891246c075042d03160426591520f0140c02c01c290010508260b1040d1481203400a00038545282c0540c0b100c2c80354401581d00c01e500d4001c001c03005c8040343e400c1009645a842e5541c40420020341d504000b4040451381c1042d2003150410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 57075641 1250 57074391 57074399
    0x203011416050702030705060a02030712030b0a03030e010c1a0115020c06030f0907030507030602090406060c11090c160809030105060604060c0b0604020c2a0303210a090f0f030216 79
    0x20900a48031026182001c2d6680c1c001c0b400041d140002d42c0c1d02c4942c0c01100010800c44250740400605074803071056142c108681c403842d00c16015640f441040a0300100040410000302c1d00c5410030388206074041c1030012002034181c82d007440070000703940d103000c141001c14010006003001402003d000d05003071000c2d151700f01c010b40000e801484041c0c500e8240300744102c049440c030761b428071510001759070080465100a580f0328040d0080e41054020030300c11403a015000401d18042e000081e1010343c4806090300d07100c0d03031808100da4101c014145007160401071045210914492960000181c01080850b445800700001c040c2034500081105010362010702041140a8100c038036840c04039408112101243d6540b800f01d0028011004045503074490308622011103a840c04800d200d241d4228031100c1c07202c0b0705405060343da200f600d210310a80c1d5450001040704004200995401003000100401c030207915071106090844441c40070740d03081107480004020503030100030341c3c1202c50f0440b038824011854 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 57076891 1250 57075641 57075661
    0x30909010e0402041107050a03090b0301181515020102031f03051507031404030c030e100e0418050708071409040308131104180b010e010b0a0c11091302030114 70
    0x40c4515144918810086401c6507130f6500300074041d2600420040d111140c81c2042e0740d540030b8000058022a1802c8804100350380c03120104d9059075a042c400d544103900f0510010001c10f08501d11800b070340070034040410b021000842c0e074017003000d0aa00142e05c0b410410070321000c00103140d0b0078080021810b01c0400000702c010a10404880c8000f61140c4d00d996075440c01c2d400b8008400400c40b49003801ca041004140e0010000150b990187c0e80d135180c500681030510107810101140e40021616007000c4000d580740a411503544c290380d0941030715034400b2640d03d45203440302540041400307420208050001511100458514030300c01c132201803003420203403000f4000800140c0100451452002c181d02071001b5041244500c10b006002080704000785c11121440391a011000c803041c984c0324000007800e104a9090038180d07001c0544240c0b034080c0c640c00c20b55a03034688407011a4420108810607055564010b8070306d10807045446045210700c0d1920406003121042400c005189441391b06100c60506 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 57078141 1250 57076891 57076909
    0x31b0f05010c0c030206041203120908030a0e0c120106170a0f0204020f07021206010812040806060907020f070b091c03020c0f0607020a09090203010c1706090c0c060702010606080106020309 83
    0x100a090041d41401c2c68204414100c540703030400b94110310005000164180904c1c003001005010b81d560040300d00d40c4200301415074085041c0545400300c01d001191100d4103d600101d9150b4171501111603c0840c0b1000c60500140003a1501c6542d548840400903030f090004c64941144081010b03250a0300507943e068a89600e280c03000c2c0c0515404110142c0445800c012104200d030001d11003845441d00400c610382e225006d000b40340e0309018030114070000c0c22040c0242c03801d554682003e000c40d540c9203024802d03401c030010311040440c030416982403007011040c0190005819001400d96503103922034184410304442120b0b403800c898900002b10040381c1c0c0840c0c00c3d503600100f03c40004252806a000031064050607202030f40c413041c0d42000144414440c2e2011400c680701750000e020646030010107480b02c2c40c00c02103950710086242c001403c0e503d041d80345507a1045080c1200d504003648150007516181048404002507036644105200c5190882d00c040c0c0100328034401586000050408249400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 57079391 1250 57078141 57078149
    0x903030106081306020d060819080403060f090209100602060c0c0312040201030e0d030518060402010504060c02031507050304020102160506040302040e01270605010605180904030e03060c04031b0f 86
    0x10703254040348100c4103035803d980d01160410f000b5501e603a034080d80c9100a0000d485084003504c00c0018002c480007166020810079500620403e0516196407500c4001d01a074141040c800b0396154244001a074a08040500071304405d040107940d981420000791501d1009041e2404c0c0b94804d00420a500800004035001075491500240e182d071039030710040e8050501800310340a6402041a0b03e000f0a078164001846882901040d803203810181100d02c3c3c80d0801502d000c1d000560400c028001030740107200c850030b01c510290031650300038048511104d02000035030380e0318000740000060000f0340d039040000c00700e07160740661440d0031145060002085440740e444000c3c01252074034202650103600f036001c8002088407824840d070106500030b04003001c8000d448111802880d00c800400c0c40e5200d507041e6465804020410300c1e1100c504000c00489180c0140110104a08041c8078151600c09100312070140510f68292516103040d0b00c2c10007800301800c0700a9280c0702e420171080103400c610302440c42c215 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 57080641 1250 57079391 57079397
    0x2033d05101101020d02090307090903020607180806240301151208040306020a09061803020a06050d0207061b0905030f0a080a12050405031b03030417090f15030108010b090903030106 80
    0x9401048402d8600c41514850300541c0d500c04100e100082145800070042c000f0120140c5040b26114135141c0c00f10f0b04010405001070307005000181519004a07004901070f550300806090742a5148085072a01c08c08030340d0440c80ca49048040807688030810841c1c2d90200c422402449020002040310b40c450505114030b034404030300744c070814084c0070000c01110040d503081075080d9694580028041d141d03a0b0640308003400240c010b422506c120340854a100140c0340d0041078040380c54035088088030960080c00b010740070207508200950004440d41310b01ca10343d100e18101014600725000020701703507076443c2c2e015501980003000750061010300450707200c8050b640110b00e43d07190b44058204443c0702d080e40c9800c0d0300c42c0e4a000305102c103022000001d0114003550303420300b0a1940d07003864100d4880c007040ea0000c0c4034400407611410380c0e18544000d400a40c10241801207030341250000a01548100034945042940000041c40a00002e0040c40307915807003510308414508200003030650300c1c84148500307010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 57081891 1250 57080641 57080659
    0x403124419181a0702060108070303050306010509010905060a020a1104060605071704030203070305060f07050901020c010e060d020d05010311060a050f0904060f060302030702060612030a0e030c0402033d05 90
    0x10150000740b071054680c1050100030905026461240d09040680f000c20141c8070380c4000144c40b0ba00001d0b9881903903455503845055459110054070039410000e0400d040c0310303110802084588400c000b8000e00342c002d9004040d103540c941052856082081155401682401e030300f8866075820104445c805a44240661440500b0822105d1580070340d8100940c14060360200005000b80000d600340114682c2c4500011911681016185441101c1c5003d0240e00001202d1072298042c0211100c140c40141c8240c0c80c110b50116514100da01044480b040c4a64807001030040c00980707901c03885034580580303d107890203144c408058903c0c02440c03c1c1d1015204001081e0307460352100e81211006180402e4280f090545898010f4041c0d003080320701c240184a18070010340c01e8134010b50159012401440031350f05e07103c00d24204803060440342d0703240c0350184501da480c100b45072540e06c0154420020382c40c1e0004a80c01d07410030b4840009040c8455000c40300c258144560701ca000041070404c660f021502d1110b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 57083141 1250 57081891 57081911
    0x3090102071a0c06090706110114011e09050c07030201060f0b160c0503010603030e01110705220e0613030909020306090a0903020c090a06140d080403124419 69
    0x7003140300f03441188510340900340c00c5c4009003000081e42c0341038400d01d03210000b600c0b481c003c085080714048100f001049036000c00410015488a14038042040c18005140115859800c12820b0303c10650300038100102c00107034441415820f100302000390001203000f10f40c00345400e28400d41c5000b11480c03000d16842c091207e508001031045000c000b0305026000b8003000380e5038140a002451401c08407800701d4031902c9514154100030900100751480205008521001004c01c1046140c840c0c010400a070340c1ca110340030f0007400810020748540016022405001c0c49860700038940c0d000f542c0b01101050040c0144801c0c1d540d05466150f0140660000241040003030074201d00e232800c0c4041c9030380c025407070805000d11040786401c41419030b580741420405140a800611600411601c009040701800740720a000059051700d0007200da482d546404160010324002c03074681100308001d22a81260320601040006042a071540034840f6038010a070014070304001d003140505002500b1010007551440808 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 57084391 1250 57083141 57083189
    0x3050705090c040f06020615060307080c090607020406030506061008070206040210030609050a0905010605031906020702010c050f030304060605090405250f140906060f07030e220f0e0309010207 85
    0x10f0081c0041005100a607640d0003000e034441500f51040044030f181d804445140e401d1440450703002c0c00e525554048140c1d150614102541c01203410141c1c485001c110308400b60340c4500460010b140518050240c0e424103d080161001c101e503415000d1010700382c10082c0054000c00d560380c1c00b40d01518440c80c000300c2603a0803401060143c01068030305103003a051201c60b1032a5444071240c584500001c00004d40c031942050343d41e5480341100311640e203410541c0303800a0a41c0c0c0180c49800d1042c1007002070703c00c0b25510f4074104100d403080685c044d40b000c8100000c0c0000e40c0102801048181d13861031803400c1c292034158035840e0005248100c90a050034901b5203041442f414001051603213a24450305803545114410030542841d030902c240c5010003c40d0b000d103081411600d0011100705e9031441c01800b6981a11080640b525195201d03008000c00e01803d10080490072040c1041c0703c00040020000306501c0450707921103003054581d48240b2102560b40d80009258050315256030038460903d810101031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 57085641 1250 57084391 57084397
    0xe0a080d0f050108060709173703020f060a09020a0306020319060810050a051314070302030d030e0d0e1e0303070f06020910140a030f0f050f06010909050103050705090c 74
    0x41d515580c5032a000240101c03020038402d00400c1d55541d1020f0240c2d8030f224440d108058219850a15003002e10b0040004842c00c43d20405110901d044002162032042d99540501c0010310580150b0410728440c2d40540e4107010f500d0b8404d07030b03244c401c0207920026004161284400d0000809441d0700001144203040401d075144c1581c1c0100f0410300605840c0c20b100f03034450302106050184142440041047c4041d940034041c46441c020a914a0059050300c1d01003400c58100003a0030540259180800962401c3c001c0100540141e00d0208684946115480c80c0001400b500c004004048035100700c0c980d100f607100c6c54010032004074031211002d030300006421072085070380060240f00364401e1078041003400c0d000b0307050700c40c400c803a015104403c040064855115004c05040440002c0041301314660280c2e000d8507004103c0040000c06003002c41030b440480d1030030380c5c0358001c050002040048560307200e80040041c200124051115500d947c1d03c15542c1c1c2c080c2c0c040c2d079120f0b5900700d0001e413212440c0015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 57086891 1250 57085641 57085661
    0xa080604020c1603050c180c09061309020409090b0609040b04020906220614010203040b07021c151d01021315020f06040309140103020c0c04150902040f0512010e0a080d 74
    0x241c41c1e0500e44d03a00d8502c2d590402a0462806107128452400d4011840b010f101d00c100c460010071442d00c601c581c100800b0b40e0044051110f064664a00030032403850610280000e4026007000040a0040b401d08020701d4000808441c4160030720420080006d1000109540041d815122002c0d140c50704400104c82d4114908060928200c91a826055502070780004044500d06c410340120400c0c4030004903102d20603801644d545460800212005041c035001e4071354011052402d001100711650b86000c0c038542403e54a070361003500c8505c070038150201041c0b00c0b450001004002c5250009001d0704000c0c20380c141c49601c59000089065841c2c4078003d0025076805503411041d94a0382c9414074000d000256103000344514903403040744182c0a54040d1086445a1401f00001c2481c000c0c81810400075140319108410307180b900003000260403141d130010700090b0916504100d01c40d4105414802c102100c036028005030382c1000c980805110010400003032407500103640541d1650001540c90141882e00a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 57088141 1250 57086891 57086923
    0xc0203120c041706150102010513080307120c050c06060103020913021308120c010612020a03080a0216060309030822020607030c021906020d030603030e06071e0503120c0a080604020c 80
    0x108083c03410004a0804c0c4500c041c00c0a0465900300030300120b00304e690883d4405601c8004158450101c0c81c80d401440d4402c03001c0c6015401d420403080b44805648561912034081031001c0b56031800140203216455111400f868110f0900c1d0345e03080010908150044c5030b1151507800039075441003603c0c181941c009401402c08a032200c04012695080c56805441008419407a1200116120940360f40074684141c00400704004181192500410b03036014001c01400e61051562480d412058090000000c150326103001920752402d04000e803080e80300408510181140d40e00240c48481c0d4442280c61064040d01c42a445151610f0269a5205801c07000395100b4a0b0103050350aa01c151002981a030312607501385ca1500d01d030188258140d940500004010851a0070310f404c2c3d83c240480076100b03240c0a1b80c00814035074024802d400729802c081d84c3c01d50b400c1e000043c000521012091000e41c0102440c10380600e00211020002c02010015084e2032180b6000910301080c00f008102203214903081c15 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 57089391 1250 57088141 57088169
    0xf060d0507050403021e010c03120e0601090f0b0a0810020703051201080a0c1d15061c02090109050a0806040807020d0506070201050105010f18050d020303040b0301060207050406090c0203120c04 85
    0x10240083d00203210891080c4411882000d01040480341d14201030010384901444240d5175405484d041c0c500f000c00340c01c0340c3c3d8800c6034104088003000414001c20203100d001402c03504060b16201540d0791841e00038003810710b00c070080210503000158024281c09105d401620f402080c40c04940e40e225000c00b0a407180241d000109800402190902c012407240401111107940c0d001c41034907250b200012002484c0f036840000c0d030b00600044600030703440c070024a2540340000311b00802c0070440000101805195004c903c10542e560042c0840003c1c09085030036030002407501088960b603d20051004142c440040b95a8085480c2c4202741c00031701c0d40c400c00303580041c030f00144000c0c000c100034440c0c3c500140e449890408054020518003180341c0852001c441428100014407101c0122150102e030184000c2200091100051001d035000c0c1c0102e82c081c01c0d07070301d15010400c0141c0d001500042c030034514002901c200181c001040b640e018904010140710340c0c1e90310160003158010350f840340148060380 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 57090641 1250 57089391 57089401
    0x1119210e0306040507050306100501120e0705030a0503040306060503060405060106030c0e06040603020706060e090c120a0b0403020d02061e0f09070e10030b01091b0516021801030b18030301050f060d05 88
    0x5c500d10f02038039415000c99a42e991142444030708440300c1d114543c04521684068090381c010b94000e00500d03211002124807007940c0348017080c908060b40005035655003000c0390600c20040213020703180090404600610081c1800d444803a02d6840610500e810306544100018a25015135850881c110000380300c40d85407681e90740054069484003e00300c5103146803071808035945903407001070b50003075103090000e1450003060814080c0580d03d40b02002418420701e00903100050080c13060900c6130b4400c2e0301501c80740500e000041e1034864040c04804001540c1200c065000c008d10324055401000f20480540c03a881d0000b607a4101103044d00003440c60002c0301c003006000c840160418003128403400c90300045a903551071880c1141d04910402002141d2807010001c02482903003e411403140f90707901200341c41020b07030018920301c1a01041d4440b1a04560040040c800c5200100e40c0c0030603100c0ba810420b4084c441c0e110344922050042034410381158040d003c05850340029141c0c0758034410030400c102e0802d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 57091891 1250 57090641 57090643
    0x40210270605120601020706020d1b0c0b04030b011d040201270b0301150309020904020603071b050c150a0f0f0908010509010f060b0a02060f04080705010c1119210e03060405 76
    0x105a843d120307551604004211154800604041120140d5000d806030b00300c04c00342240c0900b1403114050070400751000c03501c042103030092200f004207400c0407590350703451451502159a60050340141882114904000d040c040480c4405501c140d0919003154014079110a0207d202194107034030020104110003c40c94080385801141030b03d54601d00d00401000c042d00480a0f54580c600085d006000b0300301150045c109107000d19007140d040c1c10510401e881050783c11a210b20005010350705640f050030b40b5800c40c1000c0f040525209600070880d494103015040c0a000640040e41003010041405125448140315581210141198070024055070a1541440d13010f0403185e01c0461015141110015170a0100003c80756106d0064024101d982d8031441d19661410001304269582c12003040080d001800c02e2180590300c0c1581c0c1c8880d03205881e01e0710f02030b00d0a82e0030328a041c440302071084400d0108284220041c20135018110180440303410700400c4546481f11100c098151250005001c10494 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 57093141 1250 57091891 57091897
    0x1b081b06040b0a1a010914120a030c030e0108010b09090603010e0703061b0807080703050403020c060a0201020a080c030c070f0615060203120708191505270a05040210270605 76
    0x401c0c0da009010302c2d004d440040e9288142155402e000c1500241d04029a4a066a07c4070780d03054000c000712010b03801c0603031f850308202981404034006040c600010041641000480000c02c030280703041916581481d0b0606082d20035094814407490080300000c080741d809400020300080e200d4103458040c2d503a4600b2402034500414801c0d01d000810541c0e202191041d144588a0f8546690300c280f140c807207031416401008045c10540440c090403101d10382d10b4560310000c00c3d060308140d0005964441c81240184103603000342110003041800c0050050341c3e82204143c0710880d40140f031058002d0018075006005240b03040300036100100c4810002012900840138103528680060080616618060b045030010300444810071154041c52202c4410705c00b03170388003118035400d040d910f200c2a501d640010b0200e41031350011050038040e041c050000c942002c1085034104c03090301400c1c0320a003030a500090101c00d909943c00c2c100840340c21100f4600c0e119654900c503c561408603440003c0c1c8407240200158 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 57094391 1250 57093141 57093151
    0xd030501060c0813210c08010203070206010e070c1b060e0d0224070f0501060608070201060e040f060f1119020109020f0d0c0e07080402090106021518070f090f0c1b081b06040b 77
    0x6d007500c4000072030050600032244038080d140d000d00103503130070030a00002e0300c8005400c00d401c00c0385600e4138000041c0c022806a0116003003200c150b10b91403814000a004207100007400d8011032600000c0401602d03600d00040e10240768900601c02c3d2010400644030314040c11078060481d49007040b05400780702040d07000c00c1c280c0303500e5542c800e46903840030020790a807003041c80390040c1011b0b050300003408109045881c94002c0e100b008049040034480d40300c502510801120100000800101c140c00803000140c0c0d1296000240024000240c550300010b0b00c40c1c0c54014000e010700808070211040002d0060380f0000340920248c0c445440c10074080040c130280342254101d020b5a110400829203030700016035007490003101050203907036035a454035041e146140041d04000c2d512683c080482c2c1819800b281e84050989410300007580701107940c5050558025448c0c0d60140940a100300320814a019013034040e50390001190ba035500d92001d82428414040003401c240b50040707105000c100103040d01240c0c003036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 57095641 1250 57094391 57094403
    0xc12040504050f010b030106030906021209010b01091d0a020d020408060a050402130b130f1d1f0209060d0c0504091a0a0f050607020f030106150f020d030501060c081321 74
    0x155146503108000c60f03420300824940840c24001084494482d8103c0c000741446010090704020480e40084c0c100c071800d0b244c04400d651114521511940c0c0800294001c058400c01c56900c0401254a22021100074290034070560700000d101c1010469501260003c0010000700c403098036040040340700801007170f20100d10410040403807400001950240d130704040340041400e40181841c2219a005200f00e002809032142c0b1291100c0140b00034128184021243e0005845c26401c1003144050f010202060007001c24414000b07000e103a01e80c0c03400e44055042d1840005402603880d00d0960741e074055a40424401401d04000061b4040014080404500150390325184d0342e4484a80c040302c10601d0040d1600300206001c500058680881e0008581c01e020740002006d5840d5000346500c0c280c1a42d118001c505e03200040c030b40d00d070f034100240b448191143c03400304400d5051420042c000da092a5000d05000c0012035099962009046040001e00c035640519030141c03d00700a0f071441e01c103400c40503115 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 57096891 1250 57095641 57095651
    0xb0915010f080c0f09071b02031e01110c0a081e0f0702010e040603110f120703080a300518070303091a090f060714030a120c02030a090605030c0c12040504 68
    0x40c90400f0480401d01c100b00421781310059650501c1100c00c12100f140c4c80d514035107140320080141e01c0c2406044103100c0004400c0c070010a03d00e0055007585c0c0c0e008280c048805d020040d003641098003098100149a02901440c1d80d0b00030002000518000400c4a18000c140000c03407403400d802c04401000824030130b0b25218040c076240f00400044440510000c0d0040c2c0d0500f00c001c64514082407016241140207060305c90203200c840d02c040c03401c00141c008481c1100c0019208159980200d9518110780b19141241c48007403010b009401c544401184815010751220f002c17410282d0030040320808040d42404403640c1c0366580c01c0042c8080a030348148503820301c08806004060510300d0864012400141c0003100300c0c1d2840c01801211b070b00909081e12841040148000c00c82c8050000380511314140d80c9082c1c200c4074101090003100e200c804220250340c402c2000340481600800202c0445036070b414078586072350319025404582e10844035804050b004181100300710500c92805801134070810340342005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 57098141 1250 57096891 57096913
    0x7020c090601020a0b011a120f0417031510090302030d020a060c09080307020d0204060b0d06030b060103061202190510020604060e01052502010b040e060601030b0103020310030b0915010f08 83
    0x130700d9410300d210141508590000500c080e5080c0c9011030404d40e90f110000d0301e401e032284900d22103982c054940d21b0640003442c0c01e01043c0040004000c01d90030001c6c030014a14100002030301c401d06403c40510740118a88007401d0700e00760058810000468026080e25509406c443c1c00035107405901d001251410310346800c950310144607102d548140c3d00848000c510300405130b000c1005505045108a038003544075040806c2c621071100c0541a0b80d5400100810f20a00710b1070a00440031000b42114101440c080041000030703002c0384100c1200c7d40550365a222040e1180140d030407004c89400c138603040900704401c00011940060b80ca1322a45c0190400c00030a0341403940c15081c0c400c103403040800202c1d10104002d05116800401d04801c0242c00002440b440f03400c04202641c64100c005007160b00b008080007040d507098021011140c0c8246000c6255113041002840b0180a034080900780d500d0000000d004000e04000d00c00b84000b006c0c0791441c03150381d280c01a0070101414092b0301d41d90702407400072507 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 57099391 1250 57098141 57098143
    0x80406050a1a1903050d110f0607050405091e0115110a081b010608070902071e0c0b0706090503030c031006050a080103030e1c1401060e100501110a0b07020c09060102 73
    0x10b10500c0145209401c5a684410003040309210000f44506440e040b800000094041103007025042c0162a5444000641c805e06800c0001c00007802a103508400c00704442d40b43d1044c00c4400f529021185c0d0401600e51810508001c800d48506032544102800045020901c100c41e840742500307943d4400c0c003140d400c244002d4a84a0780318004002c00c10a1041c40c0e00343c102070108032011701d0040b000003030466940f8046c900d041e540350f106000c0c01c0d500081030401e000101d80301d48160842d68001c0d04294040b079450b200310103d00e11a0500e03800010401b0410080142c10069040340c000d4100c0e80c50b410031045003040c561050302c4180c04030b48980c2001413a180a0800e0310709403150780d1281003ca80c690f84044e5881d0b2282103940d50310243c80e80300c0c1000302c600440c2c6695458002c0c01c0038040d054003140325500f150700301c0c0c201c1c401c101303180c00800a0024034000d80707401340c1c1d0b020303c1c0072000c43d010260f1346480c0102e0030800074000608801040484da90020b46802d440d60121806140b41d26060016 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 57100641 1250 57099391 57099401
    0x1305040605030601090506031009120807050a0c03050c071e090c0c11060d0e0d03060f05041503020d08090603010e0f070c050604170c01020a020601140613031b05040c080406050a 78
    0x7441d0103801079001004841d9555006c1540b281000e41aa0030010b100603c0b403007103174079010048450441b440f40c1450071032f0b4010300040e030140c11070a080b858510060805071481111480040400000150401c145181440340000600d81c0c0311010b01c4c0e03010a040f02d940801d40342e002e001c2c2814034020a640c2c48510402c203440040d0b07000390030101d070031007980305000440d84100c40302d841e00c2c0d898000100c50800704009142445e100ea55001035164140f5800d0803183e035459229070f12032030411400c21461003424841c4411a40c1c120340304940074020b46404021070140d8482d1640c0b1110110000074551240c0315100d10400b40c0c810265155038440b1010b072500903030004081cbc80d65205800083c000350606a01349000106e0700710712410965000401c90990b40007441500041c1c01243c0100004110b003580c045484104032030040c140240b03190705614003180d900c0003400d0030344800d810703110040020409002500015100344540d4070701074800382080000399401c54a00c0e1a0a00240c0b41290038458 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 57101891 1250 57100641 57100649
    0x100219020a0807080705070f0806090105150303300403180501090303170403020703021c020901080c031203131a0118052202010201150f0e0106050406050d0f0209030d0513050406 78
    0x2d1800c024003a00c801900d900006411281e9214180000c01c0c1140011103a40c001c1450200a014910302040d00ca402d444014100c0401007000c01c80100f43e5503404003d40b200c2441940005841d03207150031501810311080c40f0ba101c07031031003030780140320074150b10055024034101c405c04104080d0b42d8070401111892814440a00060a145208800c011420603400e801c14042d00c1102d822980f04d40001c2c140c02581c45404d148202004000b0046042c400403140c014181c80e000782c1090141500400e40701c038450503016241c0b18000000030005810030203140c0b05503170409011817502100c280d400d0701d110003c0c0208203403440b010244040d540880e005085c030480810304846d4400503e00c0c100144145000c600300e06554882003c903030380b036070320540c000003c2c441e1b00b2101203101d00c2c010340c60795100c006070004c1080010400040c00410341040803107111617502c40c400a000e20456400b01d00900a5602080d49409003040c0b50301125404805052a1607030b030100103114640d58410072044070340601c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 57103141 1250 57101891 57101903
    0x60307140a091a042a090308030a020a211d010209181b070b01060906020307050604030e060403080712020609070509040f020d0212071a09010e12030c100219020a 71
    0xa05100481e40340e00840034050911000b1800100fa500009041d60540c203644200a01d8005078240011120a0746003046407180c1410240641551900c0640d48001400391150340c1c2c001400b00800380c801c0c81008900c6084051036029504445480c0380039142e20340310003000d181c1081c0c000c041d02c4010310031250f002d03038000d0080325036003d8007a081c070415400a0422620b003010b0201c5000d2030300d910340180101840790b88020322540c101500949245400c1c1c0102c02154030030b005820024100041d0a50010741504014511550407400643e040c800c6400080c003500001c40d610081010018020f1400b44d45030302910825030760001290703500c8940b441065402a445000318010480d130241e01d40480340050302142850030b42d500030400200400c00c0c040352a07402000b040054140e1103021303c1210035000521440e00500400081c031018040c15403a1103458181a20f6803101e804200700d07044007160209031f41d403ca02d06404200250008180c5640c1c0588510301601402c0c80802c862403404e603c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 57104391 1250 57103141 57103159
    0x501090606170a1803051c051314101a01020105010605031003060f11040609030b0a090b01032a09151212050a050421060b030a030806042c030306030714 67
    0x803620795410b8010304111011a41c91034800c40c00c105500c08000642e010b40c0b0b81c80d81c1e03071145a010007185c261140c00340042500d80004c0c4040c950022400c01c1505030404241107240700b0f1a406d56092200b801240c101c451300e0145800c0c0f021401905140c5510400d8000304070580c2d80d40015221440f00b11030320103030440c1c6940d013070000a62550081c0f80c01c00010500044401d4070550500306a0312540142e408a001d5803c00c0081041d0003111a82c4074146100034004071056580d21840003030b06020081c070124909112900800e05004003ca4041c5028003d64620750354400d40c500618041c1d2001c801c12401c40e202141100100c040004480d038021010002003441d1075045400d504410231980400c54100800581d00e220a680030218a00c0d6809508101d0751b94030b000c0040f5605808610f02030f0b0014003074500440d4014006540c81441070303030081810402d1441602d4550302d02482100c0c151001c4441038184000040514840d00c0709034200c2d074959442d0f16031010031003420501d803640700c5524 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 57105641 1250 57104391 57104417
    0x3100b060901260c0c0609030f0405090405013902010209030a120504031b060f020c1003051f030c06030e06040f02010c0201032a0906030c02030405041503050f030d0501090606 77
    0x30384241d503c40b048415107288400507180c0c1800480f100380c6014090000209405042c090309000311500014982c0055185c010100e00034005030055110b580d20420401e0001400c0c03250a400040b602c45000d4508040340c4601072914402d41c02c903e1008044056140d15080040e0051088483d100002001050020700694903810340d600060105400c0203400c0c4400000142c500c0400300322180055400d2b243c075130034000000c0003044d80a40c100f007103500c000c40c030300001d4a0300a24240380e542e00d454085440e40c1d50aa540040c03d4151503009180328041100005004680380d070081641c25a950502080500c540d03a181e03298400d88018000c886a81038100041d801f501243c44140c1c810705000c603000c80101c41b10f404038506454030919040100142820599000c00081e0103000c1c607041c1007142c4002010000e540340600e008d0706008030790740c40061302801250107aa00c002c640c070408943d05030008040301ca40700c4d00324105a00e55070307003408004981160f4600481040d28540ea55044c141100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 57106891 1250 57105641 57105647
    0x9050a14060901030b030a05030304170304080304060c02010209030a03030501210c12051504060b09060301020301081005090c04150e010506070201050a0807031b052a030910210b03100b060901 84
    0x40182c1460605030b4070006510940c500b07010307040865005c0d030055a240d20307103814500078000015a110700c80c21000c008220000d41640c5c266904190801400101d048005001380d009201d079044c050781c1482504002802c02d54980c03c076034165403d600000c4901804101081161954000c004048040e03810b81030005034440c101c40c581881c02481140c802e142c2c120044180304805480c190750040d11416065002d003002d04d43c06410180940c001c610719032600c194151034400c0e102c0144035213500c83c00841c003224402c0100a01800f0020000c110713a9082074080c0341c600700248100d2200c02039241c0001280d25040d800d44040d150180c464624200c1300d6107040f584084020140020306640380130030742002c3c144904d040c262403056101d41c1d60703814612a8440c40d082d082280307580760b00c001d001040c42225011007524164075064a005862940e140410746400d43c240f4401c0401d0507561004d211070407840d0f0810b0a21200c254151060810160b0404003610542c02e07805070801020024020300303501c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 57108141 1250 57106891 57106897
    0x40b041728030e06040f14090f01091a0402030f06010f02010b06040b031e0702031c05090a030507020102150f01060306090507020c011404030501020d020c0609061b0a14071209050a1406 81
    0x1c8a4a084103124a0f100b001a4280d0026000180c0c2001110424800b1802100560181d10400c8485403c0c1c0c1c901420201a51038050203502883c41d180d2071032080b1509140c0c125554803400400540d00c92074040c490300e00106040354424001000609100c003a14011b11900c2c0c0000750141c074141ca81410001030040560001e010442c403404211403442b03081c2218038045000301080d901640e40c8000f080d11061070f40700d0044080a09525200600004104c0010b529900b01d52604201da12000d0f6800141d0500000616120f901c51240041007203604c0d1401d400340c147d540c65141004142e0300c450000046503021521080035a004400900056005002032091001035000c201d00d001e03266a503203401da81029216021140d0007251a840c204030034020070b988107800b000103010794940380e0301e17036264044007001c00f41403100700040c00d00406124148801060009501050790b82403e03160018801d01e8031220720340019689640850035180a170814030441e1402d200d201c003001481c02c2007090b254 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 57109391 1250 57108141 57108143
    0x50307140403020d05060603121c0506060c0304060f080708040809010c05010605031f0e0c01050f03060105120f04050d03050705041e08011409060601090303050a030c030908040b041728 81
    0xa800c1c0400030060b5600a08480d003148207102030301031401c10400b45490101d200030300d050f8082051140c0e44c0c071114601c80503102800352840c0444c0a8840301d0202c1c2580c0710b41800140300d40030002c0c0c0880c80703031340202240d0055105a0b60300007a41e03407908421190500140c0c2c00600c40c900400c4042102c2d813048100a010310700a0700000f540d2680c680010b031500248541413100c1000c00d65100082c52020f1260310121051040a0035040c102480001c01a2248426511f188074010000c40c10740c1c0d00c540152420b9161041518069083c0710500901403142201c088485225035422219018860300843e0b000b040c40b900c62500b014109042c0340344070100480d0b400f19582200d1030004240d1000d0081c0b038441c40f0340481c40301c04c1d804d0080000e400c1c00350060109061110b01c43e0100002503000301111f01004403842c001410304841c0390211f014200d6080c001e40342c5540850049110f00d85100188200d0714a06840105080d000030301c692038041105610940001540b803102c074030030541c94011401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 57110641 1250 57109391 57109427
    0xc0209090f01050106030b01090b040501090509041e0602040311030a02010f0c020102030d0606081801090506010b03150a03050606031603020303070807050715030f050702011a060d0f090506040201081006050307 92
    0x1c560401164210761003640110f000a441d0001c2261a503081342038500544040480e10b0b00d086e06080000e041c40d0f465204050040407200002400d004240780710a001e1045031501000d04001d505000010303410078001500c800085c0303c100d117500d24000698a81030341e41a15034003000450043c064405000c291801e9042d8002000340e40380c100c20500c6400045c0034543c4882845007090b001905041c10400107441050785070000c450701080b0002107290455400f00c00140c1d07a07503074400404410203c844c04803a00a0100b100200c100000460002e00c1044250222030400c1c58100c0b09243e850603610020b9015002082490086413100c4011700358140603200303c403240381e81c03800d09192180c190320007900007994030b0316611903001450243c41c3d0000154402400401c0c101411905040441c0f111035102d40000110303926000b041c0c5c1c00c032460464400c44100007d65180c14010380b103040c100ca02700e0002c1c08000000d8082480704e200c1500b03551041d600c1c1c904584d00c1030002d0314480c220320012151 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 57111891 1250 57110641 57110653
    0x9050c060307030e01020d06030c0e010612090215030f01060e0618040903020f0d0804021806031b041118040e0d020307111804050a0506091b060706021612110105070c020909 76
    0x1e91361300340020b2540c0419001c0c00221540b03542000a009030706034004203060300001d0010880039600404c0701200b116003650010f03001c1d06a100003004c17a80122900b061303200011080055211800b0041c41c101d515139200e82020003c40e108201d0075116100b81c0480c180900c1010001b14282580001c0b4150302c04d004071032055030000e100c030345000328203140100014190030401046052000c40608050354150300e002c483c1c245140000c0c0c41c0c2500740c003884188208001c051609030394503003018540154204c1c102d5a10130104600c0a100800100082d0051342080102c07d00751000103500c02310b441c0f03954042c5040520650710b9035985981901c0550344080720020200982401ea0000da02947c8244000c0201c0c1245103081c508010006000c5401c1d60054030a460300420135210010108004492059480b2200c0c0352040090140364000500c6d006117241d06000c005141c032100e4004002510fa01c0a03019a801d101d9080c0c0301c00311850400105040c02d042c00600300318070090340143d42282070341c078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 57113141 1250 57111891 57111911
    0xf07081201140f10080702070b1b12071205030406060306061401180f1203021002030405010e12090607080706090f050c0f0d05070e0c04080106080c0901060309050c06030703 76
    0xa054002511a0200d16034020041201ca070300c1d00c000381c10b050030984041c0102d541c042c00249000386160144401d110001e000141c400307200f4002d81e00589015080302d40c030741c0c1903021b00091140d0141039111a601c210394507221165201c40980e144240c4c0302081040380c9607001e03401c0b21150000380048a8181e1074200100004460b401428040d0010002c010410040c22000401c0103412080c244031a205511081c8050700c1300d01d00c540107482d66200c41c420070fa83e10745022441d00360032028002c1071030300c003100740300401006400913403440c040c000440f9201c1034040103100c400d00c20741201c16800142003214500103142c000141010714058600018040c015441e01d655140349460102d800c0d8103c0070f0203403414a020844070721804400d55400c4015812607440e02e54405d2a4090001e81d68000c400003283c44a20100b150064440c00000380304c4195642039295a510795044554860704180c400030801620904c20501c41d142c01c0710042c403200d0007100500142c1e0b031014010004054540c02204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 57114391 1250 57113141 57113153
    0x30a05010c0302120112050a11121501090608030c0a060f0b090a050108070803040e0408030a1b0207030507050d03020d030b0a050406120b06060705062d04060209040f020c070603020f07 81
    0x222004900c2d0301d001d030b914806014241400d0b201600002d803450284541000803410001d0311810340366102400c01032696010001400020180020b24543e03c00d48002240503106a11011b04070749007501c003805055100c0418945a0003100b4401076183c0c41100c408000c203040d81c01144624881b41c10016501145502141040c01d04440d40303007010761140c004000d0f204040240390011302020000c1c509041c103082c09001c11200c09480603101c45408404514866200d900c0b40710120181c001c1d05034402c0400c0d10203500d0310350910050b00c0c6405100790009031828100c0c841400c09500da030150286602c0000f056008004e40da0f819504203000c050085450303101d034031901014059140c0f0103111703880c00e0b282c1041000342c000d2206005031000d0240c4800543c4c00602c0e590450041400310043c1000c16201c1d043c40c80a00b0344c00c190100c841c4051000344041603005205812007520140007407940c86025005034800d07103045140f580c2c001c3c02c04100f800d10a50240a0b04807030510901e1a001d040d4482c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 57115641 1250 57114391 57114401
    0xc082e0b031008010605030c06070804090504150c0e060415031401080102120a0b060304021002010e01110306010f020a02090a0209010302130605090108070801150e0103021c05090c01030908040501030209030a0501 93
    0x40000600000902c000c4040003080840201100d2000344051414000800c3d03c469a0540aa026105c0030131800c0030084a041074901425800a04004901d00ba0a1465800c01c0341504840c0341468401060700340c5204030050071020b6401b43c500c6160a1401003212192a04041d0750810140d80c2c102c12494006e101034154000c0c0301143c00561a00030a0400e0365064102900703a1121070b01c1c2c0783c0064511384404c17042c2c0754083d4045515014802c0c403600282c0c058078201c0350007260343d440c206002881d00110009580142420703039410160005000003a6510840840043d5020034428001104c0d1501a0000d11481106140250901c02c421074944409001504910003182010404042e03a59102800170703841140c914203c1a594584011489030207204107803001085135410200c8826400303078040760000c03154221020520400e80b10108010001625100180d010352641c8804540c170070b0185151498004000314540340c40d20300150300030351000f002e80d60035005000006010917001c0c426 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 57116891 1250 57115641 57115649
    0x90904050c0a08031b0c0904031b05010c031b02010e060a0c09050607050102070b0f070e0105070c120c06081303020714010e0d11030705040c0e10140417010b03010c082e 74
    0x445d100c80d000d003d94031003481e0001001c0041d0340296000011a595044426009034042c18a8401c00d141484608002c8800c540041c0003582041c3d140c1200c154158030200400162411402030800c203407404074240c07070b007600301c01c8000d51200b40420b824003a15404010500303450b05145a05c0c07942d0340302103040380d00305940581d00b81c2d44c007003424018000e5814543d9031110000b01e04402c2c924000c02c0c094010f40001c0c0341503040120201300352040010750001c2d80040c0801800e51107610780d191420044412550041c00700003515200802c2c20320494200c047d0b2210362640140c000141441411a901000da16103181000f0a90204800c2ca45a426035814a00c0c000c08a00b4500c018110034540740806a6104501403031070b14500aa1441e44401844038480040350250802e2401401c200c5694030400700801c10b00b5800600080e11400b1041180c4903604124024481c41c0d0040041608a510079410071020984401c00250614003407004109144102c08081418101407840d61103c1d40e03035600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 57118141 1250 57116891 57116893
    0xb0d0b060a06030902010203030a0e012007050d020c060403020402091302120114030a0213200a0201060305060f2a0c03040e0421140c0705090901050f150303090904050c0a08 76
    0x10510109081c8149440701505850809000c29203090303000075924400148045c2495556403005110300741d0a400000b0100c01c059000c45215484489075401079002c010111000d100c9c0f000100121030002c202900c806500400b59420203140d038003804042e5000820950b4494031003071030340c4080c400382e1001c0c012842603144c10140c29818441031020150580c10540d00c80e034803002c52000169034441030702c504a54620004901d600d0001d103404c240400a00340f071040c003807000c6844460303654150302010842c2d00550072030303030180c54842110403070342c50a484002320703095181031003100c2c3d010f9106801210006916020b29015003802480d007941c00513000403203034016120034041030040e032460404030001c0284005400701c141d0000680150200e030301e1603420031800705c2d800081c620309121400080002411228442c58040e403024002c140444400c0440c0134844080351fa444040300c1c404150010180046141c022110204002a10014001c0310144120300a91085451384001d902c02058540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 57119391 1250 57118141 57118163
    0x3020309070e040b071d0307080313171203040c0b030a050103020114090f04150905011511190b042306040b060301090507030209090f06070914090601020604060f0b0d 73
    0x1000c55003420590b40c0056038069200c0240700205100255581d0814030380d081041d880c140c2c403400c451210388440802a030600802200160140011006141c00c02200340900081c0e0303200d01090190b000b411011580c0d9a001072801c0c3d20028240e40110b40103030083c26101c8865a817071300f403d64190b10464920103d591548010011544c01c4a92190646009800203080070b6981021400103130000500c60320941e207031852018420040540c2001a04103020107020750f68441004107a1041110030213000125050003000180b00701040c00030000502032503a9540b103845840d065101d11001d80191405c2c0c04d007001c00d01682d003140c001300004070010302c080c1c46c940c9403030700b4003410590000300324034041c4c1d041415140020310041284001c1d0380d812588803a8589620a4013403815405003036540d1705100d11810f1080842c0c104407880c0031605130191010b5030b12440070030f000b0f0074182945c50901682c030100114000451300d4201100c210104074002071141902800294441040007055500d00810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 57120641 1250 57119391 57119401
    0x4050d032106030318050603130c230a1502030301030803090102040b070b06031e1e030d020a021c030606080a0504060e01020a030c03050108030708030c1305220509010608100b0105040e07030203 85
    0x1c06811405c01407a013050303880091810001c00c03118807009000c10300301c9480201303e0042044003110038000d8440707c0f1011105401068091181002e22401c241c4190240308000039243c2001906210a00c9198061030860740303035544142040d0800361950000d035409010208084060030301a14103240958403041250a02130241410441040d0880c0c40d1000d6410070b040c034441c0c0000e035180910341c000001000c2040583d1303030702e805d43c01100f2490786080d000040c0480f4444d4005141a40910300c580c0c01600700340e040c17400780c0464175580304c6c820222340740900082d901403a5502450348075000341c40100312a101c240144c0e089038810100320020a507503d40c181c0c5a15450300c1210301400701c030300085240c00c151f40c031804054080100391400d03902c40000c00794581c584c80000d58008010107804004192a101030400c107202c2c1c00001f0070401460040092542c140c140141011609540c000e0040d80e0580b0904002400110001da41440703c1004006441020100900d2042803551307030058583c101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 57121891 1250 57120641 57120647
    0x9050616030b09010f061115180d0c12030903020a060f0e01060b13151e0302030103020906060922140901061d10050103090c170d0305060a060504050d0321060303 71
    0x45082c5a6020750004001030181003000300014083e0780180c286003088074103210380c070740c038088000c102c034051030300d880c4280a202e040c101d0900c0a89900b903000e6503200400520200c07221407001e81d01414120707444403c00007190190b4403401c581c0b4000c0c03042d1801400c060f280c1c001136810010300805915a641e00d20101d2200a12030a8041d2030002185031420110407100f02900c92103001d50b202c0300201d0a440c0400070b004d603240aa81111003681e03541c1203561110701030004d42091200343d00416120740000c210303180c011308070b5154420092941c400883d50f01c0351081040c5000c203003a0029640c0b0514010401c0340611118030a8481e000003207192410585c82c06c403041c0c030742c1c030540c002c2034400424000a981610b03264001c5c2c61003841e00042c0d0300c00d1418400a00003050380400074218031410f2140300c000c008250b10071650790382d1718284001e850300020b0080e4030250340306e0540010002d010600403403815030b6107559860b001c3c0c078164500e8405000740c94002160324242007007165441a0420800d60 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 57123141 1250 57121891 57121901
    0x607020c011e02060c0a030b030a060f0605060403022409120604020a08030703120209030309040203010803120916032307060f02010c170711010e010c050409050c03040221010905061603 81
    0xd9001c0103002c42000710602135030b100005400c070021140d010800e44480344c07080d4494150040005d04880d00402d150815070002d001514041684a003001c07000700341401c0a80440e401c49902070844eaa081480780d800181d05003009550030346082081040c405240e6070180c0b4080c5451140b030160049080510400545035040e84c8803510725001400b1400109403c25a0710501c036216080140e0b454840c500081e007144200c40800758000c0c03000c0004180d001c0d00002519032001c1ca170f030707680380c040e02c4d6100300e16a02c13100e0302503001021014103401e20008658484418810080720084039000da1440070113400c0040a400840002c0c0d100b000c030508041c2d09000780a00c4c201d035424100740315103040840884d1194010100000d229061031010f0300135109601409000250310003c1010200c15100140b84e42e2151140d55103150402c8045440d01c804581105e00855000307058062003e0040340d810036080410300e241419540c1c84c03958101240c011720610b031081c0d000f83c0d11074901e4966460040c08541c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 57124391 1250 57123141 57123167
    0xe0102090301060e1e040302030c01060e07030e15010b0f04030609110118030203150613110310080105010b04030b04080c030c0604020405010e060d03200a06141303090302100306080607020c01 84
    0x11342080c00b800010000640c580f00d9484612145d040c142e075660805900d54480c00060640e15882c0c0500002c807800c0c0b01070035074000d2640e6503041c4203510f00b4000e0207540380d0869101d400c01ca1045401040388064540c010314507103a0350349200e81495500d0700c60394102c075403650040c1c03412640414901241e40c0d0150006842030702175010320000e2400c54002c6503a0b515803003854860382810901190300380d079030b8a00104d428202d2103070030301800c5640e00b410b0710280c102f640c411005000c100340c0032800d0101801a241030b5040c482203a0b04091a503240c489000030064000e0303d01c54810031150900b04028070040510070346000c008c092070b003420701c180421103005a02c20584040c1030340074040560344a10054100542501e0f20452a092040c008400845092860f444920801c0303003c1d8108200d6403c80c1904d102c4110b0b82d0360252340d5848848030426200c1d10000d0000c0c90000041c001480c1c0b0440d050b182401c0352800240d02502e03024814a0f1480c29034054000d0390043c11210350035070b40010844004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 57125641 1250 57124391 57124409
    0xf1e09060108091c140c011a0307060503160e0904061a0603040206070209070306270e030406050f0708040b0304060515030705030d0507020409020d080403031205060f010f0c060e010209030106 84
    0xa2030b02800f401e46a440480080b800c02103400115049a8031400303041e486070407070402d0700e81c3d29110110900e000344504915015140703503402c5565034900e404034003102141d8054440a1071075403a80e480d07000b0b068000e061340f4184541e4034940c40301074a0709840e5900c02c038400c0e00c0c0060016020b46440e180084420203991140404004010068840005507000294180c0c2e40b41d446031100c62064000d04495000351040040e200000c0042c60329500480d80b15644c030740020014181401503581d240e11680c0252404203001b0408900014803040003480e1290044207014249625662008a140d00c250750660f61a6210000d1001e60f58000000100011046004110789440c000200361180803050341c04080c4100411060195100c603001b2840e601d038020511300108040c0d2a1547c980d4000707000039400207250540320340c4000024410300340903000040400c0c0700b1103010300044488a92030308120003000b4101e14400001545400340220f96034282c400562207054040c141070840d952903100d0148 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 57126891 1250 57125641 57125657
    0x109020f0a080601030b03120a080a06210c0b0f041d040302070b1806030414060109110702040e1f020a12020304080d020f0f0309160527060f1e090601 66
    0x8180d0405049540391041070400d6001a40c400307006074010240e106c8180c1d054040c100b1aa10a004407400402103d0b07130340e0311413944c5600d5070a0a0000c44820340260a002003e80e040c5601005c055030015400034401d004440d0040c1d16845025070719044103403c0d0b8004040410203205100800724082ca002d46800e40e190b0452402d9203000350344089a00c40c1800060b40000c130740f000c00125503d500140080508800d0707503030034945844a0940880820040035004a60010a0700d05240c0a9068481100c0038010b0900030303281c0820004200074030035040c5502c61a25014101010400d9407400c5280d80d142c0107072205c01401c006001c403030040c4200b1000d18030400030000010a103106480d544514040010b0b11403a461200f00f00601c2a02c40c40c1d40c1b1017038003104100c91301500041c0e085400385aa040b90401a5890f01880f02d42c0803104007100050b4924841c54443e80403030007031194041002030011760170143d0000403503441d41d000c0c5a8030501d44d0000070701e40d149090034180c55421803028646180 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 57128141 1250 57126891 57126907
    0x1f030b010608010e250201060302150d110a020a0b06010507021e01021c080c0702060f040b040801151523070507141009030609020112020d0e010c0305090a0201200a0b0f010902 77
    0x405400d19101c000c0381c07512440044e405c0902c02d502003000f03941c0c01380420707403000003040d10500241c1000076003000b19410041a003d50070428400e80742c00b581141c0003042e080100356583c40c540b1400030511030401000344000b10159440b40c440700d140060000481d0040032190000a04200c40c0504030b4808044511040c044a0750000c1000d612880003e060350b281c030390720f20000c0c03d90b100d0b920070204072440100f008911580004020301c00c81c2d190500800840c820400d80c044045882d00c540c2841081114598a0680c098031840d1100e6207080c26000d240a07640078130a5107074121120031b580c01c0e40030b200107010f0b444106004070586801160200707004200c00c0070090403240680001480107450b0480360b0116405201a441a0403400e4130654599010301040402054958a010706560800081381c0380540a44181800b07081640e01900c20301070181c0066541c010380720242c0304112410000c2404030b000600c504a04d9a10508026420b4100003c2412004c501a049502d081c1d10401c6a01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 57129391 1250 57128141 57128161
    0x606041202010804020301060816140d0c0306050a0b0a060e01031a0d080d020909040f120e090105060702010207030501051602070b030603030403060c0e041a0103060b040f0e1f030b010608010e 84
    0x40d44207582460f2003070b0196254408240500b82130f9101842c14482c4c145051902014171415a059414058560750540242c0c02001440f500d401000303484100300c0c01040c00804c24940010360f1207200701c00d021841c00d40945c0462442e0310203920a5002a01c00c1c048032040d5030b8036014201d6010508400c0180e030910380d80019203050340c4030304010200c400020f030a043c41402501690310303403400200807500c20724060810007000000500c04841c4400400c045499070703030240c1034542a1110280071309a103607081c4018400c0310389c08284103a0642c803601c00c00000040d001d0003070520030700954407017500310a114013000c0c2c90500190440280302d8003c0c010046075807000802c0c0c4044a80042021850202e0100150742002c100b0502c00d4009080011700750195040c90402454090281d9003041f20b54ce0b0f481544007a402240a180385007202000104018940c201c1050b070001005500c8401d040d0982d0916104a042035204580a154400040248607044a4106d004000c821030085491a0bd20920 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 57130641 1250 57129391 57129419
    0x4080306040c1806020309010f081005060c0a170d050c0a020c130e0a0f2f040908090d0c0305061308030a0e100e030301050a0f05030a0f06151508060604 67
    0xc0e80942e6030350901c5140d25218100807000804181c0e0100700c402e03120000291a90b01c50850b490120f0744021004501e113119049261083c10359824035202e0904140c1004102d5204440d44000d030320501313074205c0c040b070400317403030104140801c8150039075441e4a80001c0d0182c43d8000c110045c4044180503c910325500402c40e040e04032002c82e4803800300782d41c0d40104401041120071841d1580701d0000004204000042840c0342c05022b0b00da6a040400000c683c44a0081301d03060b04803644443d1040742c030b0381c1d04158120003d04d601c900c4000d070078081064007141c03503000e0340c1c0b4042d01c0701e10000340204207006003840440c1c1c02200c0c10510134407464103a12113205500c0007500d00700c1401d13034801c4e002209000900c510021104040700078010307811200c854942d681c1003801201e2055140d500300194458000d200d800c101c07100900500400c1b82141c0b11010084542d044c01d84201d5151241006240c0d10030384417202030060f00051030045050752000418900300200400d01030b980401042c0018400d40c905 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 57131891 1250 57130641 57130651
    0x6020706050c100f1a040b0105040e1504150609080105040c030809030f1209091f2112080103050d03060302030c0f06071e1407030c0b09010309121214040803 69
    0x4800d035900c4400b480a0714000341184001d00c000d140403200d845428090b00310f01d654004654900c0900000f44042100310f40d507903401940801c00411040240388091048258064504040d5004001d11a4042000da5054a040350611a005042406000d42108900b8043c01810b40204450310303144e1303950000100180805040480c010501001999007088102610b516000940320a50b04d000d001200b1504450f040034401c50380c0d00c0000c0c5c8503410000f0003080714602400d00240c1c1e00d246c4030300e40400c0b580c850654000c80784040c032036001099402004403000a034641c2c400c03590750303d542861401d2100045c444001c060400c042000540d800288101c103040b011070f10f00004413040d1001035964841d4401c000c007010440b80910318200e04284108200701e005100300700b0041c4801e80f54981329000f60100074007542900005228001c1203a01421503400c040c10000b400c0901c81d00c1701108281620400d800061115031034082d14113560040e042600b007503030444099401e113a650103085010080c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 57133141 1250 57131891 57131897
    0x6060f0c02010203070606140a0b04060507030e0402132601020304020904030305040f0515010312050c0a0201050c070504090507030203011d0604030309021804050106050f12060609060415060509150405030c0d05011b020106090c020706020706 105
    0x90340c110354479603045500c9100e8610012280b150b450400e4044940d551880080c1c0400c3c410540c01c82010600890344510340c02005051240d031a03503825401428060000d903035905101c456070000032400c000702817034001c10204540c45580740d45004070b0300d4485140e511007008000e01a00b0003042000503c005110f0342428402e44502d1010051454194168001580b242c280741c0301e00d05100d000700320542034074002d4000780b003090601e000c00d00700d44040400c80c3c1150751182c80001c0200f8401d6200c4600340788020440c00650b000005d0100d10403805076015140da035075501042140b0703d0010300800f4000c3d0300b030381d0501501009040c0369803102801494103024910311000031303006a546a1004030444070b0021710810f02d50311084010441c0d00b002034950301030b0440b4828401903080d25400d540071100024001c0c0142c9200f407041c055900c6000100719075a64803101d1840710005a0790b001e22034840700741d0001840518098684003076030f01c9070710f60601b55080b5120500c41c1660114450049e0b1300241 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 57134391 1250 57133141 57133157
    0x702270a0f0b19030204140105010503010905070302091206070810050604231008070e01080103020904080d09020405010801090507150f0804030203090603040804030b060406060f0c02010203070606140a0b0406050703 94
    0x120981c02504918008640c44000316020400c0c00201035400001c1d60300a030742c07c104101c4804800781070b0903000c0c012240803030810700041180280c2600095800007207850003500b440c6050000c54100c56400f03c00c5040e54000408005071142d002e0342c03040c3d000d141a52a0030001e071521000c00c0f600e204502404480350070f04030054083d00b40b40382920000d07041c0501a141c0340070303030142d00034140281030ba00c0700009a001e0140745920361007407050a050b41d400502e110301c55111940e802d040c5a10649a005285032100c07035130b82c0541c2e2540300d55802407284600110300b8100f14588641055610b8000c0410248140041c800d070035800a842c0d2840e1130181815280360f01c032402c0503461406114442075100d0000010032080111200181c0100c03441100003004a80380c00c000c0005aa042e4004c440018582e982e0380540305200d0a0011003080c01030050300c3c982103082d03c9400580b00c0c140c20850030500320440c0c3c90007608004907804003c02e0003803074003800e01c2d00300340000341076100d42440901048898 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 57135641 1250 57134391 57134411
    0x1203051618080604030201020408121c270501020c010e012a0c052b0203071203050618040b180d020c060918130302010c050f0d230403050702270a 64
    0x1041071005031002408a5100c0e2800386030080c003075401030146075a036018140200040c0b103421026103000c2000c681a2401415101e0804070050030101000e51202014540000203041c54401a1100704c0c0a007002596418500c64203a0a503142c1442c114002e82c54249080340e000644030070b40144000350803101c1e280c0c00100804858001092002526500074060349940c9541d1200110f0b1694402400e0310032040500c8000781e03128001c081380506040e0000311008413141c403d501090b40400d004112a14150344544417480200f021a01100c0d5031b1a11010303c201c203140500300d0448000303010005c11a1001401303009484403950100d080c095a40031500507469920107100d8801c080701406140000e160500951002035030740300066000d940b03407104404041d1320440488030f102649107201443c1c480240b0405c00148489880004e50400a081801d68030009410440c042c602998a103a1a1030b80343c0100005411910641d03d070300424000c03035503003078030034074a81651203136280100046030322607 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 57136891 1250 57135641 57135677
    0x11120d0c020603060105120a1514100f0207080118150506030a03030b0301090206070303140604020c0d080c040305010603030215010503070e010b0309160f090e0d0c02101103040303090312030516 85
    0x12801f060000b010305404009004400f0307800f8900007450418144180b0f681c0b4400041461140301d103580d00701d8602e81451040b58003804100741000440d20441c0c0c61250344041560071102845144220050032090407800d2042051032540c0c2100c80c1c1ca010000c0c0d09000d00000e82e910b0a8102c010240b50b1209440c581540c1d00f94821070b22240c02811682d41c0710f200d460024002d2000c1c4100780c8846400c0310100345241032138400c0c2e03006d40c1e6002008044000e80040159100103000b45195095a0100008070000d202805017600942c0720760000d2000100b414804250010140c02a90003a84500802c10600000760b424a0448542010407a929250301c00340354180ba1204070500d07500107078034200159569040d0700c400c044a40301d010070402c6074098881d094032203d01c8040b900014108485c8140546452861001e040115040a0411441d46006c1c00e055130003507070082d4007240d11a070040040c8585000340a40078602c1d80350030440781c0b40aa0346070381840741d50804a010880108094074a4408d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 57138141 1250 57136891 57136897
    0x501081306050c09121204050118080d18090207050303010504020d0f0507050c0115080d1803171b03030403140319050c130807060f031e0911120d0c020603060105 71
    0x7810a006201c10314003401d0b180c08503400040d159009408044104001d040d01043c003444c1001603802e0b552a15240400445181c1c41c6140345c94107081c034510000030042c4c1d0401005442420940300c0f003038070025100d4801810005517000b18441c90040120b00c000480220440303042d200e08070b800503100d00215640500a043c0300140c04085407612040c4072507035030800080c081001e084402813000c01c3c85401d002c016a0308a214407205948070700149000c5901501014444814052a6000ea00d070340351200036201413111702c48006968001a800030004003211800c850074030303441c011440d5040603600100720290102851006e828080081000c0c0c2181180444030754180074006d004038106004d20840741c0e4016401c038140503458801c0051f10302c00c04141324080780c019071580060600882d0701680a0039200b56003048440c02000c0e003203045002c07881641d0845024050048501e10044207111210313800d00e03201d159039480800341128003035000501554043c0d064507015200d881c1c10b40143c40f680 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 57139391 1250 57138141 57138143
    0x90f0415180b0103050d0302090d0809060903060406090512041401030902030f011a0901150504060804062309060106091a0708040f3f030c0c03021f0915050405010813 73
    0x110320740800c0300a014118980c103044e00c1c054401d4581004001400f64200d104004901f07400c180c2d507070780400100300a0406401d03414030140400c1d107400319040c006070510800321403c440707065a61310340605010040020104100d504c0c82a24a01800c00c500c0030b00c0131074400012410140ca41004004544084c094400081404002880000000c0122002c59064103c0090096220900002d109503002c440b1080081c103d0721040e00d0a030030700c8011142c3c142d008101782d5146444000c9080601da16000a09204a541881181f1802c0600200b801c012060b4081010818800400c3c001c00c4004200401da0034501190540e4031409480c0401c001e0082c2d90040044190415002509804510008002480b204205001e00035104110041c0c0ba540ba140100c01500810b62400041d01500420000e54000d04a44501c545c7c1c0303034002a4110701c048500091008221520b006558003d08a0006070078424130441b05d010000d8030040c0340740151b100f02410485004081007801941c54141410700e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 57140641 1250 57139391 57139421
    0x70504020c1b03010204050904120c0209040f030f0309110f01110d23030103050318040b03011e0e010e060c0703090b0403030306030b1501120c090b03160e090f0415 72
    0x81d907000480c0584401c1641d400e414100d0b866056214185010303c02c413800c5d50070041c140c002030f40304d030b4480c4900c48403402403000502c1003518000000d80d503040f02c07107441540700711002901c3c144a8a00100745a002d08400000e040c101079881001410240c00b603040703c0015281410140c1440c4c0049501800000b190030042c061068084039460b4840d030030b441881d42401c80540034040e18040302c4885c0c0300074403000e01135070014000300003840c0f00d52080b40520400240007103003540b50180028210707550b00b00303081c001d42c0b0401d104132041000b5001c0e002d81200705a00803c01c0c680d4140801e6102c0c40d0040030b501903200001080780400d0700a106500150100604090b02c6035100d00d0050000c0603039020036281c0c2003917000014010001d45d0b64100c1c9030081039440c00e1700c1d02c4641c0e000d04040c0c180d0280541c10711508000c003140d08420035010f0b43c840d1038421030240c02410019409070000f00d5000000340581540000c0081d0750955060050300154012040c0b0a592001c51220300181001d007054109 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 57141891 1250 57140641 57140647
    0x50903070f0c030308010b130603020a0314090d2012090402070c0f1d01080a020f040204050d08040e070302030412180314010f111305090a0b1203030108010c020d2007050402 76
    0xe01812100000c00e83c0e100f6180c1da105a620359400c62030b640a030591680550b480c60100388606c6200360050b0123106403d040224903501000308000900104490204555000200d0320701c003030382d1080c0d15043c044007059402407004241002c10361a015402401c1d2101e8500044483d480e4841e9411600d04d207402c490400c034116200e1402543c42c01680c452016071040408048140c00c0a6500640c1242d88000080c61250455400d00071110781e43c2500c103900130380c24040042e080c2c8550f40d038480c1c010b105802441d0b0380c03400e207005000d0394100905a8000c01d0310501c2000005403e1103c01c101402150801c9020481440c105442d0b40c42c0c59007004180c0b11003014034050307605054100d204150700d031800501007064031092101050040e40315a880c0842e003803100304014188143c00d00e8000303072482c2021601d843c4150102d510060341210342282c544c00000100108074083c07150001c012803d01c09051800c640380c0e8000d104810340407942e403500420a12131800c4140801c0030700c004110250055407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 57143141 1250 57141891 57141893
    0xd080a08010305061e040b090703060612031b0519050102041211030105070f0905060705031303050a020909070b072012010209180907060f02030705010f02030106030b010c0213050903070f 82
    0x31150800b8842110300e03100700c0011070700300015141e4058424402c0e101401440e9110b8903500c0c414000038060021314001d105010000c1202d50050b4806086c16566261200c5040d107070061003986480040c4c0c281c42110380183c1c00141020030352000121284a50304d9119000e402d26034028811580f1408058008100600c1000000560f014002c4800c40080150b42d1350f0700d41c00c1d2040044152210001610039605110504c3e00390041c10801e4042d0342102d040c549040461001424030350030030b0b140d076486135440f2811860420300d815489201c2c0300140c10254500900401c142c01795640c000c000703030000400b050381e9014040c04522122401404020341c0420035a015000f58010a0072b64000c850190025000b540f004900f0360264003101d0007032004078a4141c084607401c000c20080f9045000c100405030114031700f4055602d4072403984d0b10069580d450440f0160888108101c054184120408131401607583c10a0300740e920300d4a81c40110b25a0f07a20510a4154403481100034848101250040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 57144391 1250 57143141 57143147
    0x30a0c1e020a06060b0712050f120405030705013801120f05010504050705040614090d080d0606090e0c0a180513020301091406060403060b0616060c030c0315060804020d080a 76
    0x1c070b007150140c94104103207520385490b00c44502c22007901038180e4425024912145124400903c03004000009440c101110740d120f40c40001e001380c0301a5455071000c510001404400e200340000802c01c1350101b0758400d40e2480f041180d48151502c08070280ea034848003082c59029202c02481c1000d01001001a8a448a03514000703217400c0c040c9a020340d10345000030341494000c3d0300702c9040d10804c3d21000ac520600715000005580032049850708460340c442040c0010303140c103025280810f801c160101d02c0700d040003402000d1414980c04245c9080b01c020034484c048008800301c400c4140c1c2c81c502042c10701d03007030400551b080c06503500181d04151204e08451201001c0d134055810303550f0303144003449a6140c1c4c0425081c3e0550583c1c02c3d941c4407508000402c0010b29960145502c3d260203081c49051000e03001c82c444001d040c3c0ca400703890903600c81c40c0d005001a4580304840707114506050410901201001c0068040000d000c0c9000b445868000b1400350b58441956a031900d43c01140140d039600701007001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 57145641 1250 57144391 57144403
    0xf04050613020a03171b01050c09090a110403080c0607020106060503072706020c09060d03052209090c030b070809030406051305040606050a09061407080d0b030604140c01020111030a0c1e02 83
    0x300041e10715504d035514401040c0908c50140e044003240a0501c0c0b403000412194080c06001c503820301d0f84d034104042401d00c941019100850146003015205d03242c0c12035a6082a4004001400b1a4036080e0103020a54100058030b030030990301c0c40c0c00060303010340c80075499241003050300a103a05024010001442e503400915010304490590782526580c40300b0301446000341840d2f1005000c500e0601c45038004130300000203110409000603840c5046951448110300715071010f10b00760344020f5608028824040401011a0002d030703d46002c400f44d161810030180c590189009600410400107000c1156080810320103010b8000100100440b80c2d68960140c0b00b5030140c00c1d5180072440655001821034001d01e103c0c008401d050a41e2440d000090f6107010641e400030100704255a500c10384e8547e6a1810045644144d10032803400d0181c0c020800054507121500612038110380c106040c0100788d001c05020740b5000440c024000c9001210204103a542e0180c3c9040108008114440024030640c00154 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 57146891 1250 57145641 57145657
    0xa051608010f110d020f07241116020103050711070e010e010b0421080409050a150b0702010e040b01020a1703060f0a030803040201080411030a030203030402090f04050613020a0317 79
    0x8011031001d5201041c103443c070040000b65403d0381404268402c0307460307400600221030346108180c038014041c1d4520071301041c0400074030242142a940040603821900c900000381c245030943d01e040504d0340c0000d000f1b0b442c0060000341055140c40c0890072840c09180490311481442040d2541d082d1607040f090701041d800d00c00d40031865407980000410b1503142c0111015900900070011011203111420740303e03480140c1080790707424410400060207103441d100f120f0040c1805240480c0c0390321506003072144c250385500001c01e000420490000141c0c1c20450000440100707880114540c0b6003800103038102003000308080d01040c031040c020010032410b01c0045100d1541181e4000340c401601050043c101c1c1940002007224408101140c0990b004e560b03540d5220303208210280c985580315004c2410080d500c101140980e0000c001e0204502d41203070940c0d88544288118a11842d054440341c0d42d40001400200b40d542034665001d06540720820034030701440d0808041c0940c400c04001c0c0e03006960011b20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 57148141 1250 57146891 57146893
    0xc06151f0512060103050103050303010e07091208090109050a060e120f010c050415050304020d140c040f021201090b030c010c060209061303151401140402091201150b030c03070804050a051608 84
    0x10010f405503000344109810380350003100450960f030800707800140707054002d0306403018401401d200041a500c49a8140a214420341d6072a803101041c200250001000e03402451080c0c502d101c0030300c010b590064120003030044c1140c082c4800200820785904201c2c40f18200c803030b25401c4c401d41c2402180c211005004950b1840c0d00c0c0c90003800c110408a903140400c1d44c00a50101290b4020000302d08000c000900740c40b0a6070542c0d00c840f80d0100007404407031800c800c0200f8942c0100c1d01a0004460503003c078010035401e0010f0059001c4040041e0b142c01d09458450305112500040340c0500c00c0640c140c94849034041c0503242c0d2407502d2800000380c2c0c1d2051104a4102c026418000c80c1c81c02c40b030003034402001680024401d240d0800c0198180007030380d02881c680080d8240308002e203e03a1a0a210f4800c1700806000269500a280e005603416026400c0718400240030004d204464070740b6800c5a601001c94035184c5241d840e00d190407030a111075641c000d4511300c034010180c800042070400d02011544940 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 57149391 1250 57148141 57148177
    0xb0105100201050103050d0e011b05010615020106050604030308090a06020304050a060515030604020103110c16080f0d090306020706111b100605030601030807020102011d0c01030f020c06151f05 85
    0x40220b09850003400300a00701e8210044040f11180a5925100a000d05040c0030300c12541c211140900711107003007401d46145e910345404104014001d0500b0b5107103501840240061800c00000c142244602c1c4002000c00804400143c030703400003441070380500769024100390f41d00e081c9410015030760301c001401030341d2191624000c10140040a114440d44000140140c001039840b90015030040c40070003280302c05810100712000880350180304a6009400c20074104095030700f021003040ca85010040400c1c40c170381c03020810860b81604450f002049a034015005a80c5409030319006c0007600124500601d20003004c522060240c40345041c461030006204100c41c1003410409003001520b01301e11445030141c01110040c0041441500100160360041c00003051180013038103003840d9190007203510221a00002011065580d2601900200c1d8500c10400d50516801101c01d80e155000a060340c40c8007180e180b1104040e445007480c1c41c1040103001e0200d1050101d60f88040c107280d11804260302990414 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 57150641 1250 57149391 57149419
    0xf01060501030627060801020a030e0c0a06090e130804080d02101e05090109050a03180e010612020714160504181707030507020a0f051314061003180b0105 68
    0x9204030000c503081e101000b113074608a41011010a500c40b0160f0030007580f1244041039a0000340002c0182c2d843c10341d000601d030703898424990306240031450628800c4029080170410964080c0342c041c2610402c04000500c1d460300c407c00800100511002098040003160000d201100805c3c80c0001c1449a002c0d274224221000101c01151407011915040c00e42c0d54256041140c01c0741e0103182e200d0034010000460f50059150301c4d02d00340081e10b04400041030089584044144214868010440403d0385c20f000e505003040501030240110484a049a021079407100703100400c52007504036031910301a6110700645541400154001e402154001ca04000824101c450f40c950300381151174007d07100c22658103030b81850841c0c1c0d030b120785c1066040042c02e004500250b51900c02c0d400007408024030001d220342c508418401c403500c00340d109007034040c0b034101d8441d40102a018100e501803021105914010035030f140c2500104502e0760103081003a00c5032400010001070010080c1680c4c42150040141418 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 57151891 1250 57150641 57150647
    0x1b010b0a0e0906070207032301060e13020109060c1a070c02180105010201110f032a04060903021512070f0903080c01050601030e0d02071823182404080910020f01060501 74
    0x1d00d100041000d4220403004c1401011062410081c880082c00030ac0c4003941c40c81140940704054400314600c071103e0704d16404540e00246184020000344c1443c145c03014040c3c0f00c200d6644013825211022000c032a0018204600c40e4458000e110343c0180180d80c900c008201c0740c00c4486090084501561034803107a12a03011140d001d882c100d0b10b211864500d90382c0c2c3c2441d00a1401070501900c4030010b80031010b0245006810043e00107800f95640d56400949180100303d0f0100d42001c03040c1e000402001301c9820099080300156010301242066914801603040440780702c0440d920181c070040c00400c04030701044040d00003501a0000742e900b44085140070741c03115100c0c10811915005030b841400c04008040205032844040c00300901d0028080500583c1d921080d900c03814100703c042104c808005580a810940d05002005003000b41101c007003251559008942409120817103584800000f401c02100e2000c4890812010b0042d0303000c450880c0010317545011082488050f9424501c002c241944 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 57153141 1250 57151891 57151903
    0xb060a020703141f020f0c0304080f010b01110c0f1201060303090311060a020d031e020406020307200a0501051c090b09060f060918070b03070e0901050909031b010b0a0e09060702 78
    0x1c1c00d01d0540002d04c44005243d00960080c1101111303844140844251200148040d000400e8444050420740015503801403c5800014186040c081085c41e102100580041c2c00010088195030322070b54441e0352000203050034611020007803550f0030840d011040540c0302c40200d0880f485124040e111004010402560380902001d40005a0002d000b291290b40329030860941010405162040300d40d69088000603a4065042400075030300004603081007042c2c8240311401c3e2920384071500510003d03a00080c03e0b13814079210742410080c000c04e0344d4020501ea18251f100c80d98041804111025183c50205007031207040300c04100c50b0043d8400120103d501207c00ca118140c000c246000a031b448980103003209490901a0006105504011aa60b0b41480c0110701034116912940000c1d100107081004443d0160402e6003e080310409014500b107001056034280c4a84503a0030072208d921940c07142c01800c40010b030a510902007031000030f10b1a1044d03422400750050034243c941c56a81c001c0c0503aa030701 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 57154391 1250 57153141 57153163
    0xf0a02030a1e02100e120111041a0c01050103120f0206010608070f0302130602070504110c030a03020306030f0d0509040c02061608070e0a2417040f060b060a02070314 73
    0x18000307210000000d4164040420b20001c51010440d24a5454001c60381c0380d030503103030014041503400c001d01041e8501500c1c400080100303480203000f0342840f03601e5412980105d02c504492503200c00036440107408410309540e048401c000080000390782d00d003419568802020b0007400402d110031100e002081c8041590344c16200d8540341e4030321036103440c02d045502e01c3d00d04001c030301059400c0c084003c00e07403141c81c00320004140341d9008062160821040104441502c514108000001c00140e055000c5c0442902c0260001d403c006840755902c0300800d080040c001c100c4801e41c0195014800710780e0700407015009a640c152002c02c000c1d403c2000681e9640015201118014545010702690b01e120310b107090317840207036403800c078030403e090700c010403241822034002003800703a028612000c550104000085101115207844907100c50055200e0104d10742c00341003d4100740c4180c0c009014000307290045560703620080c180507503c218104d0000d4850080303010403100700e00b002880c99003440700010503282c48 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 57155641 1250 57154391 57154393
    0x510050108090a08030c07051005010519080c0d0203071502010903090e061804020a1707030203010c030605101404050603010e180d0210022101030b0a05060105070c06030207020409021306080f0a0203 87
    0xf44500b43c4070400d50b070300020242e1210190811100001401c00c3c424080152400318010641394102001c1180304101c1c1c07042c80c082080c182d4010031004100041c80c4600e02d4055450304034246c1ca600200703081101a0300007008461141c5035034804154154429400f55010740d40b0142c0454840b0041200a202a91a03035030001d018800c0b5100052180d680390f40142c4001e00d440d000319030f104011200d01c801c10442e025580c00c4940c040007503080a01171101602d080d89010031445041c10000344020500342050000c001050411101c00340e5000c003200d0107007200402d45074407907035550505002d8900498680700e45201001d13001d1000ca0000030041034404480d006018190101c030240002500407400035206542041c2e0041c0f4503c43e0050064003840c0201c0e0540d189280c0702500c4e6040d2031018140604202e410005c0c0d101140312043c2020a90740c0c00d140140c3d443c1c440e40005405820a260041d500010b40400c4910800140c1e10210840700102d05039889003e050421a0312046c840c240a901 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 57156891 1250 57155641 57155653
    0x105070f081023131d0c0607030903030f03090516030510060602280605160f080709060521010f150512040206090d05030d05060906030a0507030b060f0d06051005010809 74
    0x19410103107511550070903018110020544481ea004401d840146680307012203414032151703100070f01d424031115450786c01c240d0310540740c5070046e980140310440c5440003404010107080f0400e1040d120b904101035603074114088480d03028070b00301d10b29000001c5e0310040340c003032040c000c141138031041c107000313160031601950007a04680d022440c1c0361380e194805440000341c8107940d8803810001802482054065250016262100481070384c1c050107040302400c581d000d20180004000c2c0b076503408800300c0140d80c801c2c035016480e0310040c800404076000341c41c81da40f601c4144000100d80623a000c420107040b01c40c420761460007840091026503c40c400c020f55000d02c000d2460006001d400c0020091080500291014a8a00c9681c44960840e00300c403800250194454060124510f01055880d030020011005448078113415611130742c1d01c0d0540d02c401051006801c00190050b82c800c2041090000090003070b040d82001440d02030700600040352018150040b01e800400c00754810b011052180410a0041032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 57158141 1250 57156891 57156929
    0x906030c081603020903030f0a0809060103080d091a04120f1b08070c08030310080105011703070308280609060b0309030a0c02040605040204031505011505040e180105070f0810 77
    0x8090180385420b2020315400700005010340d14100010110300025081c6291201408000241010030150640310140e100c40014030128140740101c030030701c029102001503030400c2c0d032070008003234080c0e40c540204ca12094802c010500c80d80034001081c110303060350399640c107100d83d40095403241007210b9049000c8a843c1d24190019035500010810113009040400c0d82d0f0f43d540c00b041c2e1943d442100c181c200c1c40100c05041002034800d01500c0c0c0500300d40c0318000c1c84004084c0d1101d98a01403024058208422000480c0101501840803c00828487c40106d440b89500c51044007030a0188900c1a0a80c500880054001d80f0030094a002c0c040c42c1c0c0145140c02c0390401c041300e00300e001c0c00c02680c2c0107a03100d03400185680c6610080009510400d01c014000c5102010320044400c140c1c01102c0d03514054200c601c1e40c17981311085a003520000c206030902ca4460005014000e407001c24440825031070070f020710001640004040380030624580d1020082d5a511222050800e090300c9000700400503040241 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 57159391 1250 57158141 57158161
    0x2090f0316061808031308120f030601050d0902060408010c0801090b0a03030f03060b19120b010e0d060f0e0a020a0b04030312021b0d0503090d0309050a06021b0102040906060906030c08 81
    0x1c90f030800303040c983c51440c40d00d034415941541d115840400e0b0090240808111007081400505c1e1704440382000b250600b071070140310307058910004081604000d40050160a8060164021189641c0260817540c6407603d5907403d074005d061160218000c1500c2400000d40c1044500403d80c0d0311401800404160703242d07030b40a4401d0030403c07040405141d150000401c80044440190000d80840201e48480c0d030300009003d015031200404441c06903003041059201a40c10030403060b901541030791181c40310115400d02d000102080340d840c01020b4180050700c0340500c0001013001c0d100b802140c0390b403500c139a194540c50380e620940c40014040380c05c000462040711040e82c0a01034900d4219111004890b8000d002c60602040c4103005002c50404418484107000c104420b0401c04560300301040240250f885039569040349803002800c440d0000f17071490a11007802c0d480383c03d000001c4029900c49403994000300151030103000e11780005075041c03400900140310740a00e1250035002d03150702d600b1b074813031031a44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 57160641 1250 57159391 57159407
    0x50a0204020c0304080f0309180f01031212050a0f0b06030f0c0702010c2102010c0f12050402190902040806070815040b0f0a06051b0703031d0d140102090f031606 71
    0xb00703424003003400000b80201061055003035001511003d9951449440208840b112a000c15184848801010440300035111012503041d02d070040000c507420f81c0710749800c0fa8950f142501800c0a28100004d00c06403d2003600300c9214070301846400c1c406481030501340595800304540400800c1034800200c0c140340c8544005240311401823502d00801c0d44280c0f1400c18108c001603244910003504030b52424a00e03420f108680364010540380c10003103d045000000c10300d0301308150700340726607640b0000329085540320711400441244500350140340640d51100e0310000e4009224515041c00b0b403000259040e881065424412481000700c480084800d01c10303c00140314024009800519620340080213a84600710752000300442d64a00e41d462a031000040883e180754802c0c1e000b65482550103100203074201d020900381401c2c000c0361400480000340000d06500603200c0162000720441d5171820b0500040d001051030b01019291040d800855400b8159501d1004062001403200440c051241300e20610f20 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 57161891 1250 57160641 57160657
    0x806040c0b07020d0b0a06030c0305061005010305131b090c020304140301060308160204060b16060605090f010b031005040c110c0f03030d0e030c070e060916020c0108040f0506071d030703050a020402 87
    0xa03492341369036412484541e95003055509134410302c2000300c05e041310f019003400b401c42860188001e040119484450f031b109001d0061094446165992203110b554907403400600042905000703005140c82d010351242d103e40a801a813141504000c4443d06050041104032a03100e01e40f00d01e00700b901c2e2520303800c00d130030650226030141d1250380c001808180240545405a40101d2442c0ca0310080d113013460442e89a03520590056140350104851211000d45107030441d0114010640d41b540d8014507006c1d051305541225a02030700c2c20380c56600c03155000140740ca0100101d000c4031041580c030720070088110500b5200b01d038554001c00102c00841c82c2904600001c01a040031030341400701030441d0a00b04500c41d0000010380c8039034010030000345090407405070096402c1a515441081c6918000d40360208400e002d4140401070340071504102c005090701c400c1c4c6400c078007030362494102003100426542c85100c10101140d5074400e040c0052402007880411607521000a003e1b1020703d80c00d10001c0d400c0152 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 57163141 1250 57161891 57161911
    0x3030402040209120703060b0a060207080322030b0f0a05062e030b04050114150a0815011e021515131d0706051c020702030d12020c070806040c0b07020d0b 68
    0x1080d101d444c0010003800340a0b502c12000402d0011400d41071240074003169111004640c412107080010482c040210360741c1600406900c0b40621080c0040c01d02c407807041c4c2c002003002c48007008100c0d825840e102d44c507004041c403503014802500c43e00200a5890706100c2070300180030b07008062400045036900309403840c50382c42c200810300c0402500040c00301c9000342e2050410340300880740c03041e43e49021f20300700342c801c03003c804043c2c10201e40d00401004040020004051101c04144020060307009100090003292030081c1042d513285003210003034540c65170481c071501c0112507101003404503c0200030380f0368a542c0901b00554000203020000094501904079410010404505688013a024007202025140c207442d000e50f5118a520400b04176030010a403003c041b417041c8841d0b0010b0f600803922206414451900403014102030720400c0080c4541016984d00e4418514001622400485c42c20b205a004030702010180303a441000c1d80c40c900c1901e00080d40081403d4400001540813089103410418541c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 57164391 1250 57163141 57163159
    0x1e07020c150c070e190c02031204030e030706020c01020a06050a0908040e09160e040206070215130e010b03040b0112080d0c080105040b041a0111030d150501090602010209010203030402040209 84
    0x900851448071201071840e038000d07000503440b282080200141ca00a003d1440703602402e150182a28102d00b040041c29030301780b501d03000074a915034400c01c10b5900d403c08008000b0041e041514000c0c0ca00d06698002e42d00900038504001203090000c00d86401450341038010740351458841d66180c004200050400d0882650348502402181600c000381000d4088071152052904041c1020b42c43c00340700140c104040c1c2010001481210040b490894000e98141c8a1503101c0c0700504c000345180c1c50300c6601c0380c0758110201782411800141c0031400d003140c0d03000342095502d07600c1d01c1485640c0d200850300034040804000040058482d6014082040c82c020040141480113881c403d000391100424814000b482820040c4440d16081c890040b9010088070100019080301144007040a450b050581c1170001408111240c801c090044610480340316000700325582c00e212030800c520020b402030600003862100003186c0140140708454400c00140c00070b604507901d0b0340c20000070350300482d9910f800c280c1d02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 57165641 1250 57164391 57164413
    0x11030f0c13060312020703031d0105160501090b040b01090b0102010e030405010f02070e07120e010b0a0620030c1b0603130b0c040305010203090f160506030112050313060305090c091e0702 82
    0x440d0130340e454044c0d540d001c1c10000e4a50304009103180c00b42d00c2c00f40255500804c2e50f11080c0c2c0c0000c02c41d1100c040c401a1101c280d0714906207240108807104002e0071000e207081c10003042004000e4014140c03030540c1d0041107040001740049080b141170460000d841c0c0d004000c00d1286601511505a11000500c116416a40c40e0220000342040585020022034080c201e0380b0010003441c01540c9030304100c07600801a100f080c1001030b4140e10a48250f00a00602c7d258a1a06c6a150904003d40300c41d040101c4c5d58450303140c0c9004e50356507812001c0c82241020500044c20f0ba1030120100c0340a040c025030040c250107400d4440d05013840001e008254182420400000056401e0000d10720800d840d00103001841c03058802c00341806810711080f6a581407140050041d42d4401c0c040e6030540f2010360b00342540c101d1303520b841ca145105002c40000d98149017a000203609a142c1c00851103044048241e42c0c030400c504080c0404004195040380c2813506003005200034070301c0a84d8403540050244100c0d00e9442134 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 57166891 1250 57165641 57165653
    0x40b0304020909030f0f0a1d010f08060102010612030203070c0504090b010b0c0a060906090b1008030412061103100f090c1d01020c040c0512090c0a05060a03060515040311030f0c130603 81
    0x72020309030301482808115240041d230000104031808200309640082c00640c4c0c4002400130300c08100401c117106121001c580564402d50010026214a422400c903403182401d0183d9641c016207421581d03145d0000700410301d41001e000f000c5d0210341c4882132084507400d010a009603604540c5100c0301b01c1c822503015101040b542d009095041d0302801c800646001c40b401c200d40742280007442c407221860301c204104601c1c90004200c80444610012809c07412181c1c2c83c10501500302c08a0300041c140000c4181304560030100014011502d03698070f00341909980b02410016a0070642c2c10f00081014800d00c0340309030810b841410500b0b035051064401d031103e5440000c00312202036031044001000400c60029801440d03140c103410181590051540e401084000341c84080e50b8014180508000300c3c500031030318043d402c00c0c005850b0040440040c1180a4034010b175a800c5480250f410300d03000030100d6210300780070501301e00ba1009003014018400f1b90900340401c021811a08010007541d4440c00008110 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 57168141 1250 57166891 57166897
    0xa1208070f1202011d1b0d02060a090806010801090c090b010e030604061a010503040c0b0702030f030a120b0607020d0809060d0e0309030c1801091d06040f0201020607020102040b0304020909030f 85
    0x2110300080d06031100d581c0002400c580800c00088410210b8a0082001070b4000461b00714002c0c00c000c207034941d0450800801c810700e00c8400029081a000714104990303c1e0080b00c014141c0700c14400b2240d081e83c0c2c07075039024241c43c404940134200f030f402c01100f03112003501500b0003940b100060400e0342d000c24010000c40d00e000b200f180d080d1100d0303a071144070056540c142829525072003800d00c2c0543c1035003010384510043c0344403403040c85040c0e84001003180440d10244000083d1460140941380c88210b403600107000003900d900310b031400c20b1400c1408130607407400030141d0b209550050007104003110982d48030b10242d8005090039034420700901000e001ea842c280038800c0e94001d004041c1d6101c0d200c003800c1c5860180d400310480d1141d501e5103c0c80710210059a00c4130b044a03e0360802060b106d18a0201310030722440e04280b080280a0345042100380018480c500a549200381e080ba8025035818504038204e002c3c9004140d0358040c2040450301501d001307020103400c0060101620700c2e04030500e8480f88564 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 57169391 1250 57168141 57168143
    0x12030417071a04060605120c0d0302010e0307031e0804030509011d03031c0f02040b07030c020d020405090f160501020709090515180f06010e0a0203040f0210110106050f0a1208070f 79
    0xc501c007820070003000118005c000003004207440034204119807100b110349900c81c0348141c0c2d000b0718001c000d50060520075084040c1d540292015640e45140f503080007801c81440c0a501224440200000403849200300b81180c0304a4056a881d401e21a1983c01100da05108101c80d0ac10000c2d204160f00107a58140000c00d03540451841d0f400c803041848081c0700075109400c0c1c4d0621079620500c03040000110810403104820380c94900200210703128400913007110a00c03800650050301d050101304541c09c0001c0ea107000c101400c2e04813009010202c42400c19601c036400303031a0040e04040c10800895066400c1625081e11034000d07509248044070045c400d1701021108011410700000012040c030805000752190082203002030482903040040100300190b02410000c6425400400a418046040380c40b140341503006044981c010f40d907000003014171180184900042d4030303100b00000c80f0301d0034043c403c0c03800001512038103015140400443c140c155014040d18a00c0c130401801d800600460343c02d9841c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 57170641 1250 57169391 57169433
    0x3020f06072001060b07080d060b0f090306090106083313150c0e090a0207062405010c0f0206070515010b0a0305010608040209010b03070e03010f0c030e1203041707 72
    0x180b50348034801c9040345004503160a869140500c00d02a03041203000f00e807400c9400c140c00e9581c42c40740c0c0c500100100000c0e072110310b076100301103282401c1103011801003400d04011403c407005900c1e020350060032120b03180701d0f200350799000c00702326090741c8010824414005040c05000c0081003002008034425681180d405501104d407000038001c002035486120a1001101c1d410041a00d440d000903100c070715500c0c03865119400141c0010840341c1250103c8d00c201398840d10500c84d43c46042440342c261504070318642c9182950300008030700d0303522030004601000c1d003107481030458441940a01c07409034001801070703031036000b0008643c4c25810407803105402003180e50040380d130324240c8010080403580180c0100d03041298010500c00540d444c514400d05540c15070088603901d8851792401e4030340504542e60107804d5424059100c042c034116520107008003031103032814003800000201c0c1d96103400d02d9181e2501c4000b403c3c07012902203100c81c284040d000d440d1403101c5140035081d0711415a03815207042e89000e2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 57171891 1250 57170641 57170657
    0x140706020706081006030b0a03020612060a1502150408090907050d05100602030d1e140109060501051213020d0c0902030406110301060c0212010908070f0303110f040504050403020f0607 81
    0x606903040007007070020425880d103010b141c20095501500d00c8024420390007010f8031002d038614a9503a500b1008000d40d4020500c2d6902d00071803800086114048601900c40d200d0340c00700056040f402152448216140d90150a90100c41c184004c6002c40140c410307140088180040b0390a625900030040c0280c0e0584ca030180c840b41c200030b0003030a4420040948a4141c92040c0800c003280d0004240c54100d0f11054011400041004203056a0aa003054103005d0908240418600070060f03e0511f042e1404040c05010094450005450074800c55060301c0e40e10030040001034003400d012a1100c03003184010100360340e9640c191202c0d0060301454000c18052a0b0000c1030100f04211032090300500500035004c141550724101c0042c080e035082c00400303805401140c00264041c0b00039408000782c154054180d41c0c41c3c1c881c90901401580c7c80e0403040340031a10382000c103030440c011002a030300781c0011101c5081c50182410148806440003074400c405501c200803d450039000140310b060b200300402e98400302 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 57173141 1250 57171891 57171899
    0xc05040e1b0102010c0905060a0c0b360d050c010e0a0b0a0e0606010203090402070318260106050a12020102011e0c031406030a03081015020309130e0c09131407 70
    0x1e4207040810707802e041da854100d02101ea50742088195003210340446404d0740391000e1840503101c0440340c0301e0061495605008002c1540505604590910260009540d40c030400902c011010b11120150182c180d0250318075054551140006012855540c400440c0d110b1840004510345801034104950115500c8200b0144002a105001d90268a04018062401c01400107501c82c4247c0080794003036500020244281401403070a0903031a0002d00440c3d07040365454841c291400c60b42c0c242030b4500443e05d000d01411080500840056900c02080a0000d901d08601c48180410200049041d95260141c2d400d280440e40101d40c0031217001e44000c580172104107001021107003503c3e0309141d0100c281041c4041c1d0307280001e6a001650b0b040c2844010340e11004802c00c44030945074044070703030014114200c01006d58040040c0250000c19070f020282103001c4614001924510310103140581d000581c020b0161511250158104c1c1c000110784110300e07800d807102c159405483c1115241d96210b42c001b04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 57174391 1250 57173141 57173173
    0x9020304171206010302090609030a0807050f031c0902040f0c08220308040803101a071b03020607030807030b0a0e06090f070503040f080d0507080901060801020408070b070c05040e 79
    0x10741c6060720116401c0c90b2260010b41008400800750429040641c0030824420720345526080300c0780c2d290010200d580c09030ac07503e0080c11a0703000b103104540324002c121070343e10a108000305980003400c41010160900c0b424038a00303001018903030700c10b0f680582c07501025107079200140f048602007000ca80d41d0300060318000c141081007000801c41202c501c00381180a00109502100e9141c02c03030b610000030355803074071050fa40040403803180d0005144200442590408010008010b10010340f04980c0041e95072403861100340c881c840c0d480040e4002001300501c00006e4461b00300a54850054107000600503520008604006802d810030300104280d042070042a2420748110340d403141d103400e141c5029281401e0014441d01000d0002007192140300c04800030410140240c0d050f400d0b0300c91041200d0302e40b85034000d090714000d8644600651a16501280442040c001c40d42990f00460040c45894075011003a01c00740d00c41002540d000201003008182d070342e594024509481420301c000c00c00300e003c841c05c01f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 57175641 1250 57174391 57174413
    0x304050604110406091a0a240c020a0305010c0f08060411040b0d24060305010506030c0702060a0c0204090b0103060c110d050c011d0106030209070905100c0201050702030a0302010c0e06180f030703050709020304 92
    0x1022300348100d0110480d501d2030b00d12042d2243e03903240b408440420840c0302060020300b2680005006508000030091180d074020055805104180d45034103098647d90300744401c5401410780c04101a50400c007c3c00102e0010000b40710034581d4460004070f2442c00e0809850fa109038640c1000c4100c0000800c000342070780350182c0340c05014221000c40c40c50a24141035542407107403141c000e000f0280400c3c0402c2d070328014003030701d14940c0d0054021300014445250800c820f0b0b800340030840d4194500308021100314801c2c4002d0348031220700801085c2c00c401c900d405492030741041400a2080d0348416200100284182080d200c94004800218040c0c0c114410801140002000706081140f029030801039035441072001c4100e60070038202030200060301e000494080c840d402c3c0103901481446400705c1050760540c85462800000e0784e840c1c03c036145101c108181841154250003483c0d22042d2076680510f000710542c824003400800f00c0f00720719039a5442d2414441103603c11038280d03501004100501600c1045 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 57176891 1250 57175641 57175649
    0xc0c0606032105030c0306190e1905010806070e09060a030503040f0801060e0c0f160b0907060813020102060f06010903050604050c0a0b042301110102121b0304050604110406091a0a 79
    0x41281107207050503a005c2d50703010042c0303040e100340c100d00b070380d0003a013070007807824501030003e010b2164a185420b406840e008000f0640b8404414540400041c066101048082c050f2101e40d483caa0700300c20b1031341003200c881c401030040c80d0300186100c0d000001a90802c02480106681c0701c0e42e001c01840e05241e43c2c01c5a00382d50003544070a4080003001800000942180c1c002002800e45c1c40e110791680f1805a508420001c2c0107020303a03149024000307089030002d90031044502c1c07039035512002d98032840d400c2c5030507446810090141c1e0080012a03112001010401c3c4c1c0040185014076902e40e803601c40900d0541c0035079042e01d59800070359181c8402c0c00d080d1038007006001c6244820740f03850715052144982c0130340801015040c41015000c0d00c00c503072080054081900780324009548800d80071041d244c003032000350390b8044850329910008001018003c04d81c6c1c0b003143c220001d00150b43d1030741c549058807105805050f600607607480b00802c2c10071540c4a4200b003503110300484150201c80c1070034400c280c001504 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 57178141 1250 57176891 57176897
    0x60506040b01050d1a0402180f010306120206070528120c0f031209060c17060d0b070f1e030902010e01032a0c020a0e06090a02030603070302040c0c06060321 69
    0x1d03012000e640c00104851550071103980000e810200820b001c03d4000281a0351a809400000c0c5844c1c00186034403ea201520100c4e0a0150704101400540c00c030b8a0394401c50100400700b211346005460000090804140a40d00741d4110714400001c44d4009444203103060f5882c0c03e80d10302c0d00c0510034400300351200c0b021213003000c112648460702c89901c5101c00c800014200010b0f061803c42050807504070b14080c56104138184075105942402811003001490701e995141c0712070001075060318040b1030741d402094003d044042d070f50b01d42e198111607070031050108a00780807810015103c1034855821340700c42d0400c5903500044405d40e9200050008500c0d1880604050030010740300f20701c0800155154544900e0f4402c00c01c103100c4444103031460084540040c0d4004c04641001440501c1c0d0392103e03101c4c44c1c0458141003903a070b8481c4e00c2c204031300041e00c1c65a01580007020900c014242640b06d458080c2d19030038051a8a05181c0e101e5058420380d800c02c444242d05140c1303514140d0306e24030070540700090600b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 57179391 1250 57178141 57178151
    0x9060e0a090f060e010801060b0304020d050c1206090f060415020a05390321090a02030318010201060510050301150e04050a0905060a0b010c11150307030b030705100e0f0f12010906050604 82
    0x200349c40040d4000038101a100c0c1d008441c03104100315080141034000c00000e01030640ea007402e0480d41e500ca4104952440c0d00e8010440170b82004000494041c3c441e0707070f10500c40100c0040ca0031104c0c2c0290052a403d0041c02401c0190504c030340c8818441c0a401480c100203000d07070024615002c45114502031001c00c0942c0140f050554225070a080f208983e074213510301d00030558446182d10b10348a803020029415000c00540196810207040c20215640760a0f0024086203507150140003011900d1084540082e00c140014499a0301e9034502c82020080340c07801d60091004040014225001584d4105040d9070f2100460f007003110910685900802d410703810050820b4220000e4440c0302c078268010f140c5a0000081c0340c0e10351b5100c58a8409500d02c2140301d0700c030302e4043c00180041a11200c0349101380b0501c0000950f5190518001070384000d555148045e901e203140c00d02524450000d410303540b001c000c40c44a0b005848a0f4882e01001030820004103d0000da804c100e0300322000a014a40228188 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 57180641 1250 57179391 57179399
    0x12050301031a041121010c08010506030c09040605100201050402030c120304030605040204021b1e010603030e062d04140907020a0b07050c07180c030b0109060e0a090f060e01080106 79
    0x40c4007000401c01c1c1508181000341d0300c504d40303030003d4591040110b07030105608144039280c4c40c114800c01c0204c0c0d201c100070014100c0e643c0c0c2c10764090380e00740300341c42d800001040003c0d20a0071440217080c608030040c0c0701240860f00d48000591580580600c040180c0d594010003003036140400c10315034000c00907604000c200781d80c0207096869115501000d0300c4552a0f0f4041411500d4030780c105c40145010601c81e4a05902c000d01241d11040003c2118105c0400001450600d000600c0755004580d4180c407003110500200c020b00034240c0110220154440304550124141c001204c81c0040340c6018440255480c0e00701400a003100c20030f04051070260006070308101c420303a00041c191083e190001124000c035035803a5401c445c644125446401301c0e014000001411522140d222803510322804030034000880a40320440c2242c9900400900096003410108401409251004a8018064078040c480b684038202d80c01511101c0b00d4804455940300000c2148040a4000e030f4007414542d0000c1c00042d180c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 57181891 1250 57180641 57180653
    0x909030318150905150406020405090a1e050403050d06080127080702010c0c0f0303170601021b011b17130b0412030e0d0b0f0601020607020703031b03020102090a03050304031205030103 81
    0xda0300b014880e50302d11101051220401014144642080302c2c00b6052910b840d000019400c45c0c40317400d01072040e020100d0703d0b80c08a400341490b42c00710b0036501640022605020806480301400c03c2d000d104003000051070340c4209010b0540a000d102001140c1408012081091100b1501010814405050540001a800c01d0444070300725024603001506540d03a041c0b12403094001d030310515100501d504000100745d08800d00da00c890403010001c04095071484016a1150300142c5500058801183c00c484550700070000000d400d85503054a60301040d0325519040d881a90f034100c40564100480d401e902c41c81e01042c40009044c9285d19542440c0c43c10034815000910b410000381800700020103142d1549855078640350b580c4d08004400c0c05401c107403044900007042540c1050040c0150000201100d00000311042200d50540e00d5610303001034400c0303a0b880c007010070310110210754081103090310940e550b801c2180a50301880143d6a01d5246140400c1030265208001d01404030a100400200b41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 57183141 1250 57181891 57181913
    0x350601020a0f11010504080708071809050c010311090402070b160c050706030c020307060f0221060105070f0501020c070e0124050a031a0402040f0f05030a0206270a0909030318 77
    0x2030311030100703203c1819220041e00c00b40a99007200720b40d8840d02d00e00082903000000d03101d0881c0e0f040c0b540150640d0116500d0f4040e034885000c090b00310351240008658a5209a01683c1c450401410003414042c4590001d000d03a4800300003564800700a2041c40341002c2d890080c003c6da21070758181848400419a41c094940f21035105020a250369802c00100150091049450069020604014442584e00d808000350040092819040c080000b00860300440041c071034000d0348141c554500b480c1d0320303646501c04110070f0308007103070349540a100f40b01a87c081003290b00c000d0034043d41e403090076605200300c42d0249042e00007070034000d0f05040d00b00d43c201a0408110703401d50015140218216022061081050061784c210303c0d0003a20000340024800001000e600a032140840d90580d40c42c0c2d50810141e441980074406503002604112402c92841e501c0d0340b6540001c032017545103840b51000c00010301c01140c1940803540305911904035070308040d41486030240c428511880001d09003201d840707030300200c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 57184391 1250 57183141 57183143
    0xc090e0c01110c0303030a0509010b010e0307051504030605040302150708010e15040933021c0b0a0806070309060c0f0801060807020f01020f180d0312020703350601020a0f 75
    0x2c41c9211201005001c1030020350030804000c1c040766542e00b0a1512100144021103070000f442d40b0307052a0300c2d00c540c4554020340e6042001030003850340d0741c2400101304c1b440010f80d44105a0b4001008000001041c5001d91480b660080e0050042d02d464000046c1321484020804000c0001440051002004003007890350481d4810721400e0b010220040481d000740342c0030358081e0a4900c560300d40400c1c98a284148034041010f0b40d010901d42c00c0000582e0141d00414501400210007000c81c105075524552100001000081c40c08100d6a51801c0c040d003071400c26103c140c00261280c0c040d00c14014140281c43d0750040a1030715021007a12941c0042941e5818050300003000400703404201018800c1103411042a0514002c564881090240080d16401200880030141150403200b1843c9403c80504d0015901601c603c4282558002007070005d5008040c100c0512816182c0569042101c10201c1000c20b800f5010350040c0503100c1c1e01c2d8044500007058030b8110340c0b2404040340020110303182c140c102 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 57185641 1250 57184391 57184397
    0xb01080c16020103020f0c0703030e0307320d0c030b0c03010617042306180d02030a11160e04150c020a0201030902030a0b190501050d02010e091906120c090e0c01 71
    0x705800d440101e000e03110b0200c146042ca44003041707108120f60049040c6044900c01e4039104075201e501c10a06445041c03070721404800790320031100c455161089403205200d40c0c0384004c0500e081c241c40400580483c0001b0000c1d02c40b49100c50051042224000c0c0c0180c00c42d03c0d10075180c4c1190b14254000b032404031003810010144007070402050401c1944040e98240409544040519080301140f440d03440c03030300b11847d204240104054807504d60340440c2c06000e10350303d54003461400d010420156040203010498010501c41c2030a60700481c074081c03004201500b80c03594194000d040504001482d00218840342d03014a2510700358280c1d05400081d01080e1650a00700032589203103d00019007086010540900103c408008226108600055402201da6002030400140c0d032108180820f40c40d640030001e0124482c0001d2811515000d04010703804440ca94880c94620041851a41a100194070880c0b900b461102124108a403c0c0c0e070702809890180810040d007590448820355601140e0b00c80c41c18 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 57186891 1250 57185641 57185677
    0x6030c050f09041802041802010810050906120a1703040302010c0201271103060a05100e010302030d05030a1d0106090b04051e061203130501030e1501091d07090f0b01080c 75
    0x18010310407400300340d555001402088040b140210707510f5647d02d00c42c03049000940700c400240c414000154514240c98016100c000940e0300c40c0305110140e1120318910805100f09a0f0a0740040c1824188081c1d202d450082251241814038001e805d445003161140250b90411b5040e80044907034861250140c8015624420300e040c207414180580310100c01c245825005400400c201e40c00e05400603030007482c0030740e00ba03161181d6400340314258030310030f01000354903070003040054614074450400b6681100b060700000410a40e030030302c481070100708080e2102d1b80765100e00e4100800e989600c556072003104140e9040c4850700d080d2400110080742d40754064640b01c0f5103400708640d6140c41040c40c043d1000d0f032044070354803061010400b80201d000d105150004c0d046c04151890641e010445081d952025012103405c0e908120114000d0300501500c0c640210f802031102d6003010080001300002d0410260024412942e00684025100881b089505000070304047c4000c0240b0f54040301d007201060340e07103040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 57188141 1250 57186891 57186911
    0x50a030603060501140a0e0103030212071121010c03060509010510020304030203030a08060301050a020a05161b09050417070206180a09091b05010201050c0409051b030c0406030c050f0904 82
    0x8010019500041c020390318000020415203801c804881e190b40c011514100840da48000c0440409000d02000b03005800c02101c035102c503603d080103010501c2c841e210031000c1d10314840200c3e0459051940c0d5003c200d50200700440280000e00c10704000554a15043c0499810000460402030f01071290502440101c200201a40e1082c8196000345038010140c070381e04c030303840e200c0100910001c0d180648a9480d000225001c00401e20841e115601c9540341c030f505100702d4081d07171400c0741907002c4296a0011910b080601c00c44444e09480b002e4040140e00050500741818407458607103c014034151025810014800540d4800c0d0954040921010302690b0b62402240890a9400554400c01c0d5541c1007010940402000b43c84070701c40d5010742c0b0100b070030840e91030f00120f00b0707900c050768401c06038442000103000c801615003000d0b03400042a81c402d001400764000e9050f00754000c6800802d03480011400340701156060250502d074406915040d07007030042c420001ca544c2e124480034184210340e51100d41d8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 57189391 1250 57188141 57188147
    0x3120903100204170705040219080603070b0c0f0601140102120d0e0109290103080316031113030c06090305030a2a08030105011808030304111f03060f05040c0807050a 73
    0x10441e0040100075503d8a55600400c5080d000c41c03006189507000c0c801d0042440d007894401e0ba5904049040078034184141d01100350b0780201d020749800d416004804011807080710342001494914031000042400c03c03241c400c1d20341400d206800c280c0b02181000014051340c0e034002199013642580c202502c2e81c0b4080300d2a460020110089800c10700e50078080c54100b40201c203017030500444d111140014400400e038141140015090000601404040c004528070380d51007070078051654a40c3c01c0003c2d1113001380381c008800e500921500350688580308818800c200c45105024001d04450420421890441d0b0750141c0f240904030200b0b0400400515181c1c20303c001c0c02941c5658000d1104180715028a07080c070340c01d154001d00034917001c618025406856080c0c0c1c1038410084654010103941035480301da0b0b40001020b02e1281039a44000b034098041c44403003c000585aa000183c0c40c0086e0480c0341014400c2c0381d0740207506c41440f50313282c489001136140d000391605902c4240c5103850795848032101019 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 57190641 1250 57189391 57189403
    0x50619020a05010608060402090a0b010f0e01020106030503160210020f0307020d0218070c0303051617070201230604050c070206070201030504080f0a0207090f0e030d1104150e090603060603120903 86
    0x2e80150b003001c2000400041c045070310340c090340c002e8501c40903a503101101501070380d41444090740055041e03540e00c00f4a42c4104074040c2003800510001c1405940e0752181072660304100684000340180c2c41c1d49404600d17141921120b24500c1d40050200011840152030300c1c1e000d2207d010340100001208201150354100c0e40c0040e01c451641c030b0326400d0904040080c44442c20450072004686442d021800c583d40d4001c098105410b241d031001160892141016030000c409041c010556403210a4041208100f51564481d40c0c50000c0100aa00e0910100003d980d40582205800b02c0200000d101507102c071421143c80c06c0d0207080c04601038039a4500051144520903160f4a04240418180c4e4010341c0402ca040807550616014402c68007110909400c030f5000260495080c1c0c02008009130360075841c0c000c0105455801c800307600305613450009000045802d620b0500255400403200150b20b00b0285060304204d0944c0141000d14101c804a03565003210540c480040d540072030030801c107903401c00030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 57191891 1250 57190641 57190643
    0x70605070b0c04090c020105060316080706121b0c030e0a0b0d05090a080309010204080c06030106210204080109060b030d030908030c1b010603210302030c040b18030105191104050619020a 82
    0x10401c01c041c031205c4003c3c024903041c1c40d030034801d00581400001c8510160008400d0b40c41c100c0261900c0c80c035144c41614170040404100179896118903200181030010310946041050603100e048000d5001d280082c42422291365651081d103802c03000340811402c1009071070011180040024081c1c03a0300c0c04003072802c0c2c4080f0001700304200003c1004054001900030700229903010341240c081d00000410020207010900603a4005011151442c0f4110300042080881d641281360062400c2c2d22080b102e03081d202f14910039240c6c2520f80e106040719080800414406441034075040080c0f040c56a24049030744400f4080d581010710104880c40c0140b0041445804560103000820445659290890382c0203441444806660382202c00d44034514028000c4038402e024030088103140070700382000d18041ea045805000c100341d02841c0d400d1100c5d01e0900c04c45018144403041000d03041c00d50381440040d03030410300c66207500080c1441f0812160f2a0395066400000c1070f00040c0c0d2410b5503100c0200d01c3c01c2042c900c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 57193141 1250 57191891 57191909
    0x901030207200f010302280c050d09150c020a090509030d0e060103050601080312011a0f030405071415030408090111100507030c03061202010c021311030603010c02070605070b0c04 79
    0x8040140c2e00c011550150036203468180c924141e0041d0101e024100c883c2102c011301d18400c0c0d45108000d8040c0242c01e529007000400f00030507840f503600e011405e00400000c11038443c4248554030b101250020520550700d0003800e1038146034003003605c0c0169440350020076920b80001c00d070040030510640c1c82d4081c8850b0108440c440001d440c659800c001e1009a54901034140007240c004008803c4601e0703941042d44d40c080d00e03481d0195580c00c1c0e4440c0f03500300607850814840144102079542c002c0d401a409000240704141c102601c082982038005003c6102d800348082104020105000b070702c0d8420b0b00181a80d84407411388005035400c0c2c40444440fa072034001d42820480340d045c198481401802c1d6a0b1701042940d01c1101c0550485843c0d000380c400f11070109442000540c461600c0380d072000c0c409060800d0f404440e0145c0300c180c9a28940494080f0008400c01429080911074010355504510040105520b400c002800c18800c2c540058295410000003e0100c1c0715402200c0040040b00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 57194248 1107 57193141 57193163
    0x12070525020f0a21050307060219031a01020a06050604110c0706080f191a06040609031505040804150905100302180a030209061e0904030513080706090303050901030207 74
    0x130300301100d4511003003103004000303983da00240c10980c030142e0140700d612400312030213030966059803c0d0400b012030041802c04180e078001040036145410010026064850501290240c416521003960880b00050040d00e4088005890350450320195110400c075201d20041150b000f0040d00c015154220804083c0c9428020f5030200d9143c01940d850080c03000c8080000c08d5860300140d100802041c440c150820510103206036004840c1c440c0403080000d490b003913a4140b098000e50184170b00d100c0e001072641122a005905110191900030031030f05030302c00801e400401a52040051480a5649100d140f1072802d01a8024064075401020000550741e00000c0c000c2159443d40401010702d10700028060030b45440360316034000d49c065520039558484072170310030310071403499071000900b54000c11042084551106442c0300b0343c0d80c1403800c00e544103201070040780030f0b000c0d405014002103007103 = true := by decide +kernel

theorem cover : BRFrame.Cov 57014391 57194248 := by
  have h0 := BRFrame.cov_init 57014391
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57014391 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 57014391 ≤ n) (h2 : n < 57194248) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
