-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0436
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:48:16.24344+00:00
-- url     : https://prove2.me/submissions/057a1c75-46b0-410e-9ea5-71ad1a160095

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 78237411 ≤ n < 78417267 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 78238661 1250 78237411 78237433
    0xf0c0509040c0e061206071206120302240601021504020a0b040305010c030507020f070519030203060408180d021509010908100207020103150f0b0c0f01050a02030103020118060503180a0503040305 86
    0x101c3e0b900901018091480550b081044903c00507815812081c10304044144041d00c0540d14090901500044180d07085000310701c08162300050140742d80140501031481e014030703d48500562810440c1c40c1070050340f02d16401c498140c44402c1c01d94010707001030603000e245901c41022010a42c06640100d82607035580c03030141034266040c03144941004107840640203d041c450b0b60107949141a008891040302d21000388160104062249401968090305441c124a0b150606001640041c641c00c002c17130910003010005072a120301150300b4076030300134004507209401030f030114825040740c1c143d02e05001845101042c0040700f00300050b944c640100c000b583da07105501c001070a40d06c0000c0b900d164104035840600c015a10750555a06031034208400d191500c0030160040e00c0e003d000310310709245500e054140075408140e500154180d90003a00c481036200e51b14040c282001c541407003900006081407010a1100307551404500e07040b80f040084650002403506c1c9e01d811980583d104990760303408400076038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 78239911 1250 78238661 78238679
    0x30a030f03110301170f2a03150c0a1103040503060a02090409060f0605030c0a051005031906080d1b0302060606030702071703031b07050d05090a15080106020f0c0105070f0c0509040c 80
    0x8110283c0c40c402a000421f1307a100d031090380c4060f080415040b001d072801115000c0e1001c010440901251003121941c1d42418200420158400700c0150b00050cc840c00c0310b040a0000400c80d000c031000038005100d01e54841842e90002d41001140d00e034456104d013007450108079903009111b4955404080005e4103440c1504051a0000c0300c42c1050080b200038074200080e5139a01004040c0140900b845580ca5030341200312840e6441c01c0081500386464a00040b55603500000d481e0a80801034a030b1130304211110305034007450800c518000700182d001c540091900c0c1001c81c050342c0c11880c0c44c01141e01c0c03540c13103601c011074030041c40d661040c01e071b4404400c1001855100e078210780f0702d110600c13490b07180c1411602c0d425101c05044a200040c00000a80300c62282c48030b803a070100901951a00e4000c0e802090001843c2c1d0500b03110b0640184200300381d08170944008103903401c1400d41611042d1902c0041d6990065041e080d10099506c2c80c0030f00400200b41e158034045510480c415403041d089035060400304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 78241161 1250 78239911 78239923
    0xa050f0a151503110d05091e0307060b060d1a0f0f030d0815040501030818121b0d0501050711070e01031a090a0c230f030a030f0311030117 61
    0x455000d4100315880012031508541d20080e503480c410342c1209040450010707405072841801c0e0030a5442c0c006040203000201d81e00c858003c0041034141c03402c0d80d0030180300d07620014046200c00b131aa0010080c4200080055110042003039010340b540703040000001889003101c82052018005800401d084106460720402d1031940890440c2c410075409418070105e540e50344003444540c02c0c003149001042030002c441e00340d5400340400900c01e201541c0c4a1820b0b4805800003800f844449180841540301c91400003a03006407007269100800c06c0c5144035400d6a5400d1950140d81d130481d90b8480e41c8400310310280a107610941964960041c109105079102d803801c81950720035810080c040005200085401740501e12200304010745d4085612002065414108600e800030f01901284200052005084011460f0386012440e8101010108030a00c283c0103620320740c103a0326800400c00b2400090281c5007a601d048400e02c0d0004402c0c01d10b41c0d22100c20307402a041148400b075602c2d40c0300001d010030801 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 78242411 1250 78241161 78241171
    0x120d050717120f0c190921020f0409030c060f0606081803040611010b1e0f030c0904170705010525021902150d0501120c0506030103120c020d08030a050f 67
    0xd501d1034000d002c18248a8001e002e08422031101500b40031500003c0f03c3d806403010803c1d083d641100d810760301d62010f01052454411402606181c0c00c10b8000740070071640b0318079615005030a400001d0059001c000050600410450074815501004004a0340b64482c07076840350300000c030001d840c50500c980540304001c0203100001d011460f2801f0b111110300401a101110b6945c1401850800380c52007040c090300041c400c06804c0002c1c14040e00c1500301a1001c482c0c00001603550b2045c00c0e04400c01d01d40c5072a0964400341d04800804081000502c541c10403443c104140002942804000c1c6c1d02c9a0a6441c19500200480c503503202c024100e400340c00251004004900052492a07009008066044441c1c0c0e0080c0c8500c1c003034913400060202c000116500c88038045810041d079030b1200100b4440e010041e0b01501e010103901008203c3d41042004c890503a50481c90385201242407000072101c5028401080307800140c03201034a00018000400381d4025118540702003031620305070140100010000300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 78243661 1250 78242411 78242453
    0xb06030709030b10080f1c091a070212060405030c010c03051e0604060803040f0f08030a120e030f0a050a0806040507050f0309030c0a120e0d02130209120d0507 70
    0x1441120381e001030480c0d08490344808802c0310b07940d5034148100701c050268001070150040d4580040f6840020401c0c00300000380280d5041d03d00c4c14054100c88507641401950760a0700146e1807405503400450181a401d0703c0108540250901510880d0602c40d059808503a20b40c00895100c8103c1403e0192512900042c43d081059103000b1040d070715214424003010408605a00101d00300d6141d9401500180070030808903a43c03187da400e42c0002e41d0641b4400e10140e25602000850182c3d0003104543e42220700e0755401e030403101e4001c43e01d00100b070a5041198207103c100301c0010308001e1400600450683c07030701e80b1600c3c0c854164001c0c01c212030044c21248114030384020801c0d00764001c41a00c0a46d0028200740b900ea40c3c4441c4114a5449803449a140e1031140f1141d450410040351610080600c0d10381d980410071500806000d003200303550200941c00b4901d0b104e0b004204040341d000d448100001000c2d0040d004503075241034104503800088070005000052108188214812810b0144403154 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 78244911 1250 78243661 78243667
    0x20c0d0209011202030a021c03090503011b110705040c050901030e0105040b0c0703180311120318130b0d0309140a050d08031b040e010f05010e0a2907060603060b06 72
    0x16002803041e040501860310b1001e1181400000c0d500c003004010081503014021500c202000e00c00b03088006d1402000300c002504003c070104640c1818020391850300040c0d400c165003004000d1003a6400110094030f1359080c07007501c100060300c0d0b0700e5000d440740b045010340316035036520946c1d40014191035240079401403e0781480180700000301c0280c0306582c041003621180d40c4445003803400b12158050a109024209030302500801440210f458008040c9000c6607200c2e05148500d1a50b0740b6070040c20f91012000401c40d0f80d5440d6800c0c108803020104100090002c1d031034285030000740070383d0b40d101010b4000a5444600380f100004d1400d00d604641022203036012040d20b0303d00059200c41d000c1c80010281240440070446401814412220510300e20300d80d90340310b9840300f000840300c1d18240725855803c506800f0005082d4090081c0c0020002c0241810100074281600300c82507003598009845903020130902c00b92604002c101401c0510b00c40c007008030315645541880016100c032640081c0c403480c410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 78246161 1250 78244911 78244913
    0xb030703060b070f030e150f040e10061b0804030b07030b0103060602191b030203120705070f050303070f05030c1006050a05030d090e0403020307060c030504170a0504060503101e06020c0d 82
    0x2000e0013008940c50b01d05006440d01c00e0300425580d42e8102c6400360810001f04005000328111006402070380e0840c071042d01c090360340c601e0345100d101c200d01ca41d0307020465444103500405c020b6940d00d10301e179000d050a24a0569a540d8030880d010040314500002507030360086a0b0b0b55a03041c010f1200400540c40180f0503064074400320740c240d080f240c0c0014a240215202184c400450f85107003002150001c0550b41828020b0640c000c007948480b40841d807034010032601140c040104000b24050303079009002542064010b6440000540c45414141c940340300500040201203010001d0490071944d0b4070000c155245020b081c4401410aa00098071036089403e0843c491940034244608840b804e130b1154030343d030300c5a0030103034114403a0f0600901030070300b0400203000150f0550860342c010342c40b80035407890315141120081464000c1500703100001d03008100070004540310350007541e040300840c0c06550000c4d41d2840901501c00390010903000008550030b04216594041c495441072440a5884c00f0014a007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 78247411 1250 78246161 78246173
    0x1d06092a0d06090605091501090510090207050c03010c020f07080f1c0c0204020a030207110108010b2215090f12020f04020d200903100e2e05010b030703060b07 70
    0x6480480d000d621844060030074448503822848143d50010700030031550038404101d076220f10400c6803d555240c4400d000059080c414410300340304155a505034943c1d282008001c0011b50301c0340b00240c446108056030003504c0c0c2d8081c4124405120079400030a1601d0200b414641804441d40c0816102d800803208000e02c1000031540800041018048440e080c40000b4155140ca0200401039041840480c9801082d42c01d58014107516000e50044041d01c0044001160846802d01a68420510504c8203050701640e034800c1e00300c104008042c41011503207915009010100c2000c80f80d00041441c0f43c10417020300078044420250001441181c2e0640f0150082645007000c048a01c0c0a241e00181c07205c0c11070070395482050125104046044500c01d40300000526070850349203584a4040c907a0450740c0700000f0300c900b4103050280c00151601406c0352812005214420385402e40f90680051065126041842054040c0c400429826101e007002031006003110403d0b04481055a42084030742d000c284 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 78248661 1250 78247411 78247483
    0xb0313051501170f0c0105070c0b030f06010314070c021201020d09052803050a080703020d0c02010e0f0a0b01050405100e04060203010603140601020a1104180809101b03030506041d0609 81
    0x3020301f400303640e43c02149170400c0d030000c0325032002e03040c0d00c0003005000c0048500d001ea140108400d076000c2c005070708022580170307550000355804400329083c1c1480600604204da640c0720094060b0000508244508908000b17444407854119003d4001000c14802c2002c2040003204550345401c1d8203d02d4070559070085c1ca144281000709090207800d000050305184a50119054008522001c0c0805020320501a010341350714194150f0320700801c2a071400003d4005840c6011301c1e0495281b56070369103441d061100401c2e001e405070aa00d041003502140505d00140e0b0103010b148168001030303482d850910020211003000b1078295202210078248029030380e000401c42c0300541c10070a0349203841170900000e00100b14100c0c1c0741d014403a00c2d9180782d09010261010340f8841c20b09031100c07030001c0186801220b41c03170150f8282c5100d01c00788240a9000c20f100343e005075401800548000758003141800c12402c4d07038807650020f241c0c40d0701020800c042034a0030f10070001d1a6400700801c49a03c0c44807443c2640c0d801c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 78249911 1250 78248661 78248683
    0xe0304061b1b030503090907030203100303050f040e0112050f0a030e010806030f100603060b310b190302040f0b0102062212020609070803070506010b0313051501170f 73
    0x140d15001030018805181000c008480b200c000c80360406540345800c9481e40c00c8001e03450310607260400000c55040c024000c17641b10f9021140c4c26071081c0d041d980c0540302d41e000b20301000c2450409001c049407000844527481c1c080c0c0395078068050300341414901146003490501c10b024480e0001c8203a0400607400860050030316209080410307580d030320840405e281501c012041040c0e4071907240c0e104e146490aa200c24280c90144105110700200c4405000c0115040c1c481401004910001e0482c669811a011850b03100050310200f0301e481c102000403003410345803403502500501e80001b003085182500c5804c5441e50010014007030421000b002035191003004054420801580d00044074490b450702002c443c030f41d444031040e400000c010b04002e540700c1046545a14510517104042101c1400005486c200340d8010300038030079607091101e04035190300041c01502c41e020811600400190081c04801807000d081d2500d081598501048516440302c1421505242e0300055a002e604c4000070864070340e01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 78251161 1250 78249911 78249947
    0x100201060b0318010906090303050907060e0f0907120203010f210b010b0310050303030a0c02061f0b0901030b03010e010b03070611030906030c070209070903020a0614030f19021602040e030406 84
    0x10b400d43d000f4090252404000003441c65240c0242d201c20150550f0099009020f83c0d4101c88043d511004156000c1802c1c01405c3e07404000343c0703100c0f0407502e030803c1c080d44d015a95103000c1d9060036001c0390000a981007038100132060380c0c00c62001d00482c50440f00391400550010080f80c0030300741070344426001c184180501034021900000040421a041e01e81d10014100a02169502d00d0300e0f490140051806409201c010301450001c038185508216400d5003c4280d002d1208125282508807610b039403040d541031b41410707240d91501c174581c0d50078440c2d8005915000c00104042d49508101420141c26401000a010000c0f81a21b10355400200b5241d0b00e03841662440e03500d443d0f08ae00719405010b6814020f52082d082d0341004072250344a00044100da20079030302c5001039038039081e0070b444200040d1182c084801e8107000140001d0031200342e00341c00002da44075a419490b003140b00c0c901640e1208070410310700340028000c481103013401c0c1b24224401c50b040c1e01850400340be045004200e03003000304540d103034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 78252411 1250 78251161 78251191
    0xc03060c270609060a0302030105040b0301060303051206150a110115120206030910050c0406022b0f120c0905130c090b03190c0306060210060305071707031a0402100201060b03 77
    0xc0c1d11050203c80051000400311a1a58031a41008002e58824024207000b41d0618081e0a028241401a14152503158548500700b2554008401d100d05004040d070350b112440c1c2c1c69109203442840000e064883c16592a00d403c020242545030030b6072807000318031a0132200000100403c114408080d0305040c0d044400707607030b80e03110040c0c8180740400c0f203c403003a4018500414480002c60800003030086072400d03002d41d41d8a40e40303c015039004100300f4113440345078404948a001e010740f08141c0071140c500c07103090001c842e0101d121144111903a0000340e00110f144a40188031502e004800c0c0c500c912082d450a0103114240740303006040c40300501c181200c3d102d000c00420034413005100e03080d60b44d4084800402003c0c0140a0083c050152849034030098010303000c0401c0544428013900d000c4d00d420800400b1010300d0040000300c000b410203078058480c09614404000100c00f034042c181034140c21400090381e0b080c540100001c1018100c40b4034103584c94418100b00021320403058070342c0300c0701d0000c02c904 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 78253661 1250 78252411 78252487
    0x105040e0f03030907030309060507021503090307150b0a080715032d0c0f0305040507170c030f06060102070503060108060c160209070f031b0206040f060912020c03060c 74
    0x881c1045003000d030940341c0000301c2008402c4000081c103100301c134069503525180a65500c4207451500c105000650000003040030700145824181c0207681201580702164581001038950341d01e0710710385600303031804984ca4641c0c0c03203030390318080c4104c1d000340a220000c0c040d014a8102003c00c502d00040c400000d16449550701c0c4006105800501d003041c6100b4034007003aa0107918040401000b400100700040b1795007010072160107100344a110310a80c0c1c04001080c0003070070b1881d0001c05503080c01410019204a01800c01182c0f004d018920079002450010320b0903060000019040c9a010b801050080d4001001040b900500107a00b40c2c00420801a0f165560342075a00d108005006070006500403031803130188400305a005400c21001912a90100811aa030003e40b60100b4400d126010050f44034001280204003401c1040c11541d20501c800079031352106a6031040e40c2007810012102581101010078018102070013520751020a50083d14541a490f1201d0024a03101c042003203901014080310310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 78254911 1250 78253661 78253663
    0x819020d021504061d060a270f05210604060905071703030a050a0c0903020114130305070611010204120b13080f0a0306090207020f060f0d050103030c1b030201080105040e 75
    0x22109402800200b151070298640000c00c1e48284120700000b85c520107031100d606540b00051000b688001c000a19003491864200d404241c5c0d8400740c031014115010003940380d012548008010324024400410503460001084a0201c11000031101c03150300c803e12060304000420103a502035882403000688003c58203100745845040d411500c51030b0b40704a500401078100201031449840440c4040c800713580c0f911410810783c2c09000c200f070042415041f040c0300640c0180381c1c60f030b40080c491500c01d081c03010141700e40040b0f003a070b60b00640b030b03a170804031080c00502c1d4040c1e010f40c002c041910007580303814a401c040c200c244401c80000352a865400002c80c4410720803c1d54121965040034409407034840c441182201a40820308101c0441c3c82d00700c0c0081c0d08030300d40c000c2d522000d0b002401484d030300000c1014002603070301c851b2117820f04102c2080006c46003040ba00c2405d01942c060b64407415552614903000181c040350071018002d8010846003040107070b920000303d07030541d10b05135804a00c2400250304a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 78256161 1250 78254911 78254929
    0x3030a2a12080402030c030a021e1203040617010b2712010504110f031f020a020a0f06020406080a050f010902160f0b100b16062d0b100306081902 64
    0x1e0208140c0e0400d10003807a031280c552070050b8001c41c2030740c0c1e210798034038101907940b0b4030360000a400c103044a600c0c044580c05000f90717030901c0030082d2108041404466180d41507078000d400070800b0230901d841d40111091240b000383c1c050904040340c10324100d1494429001000b50100f0840d800c1e520614841158486150418811900030028006820301d481c0080c00380d14200203450142c410356018000b10b14000802200110002c0c4004517a48001203000c2d02950010401c0ea00798820000c1004c000741c548e0000900d00d038020702d07005072100d003410401485c0240280400e940395042c80300740720f0030418456034a8115420341d040169070703c0c907a100c2514401c003080c4000e00303d03108039000301c0d0038014800070380c0c2c0c801e0000c45001c0b52901c2c0c6841ca8060035014201c0041803401492034408001204c9070701616414080c012800e12003000311840b41e0705145040d118807001600c0301424192400c003050305c4119500785042c1809220706000140c0d55840c1408a80c090413541c006c1c800c019500c680c0c030a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 78257411 1250 78256161 78256163
    0x409020f040e0901090302010e12030a18080307080601120c08060915120a02040e0102030103050703080a140412030905030c010c030309020a0909080c07051c020603040c0b0a02071403030a2a 83
    0x140480a203400d41c10f00d4001d01c580f1006401550030401c400880e8800412141000d00500c2001402c42d2195800c1100404d24281c2102e400b624902558011811501c0a18816400c0c3d035100840c525100f00014158003480919034980390816203484d9641e600003a80c558002c0b01607692a03d190350341646240240181542d85401070980440b0700806171010428100c00b42c004d4405000c00b5466201041c20ac0c403003403101400c1e41c2c1203800709000007820302c070040c0200f4a091a010b445d44c0700c0e000d440c4200c4d5000d9071110a500110380c0d51a0101a04101c1100c000d000c00c030080c100320701180b40043c1909042c00c4008003050b564016102c115030321940001c2c0174020845042002c001e60745408850b580c00200172509611504030f0014280c40d08003180c0c2c0c41440344030a1080310103c280d00b0f01007141c0001c0c02c1203689410303041012031520903070780103000314400903401012041c0c58051900100202e414072a0b010703410400401d812142c00040c0d02c5021400c16498034040350103100c000c4070355080400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 78258661 1250 78257411 78257429
    0xf061e02160801200301150c080d02040e04030e1801180222050a090b0d020d02030c041a0a0b040b03070c1a0103060f060e06010f20120a0e0a08030409020f04 69
    0x40210b5107080540c003c81e82041aa445004110704100c1070a490740424403a044004401807032507500c0c944201e0354800d04602c02d01741c09090201c1c0800f441d00340d0304035403c8030309101103600400007416481115213010000c06c0d5041043c005070710000450b4032005005040f07025000c880a682103035404e038103c80102c02648540c11205903480281801c40c6050b20486215401c148c8010031414240e100345222800010300345504002076a080c09800045040c09a0b8180204038507141a40ca072405010103140400e401e00384180c119404022a0983d06d40280c408003000341300500107181030404603604140181085e03a4a0111454800000704450220030380c000400000041004843e421008035001000c50a000103511444011681d010440304140041c01401c805420b80e4091640c94818500c1e800080003208000c14619250100700c40e100c0c41744010025448400345c1d072020423000c044000329010b189030b520f0500c51950ba8007881c09007581c4141e00061040c0d003449004121002401600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 78259911 1250 78258661 78258703
    0x21903052a0a02070f060801090b010306031a0412030b0901030f0203120d0f200a0806120f0c0406050f0108040b070e0a030510050105040204061b021c0f06060f061e02 73
    0x2400c0390700c141d04620007020140c860200b01107085400e2898400c10b1355201e40e038910980c1e10700041040076114040c49030303041c99602c40b00071012407070004c16104026048640300030780e03080c1450007901500340345034004100361901c81d41c087c1070760758848110704494104c080c0c821504240d0000900300010b21110102e089400140015a4106074000c940c202400420800c40e0750024000d000d022503101d041d64902210801030361817154092030201d03801480241c146400140d040c80441c1c40c0017800440c0a80640c000503500207203107818043c002c05080240c0d07090003041440d038006412004054401050000107070005109144228603500f82000c0081400c404142c0d00c0c2801e5456030100c424416005040100200b0a03003024000c507004c8441e035a0f5080c100079101da00c09201075410782e0040303034007060b400700016008800010011205002e4400d403140080d0926214044941365804044000b88810040204c41d403c03950b00341d00140c0461507000340c240000c804a09102c8100b4060050740104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 78261161 1250 78259911 78259981
    0xa030c0203120a181d01050d0303060e0a021b03070b07110c03060c040503010e07060e011d0405040809130c050f0d150f14030307020f040b01090905090a060c0302190305 74
    0x40704a20481e05481d13282c103480a43c449900c403048050a0700704020006461004100a050141c000c2031014042d1400040c107a8451002c00304845041c0c0395140c80e180c0110b9081811890007400032070400306800154581203417641ea0440e40000100014184000c8014505225034144060101c910009003600d005140000c4d03901c1e840d812502403280a90300e0840080a030540005010041d240107840d50544400588011203020150000c4070004080341940d40b00c3d1030300d1f14010640114407c0301e41c80d4540201c081400100c545040700c038610141881c2d03800c61030640140403245d2104200041585c1c0364000301d801000340ca075085801c824050710b460002610030401c00d0f600b0503511020410030525030030b142016580e004400002c0d40c41030f00c2c4400302030b052416501c0044040d20604008000039074030080c030000c5034805c481640c001c3e00880c00100410403940301d200b050304842d007411410001c191900540104074002d01a0230b155588020500e00d849445055001e4505100c00c1a00304003c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 78262411 1250 78261161 78261167
    0xc02060421060506010c030207271a01020d0504060c060506270402090108150a0507090e07031b0309210212070c0509060904050303040305030a09020a0b120a0605030a030c0203120a 79
    0x40307400d8a40901d0300010a109610a510b83c10100d40c240c1e00a10046041c9440c05041000144848a01044601e608042120240130310000168410500b552900140d4006420030315019034540402c04100b20034009260802440c910654109000003080d54881d404122035160503405501c2580c60080e44290b42501d0b030742150320541c82540d0704001a682e03403d481d6a20f122000600e0300c102c02001c0040c00d041c0080c1d1000d03a108103649000d2898a55521500000300300695103c80040d4941018019514440c42d0f6400c06212602d010494404103845050071070310201090103096000c1612600502c1c42017180b807041056106910b17503101d6070b6142a40b410405071103a1030081e0140d400195a030300d00132035542e1089800070040c500c0c60b41c2da0b035012142540002d051900d03407999400804056160003061001803c1c081e00d180e80c0c4d81c04181248a80380000400c1c5081c0380f42414028403154901169070f00041c0d626042c52290b6412501c00039041145401d50b540c0c0c1480d000c1801a40b10303038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 78263661 1250 78262411 78262469
    0xf0715060b031e06041413030207150f050a03140709030b060402030f041401091505070810082104090207060203010510181a0702150d0b1801060c020604 67
    0x1124041009a5036864001d0035040c003040320307514500e400300c1c038000c0c03407902481201c40e50081c401040090051a601e41554143e50b0030340e280e40c002505058103004151301045a440540a160221344920588030b0004000c00e0940f1411802c210740824846002c40c06500102402928600d40704c540d403409020007800c4213210300c0255000c180070780108813103050038030859001e044000d000c0c180540e201d8840220070098800f000c5d032199071f07656845020403069914103a0180615401052034180105c0080c46488041c020b12040a844c3c0e80170041c0d0000001c1100c11001d41e02e8040c5000c1d801100f11443d80c0c0030719404200c00030300000b6800e0801903103500841c140c0b0022500c1c840304040b40c0000b102c505450310480b50034118408400d108507001c0121448c80d8080603500b0515101c81a0b01060410620001d481001140446c85d1106c40e00c2e64000c0f0103502c1002e40708002c05d400d062440140206041c4540d000b03204000314034400755140c50307007180d018203a03600d85103010b05680f201c025031301c030703 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 78264911 1250 78263661 78263693
    0x10020a0c0e060a06110d0c0c0801020a050702040e060f0a111b010e07080303040b06060d0f020705070e090a0305190201020c240703110706110903010e0f0f06010608070e060f07 77
    0x42c50300c9004151203005504415116080328000d002d11b8000400c00d44905071881c40944008000c3c0c440010780240900041040803019138403182c031580703a0300c188400d9946014034035415820190400550645600c00c440d4841e00e04100898815544034409003648202050324041001c0450200402c0005410940c0e25121600445034011b90f00c0c2081d81c2c4a0005680c000c0502c0c0707031030f0b0200f5481d02e4040702038161020010000039a40700c00804040c100e90001200703c0d0103400985c000c10480000c405da682d44142170700081c002203652903400400c11301c114081240303030088a4070410450341c401d40c19202580005000c0fa4051003440d04542c00e401701e078103000c004150000002500c81c038402d004207214040c41c112403a040101342c2d038400d000f5200708204000304031014071200303072940c2d42400742c03140811114018158880c44000070504112080904806030b0788940010400182d0021696501c41028500340700b500300d002c80002d44510414440748510100801d0100a000300d82d0b4000c01c0407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 78266161 1250 78264911 78264919
    0x60f040e07050a080601050d08130909060f1d030d05100312050c0c010507020d061a1e090109020a172e08060901140a0b06070602040609150903020f10020a0c0e06 71
    0x226680d0310085e41d6003a09018140c1c0000a1552850000d4424006800e020171b4010040c5551512051128202c0721140c1080e03554a4980060031880c00c654800c44098001c4090014031911241c20480d43e64800c0d041a9082b860f50b840c0042d90840401c0045400f656000c100e04144400300b20300203285070401d489480c018041c4030084800c40d800b0300c0c00c07a950340d0b501420801d1010603a0322504024813071000904048008241e040550b50741e0101b0035003100081381c40d100d14980d02c2c0f0007480440c2405030841e0801c0b41c4100304480c441c0d03821140c0840c1075101100b0300c0e12245c1d20003803d00f08150140310402c0c0c604196004c0921100140c9002f1030076640040201c506991740c0031001400d03100c1284002d0785220409021070395818a80e04144204d8038060916850030b409030742c404089910543c030910015415010034407038070301c1860b106010546145410444182141c0020702441450224184201c0c070092440c400f00f0700a2107a4031115070000b8112144655801c1e411034050b0040700c0d000e03c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 78267411 1250 78266161 78266179
    0xc060708131112030c060933010909020d12020106060806100807050a02070b121006050316050304150212071202071e02030304050306011805010b03060f0405060f040e0705 75
    0xc000000c01407014031039004010307a40d800e404a802d00c041440390b1400400039000c20451a103140d5070030010103000300d5080300207000d00c41c1c04841148031140c0106602024214820003404680c03100352140b8151455400000b60785142440042c1035854142802400740b05402c8446d0701c0c0c42c0e010341c403040031201c49859902d22580e0300380410801201d405c00b00701c00b02c0e82c1c0c000440c001a1180b0301030b005c034042d00e0044611032a180e000300f03050354008040b01d0b0802c1d000c1380c040190043d681c078880c42c01000c450801d14114280070f400d220050f50482400f408111000c4000340c188160700a19024000e1120002c540e01c6404076450300151404231038a4000c0f520000c50703c0940346952088805864100c8416102500d00d020030b107520245441003680e040c0700600c008102a901400000d00034685140340c2c00365008204141004d8503016032042a0540061041203820740329406420b01c840c004403400a01643c030000040d031b04a44001500b40c01c1458880003200f0200300140e06010b5400072580a12 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 78268661 1250 78267411 78267421
    0x30705010e0607060e0106120507090c080c07080702010e09190c0813060b06070804060801060f02030a05030609071e0c050f0318011103040306110306040b090702030412050a0203030c060708 83
    0x1469060035501c0c40d410010822090f40842d801c1d9115003510a000c07000455899a5042000040b540c8044151a03d810890f01007207004820f100c0c1000c2440b040c00c0107082403400c21a0030680740150900500013040000395a011a0b20a6440441c007410040003074003d82002c10101a800e040000410a028603021030201d240e80a220050310907041d071181c1600c0096130b82e40302006000500d1189810010600044001410010140002c2c0959540f000705c9989482001003003e82100515815504100010216150701c4400ca0358031036400e413120811922100e50071104c4014044440081000c03845500108550018031040300314020130840300c2104888200d0f03901c80c8600c206010501a00c00c58240303040d4001c4d944200840340d0082681c0c00c2c165692206026102404a0f22442d40f00010030000c05c0d00d030078403070000102d10545003254203141c64840a5074900c101c1c00b0702000c610b1006000000c2004c02c1241c204220f6010302502c0d22034104031041591000f050f5142808621544001340c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 78269911 1250 78268661 78268667
    0xe03040b09030c0a0f1205010b04050403020f190f030813020d030306140103061202010309021309030201060e07020a03020c01080c0f0f090108061c12031404050a030206090c0a0b0a0509090c0903070501 88
    0x8401d50300040c544050040ca400e40000311403c46d18000c0b82c19540b01d800070a0255210311681d4440c90183e006400312880f03001c02e1038103240028880000d8003c2040c5080041041c030f03010101c0300b5902d41080042500c9e03903180d88402004100000750701501c2d0000600800d036058006a0444031038000e070500300f9203030100560944465014143c95011030203880c20266200350025901c0368006000d404180b0380410480060301d007409010390250703442c0c45080203013001c407001c0e0641c17125451000c1c0800c5405035600035158951030100c24108241080401ca0350825401100c1e40c04580d00d42950f80c41e200e680e400e00346500b01c3c20200f40440d07640400101581480400f50f0a40c0081d4240c030419800c17141d44d100c10209011b000b00e8209a99040b2108449680f00d084a0055000380c0041402007010700c0d00070303d4048010190035890304404400b140e2a20342010100c20360314140700c03803904c1d800a240210707441d018503076401da8046015010720241480b1500181654041681a50952034881c0019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 78271161 1250 78269911 78269929
    0xe03070503090f0d020a0f060219050d030b012709050709080a080a0c02060315040e010b03120919060903031101050403090501120f0501170105011202060f07060e03040b09030c 77
    0x984290420015074419140c03c800d4641c09000041000300c030300c40542c0124003102c41035000a00513178501002480030b01c0c1c04000080303144070409110b001c0490703280e4600f038852107000d0b8030b0020f054541800c3c00041e07000d0000e0b004001e0505e8003070034944100b8444030a03c207001c0c2c4292074107645050003140216228201c0d120a4580341802844141c1031541c81e101c295200d00010001c101c0d40c491003900681c0c4e000c0c000e5015034505030424104003003450403c02145c031882d080c2038503a890401c585003291800710720030150b68105103809481e0b10801d00070500d01015840c0d94040240200c1c4003190075900111910256402039032036040315044102c80d14201d070307001d94002c1c2c0400c040a004000c0c56201c2d15825070364044101001c1a001e0005000109541c82038105985110b000b10700d140c54990300344a00b0340100300d01e1030105411940f0350040b9486220b45403103182c940744001a05400e00543d90032110503590500d044a68495407102d40204581294940c03910a0084000c50642d514082c152 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 78272411 1250 78271161 78271163
    0xb16080f0c1207030b030d051213053a110607020105010f0509040f050715110604020603040b0c070b0f0a0e0c0108160905180906010506030702060a2007150e0307 71
    0x20207482c00d2502c0c0e0100c4103107140186000200350304c07091042c001e070710203000303808800324503458468403100f543e9a83d44084200410502e000201c110148010a400045890140384044051500000074019056042500882e4005050808a031608105030f22407418420070111506684150726682812070030ba501c28801c001c41d40c0d03a24a001d105071700d42071600c50341141c82800c28400c4544243e44103400c0c8405c0354889841c5664003000760705030035001906864019544005001e20745041d034001070041c04007a00c003815a521080006072007048020482e50325a0b000501d6002e54070f4074501217080c00100300c421081ca907003404451203445000003801039104005840700718850b5110903c058020210300c65a208210700800d001070581c460b044480c541078100c0c4481310f05031034100b4800e458480107a1240d40680010010020b0556010450030f4100426010100d0940d5020305c187c01d80c008440040e4914050019550003088600340e081d07560085885020b2090306100482141c40e4020410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 78273661 1250 78272411 78272431
    0x31509040f031416031d03151b090603010b0406021b1806011404080109060b0102120307030207210309030f0806030c010c0c2106050112030c060203130b16080f 70
    0x74151000a0080c10801070680d00c800540e41402c0300c200d0300c0110302c0d952503001d80115142c1c013000d06003c143d01c0340100c20b501c0180c008011202000c0c0151580c94001481500c001041d040c07160075000e2541e04841d00000002c001a40340e5850b0300095401d0746c0a48a4030001d0b114401060712004681000041c601e070b03009140c40e02c0d20610003040202c144005000c4c0b41001100c0140e41005514080644080c2c0360010000403215143e180c000704680da50741815042d5400002c03112420301e504e500b200d901c00407514000d6201d014900d085103002c540c9118980400c41c1d07042c0259120380d8103034040300e110340c040d5482105901440405544114051b100c043c0c00d50013940c4140815405084421103451040c020a42003e654032101e02e0306c0d02200da920481c0b60925004141030003414000d8501400b000c100403114003040faa400740c050000d01100030911500440040c0c1805418180c407841e5680000505109140c82c15201f000c614205100300e0114141d14041184003401c0b0201030f20440e0303461 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 78274911 1250 78273661 78273683
    0xf02070606031406070912060b150d0b090a0624090503030a121404050606010c0c05040c0908100509100b060c01050a0b1206010b0318070f030507030b070c05100507030b0a030803150904 81
    0x62211400b27012542d043c590042c0404004510b03a000c84030040a02c070b90200c00019001d4100801c100000001400e0202c0b00340c2410801d100a4035a43d0314920302021103c01070030309010740401544e00c0043da500055143c040415552801608120300344e0300d101c1c0c003110070842613401071401034880c001502c015109500100010390a9401000f4005403540211346104055070b403580004d082c2e81c00b01c0000000139284100802803441c0401ca8242c0b42240c0340410300c06d41c500400040d50300c2500030b850402c0301d81c46040640700350311840308407168200003000a120324602607050b039018004920344180140342c03406c00004044004128241a40c1c084400103203140c440000c4628101c1d00581e41825900900d040000c0401d04214400001d40c45600a82940d070b2460800c2c00b49603100a0400e030a10000030b0590b000a600030038003840c1030769481030000e0280c54440c0110010f01070800c1c0560001c81501c80032052000110245100f104440c10100c10709882605015500d00c0035500100059050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 78276161 1250 78274911 78274913
    0x5090f0123090a030605010f0e0603070e0c030403030207051005011a0903070b03060f09090c040f0b0102060403120e01180203060a020a090b0307260a110306060d0f02070606031406070912 82
    0x104010104050014400c070829138807601ca1038201e079401c0c2e01064000c08502e070f00300002c0024a8803168802c90803005010320f02e10740380380c00c00c003400c0040c142c00038100000001000c060282c1d055501c05e980202c2111480800381c2941c0000303080a00500d168450442c059140d01032409040392807404014001c0c01c040c0e882d00181600d1500051b0549a1012104282641d5502c40c1203025104202c0200200314000c408420302c0308941c0d200c203044800500340300621110f81d8000601d2508140e0519042e41700c0c50511519000501c184005a003080d4200508564054440012051040c0c000c9058a0b400d40340c00c0342207c00c0313200b100b528070046007001c64200001d050f103c002d0b5901c102a800c01c45017828244642e8542040c03030031161800150040300b0b1180b40c81844c80790401d82440b00c00d0080c510300340200000c8940c041e03c110400c1c0306031203e504d9842140c2c950107940c00d965001506000e00c1c2d482c1d1070112200440a1a9070041e8400c04000400c000d1041c05100103e441c9034600307410185107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 78277411 1250 78276161 78276227
    0x30a0305040204060b0a18090b0d0f0302011d0c1e0307121a010603021206090114060c2d0d0804030f1b02090109020a020f011a220c05090f01 62
    0x20426a40541e403150006007a8180f05d0042405034001d68650000c1c0362030b9101500c101c081500031903031032403500c0c5680c901522640e40c410209608401c1180280c801340c5022400750041042e009292480c120a0f80983d50b8004ac00c5840d0380021180c10449c0c01c1c8030140c00250084034038000e030740350340098000c0144080065462079058012005109a48014050300c91550802c1c0d01c24400130768005420300b0001d03050205950002000c80b0b002019501d01824612941c201c00a914860300c00007c6a104041c1e00300058441c1c45002da14000008903416003985208030010501c40107402003110301c1d41020711402405129640c9a21010f0300d8048090084072a582c821541e00001c21041032102d025950300c1c20414001c013070300c41026a4641d02118002e0400100c1e4024488681c1000b00c00b060030741c0103004a200c0940299451422500b10384000d1642c4d101004100130a1480c2c0055805101d40c810001c10f905034068031040b0070824880011a8404810244800d07000d1a414100e808000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 78278661 1250 78277411 78277421
    0x90102010b01030902091b04030b090303040c0b0a0e011107080601030b04060501050d0503190e0301021c0f0209010813022101020301032006190201061802090310150303081b0d15050909030a03 84
    0x701005070b0303234201600ca0761141ea90140a8031280b40f99403000c810401000300c0d02d11003401518284091034101411110003414440045000c581071010211034120505002c0002000a0110740100c5d00c0550f524106801c8906050b2000d40707465044c0000429035041c0900c40200f01644100250b01e0141038885a07040f040d0019022410414442840e000c01c0c1d4007400030340b0080404100340301e504102c98401000311030b03114000401581c0140b055542e10380c0c0060310341d070380100e500241d480305c4040380c800540410300c90340d0106c015002c81d9000000c1c40005601440c181c0340703c0c0c148289070b0034122216410340303040115070561105080010160342c5500700550203c011260001080c250b855185884030305180803954110294045050390440c9020000d0365560b5552a100700304c0d1031031110320007809103c0b030b00001c0d080c003080c1d42c085074001d091401c60041502d151000e05807906a100b040b40c0c0601003111140c2003090004002181c42c1c0384c00015a40516806030045142407401582900982 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 78279911 1250 78278661 78278701
    0x106060c0818040e06180f07050f060c060106090311011b0609020d02150c01060b070201050909040f0f0803091b09130309030f0b06130b01080109020904021e090102010b0103090209 79
    0xc0749010002c4040c0d119801104403401c09100034201500c1c000c0001c01c0080c0f21402803c599520240c10705900d0140400e0400c1656400d0320b40f401d40407500002700304544180c500c821980d1144800025000d41d006103004141c030b204603d85070240360030000440303038141e61000d64031600ca8617185801c00114291b000340b22042c40508640341c100903540018041804034a618030003070300e0000300c251041d9001c2c03150358003400e454100542010240c4e0002441409004a12801000c0031004641400324407014202015886051040401e0462920700515001626407001600c101c3e550919000100c41c1e00080360000682049120740e128031408160208e000e201340c0174400c400c500070011074868403040781502e000310b281841c02d003042c0080c40381c0248414a000c03002460815010403c0e0392008041c0d04454485901588517580c0d1400580248550014045180741005209900341c5950380900500a0260020003040120070300660640342d07010382c02503110307403181d0000e0040c190303030880e100d0350f0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 78281161 1250 78279911 78279937
    0x804060e07030605100e040809010c08040f1d070e0d060b0a0b0309030a08100e0a1a13050103030810140d030c050703030207180204080c0f12011e0506030106060c08 72
    0x100c800040003418008281c01c00c1d00c159459004001e0003c49a80090000300700c150040700c50343c0740035101c0b540d26000d01c030443e0341040f08a20b805000d005002007a60081d00f4004000c0d1000c680d60701e0545a41078105003191040210880007480c8203010342d400d008900f0003d000c03603000041c1c640c0d844d4024945101e90341d40c4030801840108800b268400618414984d2000541d50b41e585504054410b0074001c052a646041c441014401202007941e03640d0002e40035000407800314036800038186002440289241c00641040015100b00c189070481c60407a402034641c0c0c286070703d0381c000400d401c0e06903024501a03481241c11014003802c083e058011420b00901d050340961805036078440c20148150700660059004407010300c0a0302c0040061f4044001c102e000710b2515180894440e1586920003c0e60300c24401c14540700c0340c0d52107256000314540750880003003000002038030584c0d550f1160360700f20024040c54800041d5240c04c0510030442a90344588892840c2e08003079541c000664061a0a4014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 78282411 1250 78281161 78281171
    0xc1b0f0309030120070624090501050406090b0102100207061826030106021b030106050d1506141f0c0605180f0c18070903080a09050306130b2a0d0c14040e0106080406 73
    0x1c1c8841e40b00d0240023030f49000f255552400c4100015104560022242c0d00c0ca4880c0380403c50381c00080c90b030801200b0304000760b203403032143c2040b0005140b81c0c0c1c0d99084180c081144242040b4203c128200444540000a000710000c00440e074000d0009026a80240c0d10095500509065051550607290300003000400c00720b445030702181700c2c0c44061908031134071803155040002c100c07a42d000b840e01508201e00620391103881c00340051500548119021403030b514a60189220900c140c0c0256201c03500560207011904019910004c1441c040c450780c40c1c54014103103c800a400040b0341299070303410080c21600b144403c941081155040034012001703000740010300000090a082c05008020210348a90007813601d880189400d022000b000d900b00c10130012030700000518440c0b041500f0000800740792014001d148003181c81800000034142d8810070120b130203c610051038105145c480c005da9a10011051241c40038842400b80e4050314091702440401844544c0c8100401507119028450200d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 78283661 1250 78282411 78282461
    0xb180d050435010b03150f04020d050c100203041511070b03131b050109140d1502160516050901210201050d0c0f080c0a05030c1b0f03090301200706 65
    0x10040250160166203a5184d080088240c0317001d10403440310103000c45030164240f514004495141e900108020f00c5080400d030240c0032f014080102c1110000080c00309006110300c0700c4040c0d601d401038070514050070001c548a15801c0d1040919001c03803030000c4020f00420382029049031854000070140c15071042d9045001012600180c0364606925203180428841424400010f0607000942c020900324003400b4241501d946946a59008060b04070403141004210300903c0c401038441d1a032100c518564414140c070a009010854161000028110000b026640c109004240200348901040000340c00c035941200340014105902c2d180c0b051401d140380401c0100c2c010100c652041342580001c4140c1e491814154010011300d803c00d04003100c460414910300710051092200401c1d02c05c00800c085070b00c51040003450134403180760b00300005803414920f0088480d41d81c1e40042c04064840c2d82880301d00450f03120801280e42c060201c6003941480e118241d01d03010081c0c600100004c1da80d00400403099 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 78284911 1250 78283661 78283739
    0x402060c0c19031109190f0204050a0f090b010c0203060a15050d0b0601080603070b0a050702040b060403050a0605160e121e1e0706090e040507080102070b180d0504 72
    0x200c070704001c030751031103015419814000300c0500902c1350b09001ea0101300038004104d01c10480e04a40388403508000c47c101d5484802c520184c040c1c0e501c0123410051000c2c000c0740004034842540181e60079240100407e18030907004452401d00b800020750550050408079500400780d402c20001d030340c0c1c10040204c0b41c950300c03004200301d4000008140c4e1069924801d0001070742e8005074554201e2021001059440d090000c00280d900c42ea1400070b06201c00002c503071045444541020100000040840303888035940d0910075121a40d80034201d0b009490710700000ea843c1e00c1c52100f0312451070590b9449a20300003e50a2001d0a4241f011810440c42410000c02010310100d01030100300b0944030140021000154051842020080300c3d03843c160843d850502900fa1b01c04c0c1410112409140080d04588071800c0923400c002107034010650a5000269140601c03920300c02e56070040003100001d1032405091440f40b80ca0b0150140e00c071001501c1003108002c0e11856402c0c4441e0b07044030040d46000303070b051200302c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 78286161 1250 78284911 78284929
    0xe15030307060c180503030418180803042603010b0307110601150e012303040c090609050f010909050607031109030105010f0906060f020d0309060f051905060303040e0402060c0c 78
    0x495005071560703d0307034078955800103404800300c036009481a440c4d0304080000c1d451b4004c074040c64940d080c001482c5030000b40c0d65044140003039802848401c90207590304120800c0da0086500f550000c1c80404003045c403031006450a802c4540b0108030b2403c59080a01034240e0b940042c000c141003025007603184004000c00c4c46014028010120010540016000c0142402d0b03611203581e81403007540500c503090f25101e20003550300342d440c03440807541c1c1c0c1c0d90b185400052082180c11441100745060400700342441183d0180d40100180e0b01194451381e81c07201c440d0151941c0c2507006000da00b200740400e980a0007074101001c16150044010b08000140c0c0100b421100242e1012125881c180801c1020000c0c0344600400b900551a00d119221080d083c0a992411801388000c00c15940c1c0550f00705000d420762000010601c01001408282070500d8004002a10696001501490200810b480c0d24001044a04130740c00d10342d100f04d842d5900c0c0c003000303900d40007198a2074450150283e000d040d55030706082 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 78287411 1250 78286161 78286163
    0x9150504020405060103090b0a09050a050a050708060c0403050a020d0c051203090f0102030909150103111602010f030e0a0b04110607030c05070504060b070f150507050a11060606040e15030307 84
    0x646403409004200c140d42e000b500d00c0d4141071900c248600882c0840b00711550040301084d0229204000349030041c9040c10390a4090304902882d045c071410048007282010465a00300300312085070b01c403c00c8098461003244402005c0d540101200c900504014001303e4116010300e403510b181581c0ca202050303407003120349030120b031035000000c4001c024505448850081b400c2840110706040e41c08000c644030150140420039500c82101804046a109800803000345414000b9103885441707211001100880100c0100e0204c0d800e140b00d210803d00c03d101352100070485070000c046008498031500229a0051b1082c0c42d241a000c0840d45146c135268010300c0c1d0306100391703a0b0540e18081800e10a04080881e00070900c10341c1171100411070702c01900d0035a1107598101d9100d004a250510f400f01104507040e0100311030780e040c5000c0142440c0c215019288511481d16480c98000c59201280e89030001286c25071340c0140207000510840c44450a0181e110780d1400c0100c0b107041c43c41002910790342004038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 78288661 1250 78287411 78287453
    0x30a020a0203010f0501030b180a060606030902090711071401050f0a080f0a050903070b060103090b01030b0910181704090207060f0b120a03050901020c090a2a050f07020409 76
    0x30010045090074496007407480400c20b0100855415540da904070b1400c090005e100c00d003460f100c00c001301e03041480b0030010640d00520420100c0c0d1380c1c890140182118070816072041403140001014240201c40030b0850300784d03410203010f070706042c084548407011402010034100502400074001e6044a03900808a480054940440c2031402040030071440702e00074180b2049500340014800c4a1400101752504030368881c80c02002542c0e40d000480081052006c0078003498014400003040c049c5640400d0300441c14801075480134040700341e081c800e0314040300c2c00405045c4134034454004540f200c800c110318a000129441e240aa48180c801e040e40c0220703c1c10b0f1243c1d0ba644014a610b04140d2003800610b18090300e030b580d131400e141d0007110f4644031442805010b0050024940080c1d030300c20721011040090040104034942070411400d001841c1c030588809c090300300d45032029007220310300808081c80784559a030540703440c10003401062160010401241c21980fa14610800100014020059614040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 78289911 1250 78288661 78288673
    0x8070803090a06110615040b090703090203160e010b0d2903150f0a1d01020705030c0606030a080313030219081905030705040302040e2103040b01050a0f180b03030a02 73
    0x200c20032542c04816800310050101a2901011a00c40491110760102401004016000408000c0307000760880b6401950f02095001c2002001e540660008840c5402130b41150143c40008512283ea2805801000d450002d0312004000c0181c000c0005c0c41c058185103000b1440310004c00d4003e1841c00f406604022083c1c418034640c1160508001240f042c01d100b01d4004040d0410120074100d20901070038102d03256468040c1c12030420020716102c0c0b0002c9582c0c00840d40d070300c2c80313003007042c0c0b2a004845085101c0c040d50000c038401e4600051030b5010f03141c22401451854555912009040320800011025800303101030f0002c403031030401500c1080a0041404c2c1c0d03901c40545201082e403c01046000d41070107010300034000c41076400400e80e402d40344e05480028004405101e460b28000e180800c408020607199a07030b400d14071440c030145020764460401d01889980fa0020421446802d00503c480e0003282d49040041000c1d9240210120010240004084808030003090856004d07029140c0543d11071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 78291161 1250 78289911 78289927
    0x3080f13080a11061c18141005010f08060106080403090305060f04050105090d02070b160204020d2406020615240414090402030a02190e040615060503190c050408070803 74
    0x100c0c4001d4180401262024501408400102281c545240d1701803011659448203c080c040110301d441d07007041d0002c10140005a502038000c3d61802c40c0340c03c010116052000010f11010014003003001d581040300546181d03801d24804890403c00100706800304541031400101159061203064040d17000354031418a2880c1c581007440c01d48101070441c525a9011440d080d0304a9408a03c03203040d124922011a940d658200340081000c01c9600c0195205100050385858402a6401140081500418605495594161224008080d1080070096004003001420a8604080c508910040104008110141d10300105030503501036581d0304140000080c140510400c48400c110140303000c40b4504510318150f4042a11100002e8000707000b003031900c0d1140440c1ea00c0f600854090034000306118200d1800e42090030140440545020548003c2003011907404d01c03584c1100d1190424140c800c03168402850b400d4020038001d0300c0102005414403020171000b00c01d2186400030f0000800445d1640301b1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 78292411 1250 78291161 78291173
    0x201051903021803030c1b010203070b09010608010b0a08030a051308031602031608070b07030311031306060509070813170a08010f0806160305062b0506011e03080f13080a 75
    0x104aa103500c00d0384180540203002c84000341e00e4031000c0b247c031006e480301f480301e20050389107001d80701005002000500421032041d005603c0581110710300c0f80284103000303100040c408401a035015040369500100421035401d0b014800038a501e0301e5080d150380c5003e503120700c1181150020320f043d04c25500202c04ca002545010070907050051504034500c242285003000c401d9484c40644201020f002c00402c1a4041c14081d43c000317280000c02d401d6481e5245030100143c0350070b1242103000c464541c500000800c4909122010520035400c3d511140011740728040880301c400c02d0f0744c0088031000000004e0321a01030809016250528054035043c1082d418100c200c1c210142d0740e040504240c0c088030030491040d203030a001c4e5022849a080c0001d45d61078900104802d100701c030a2076180c40c0100440b1582c1c110800c18070202c02c0b40a8015101c86988641403407c011341228500044403003440d10500100d000d0343d000384808000390b10802c0c80e1040340702c080c9141c00032a40c40810180c000e69101c40a1043d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 78293661 1250 78292411 78292447
    0xa0602060f060a0518100302090f010e070e0904140708071e0b0702012a050715180303020c01050a020717071a03040b07030b010509040f05150a030b06040207020105190302 75
    0x5803c846840b15036003880040303000b0f060200a11001c100072000410012075070740909001843d0080c04200e1186008441d003203426500b072081d010b02019110019040d03604c144051408550b0080c0303e0f040c1c42d1150384648030480440802d00c4a24000c1010000e210f03001004150004c003c800c107511701d452001600c10100b40c03103d5106250000c0c0402013100180c4e8481107614146802000a104000d0079000d180e403804102000102607100703003180850048001c451010414082d5904d03c01c200f03011076080d09410042d440010b02680c00504802000d601440192464041070b01c1150900c9544501011044d051494510299001403005201040b0700685404440c030102d5240307071841c200759039070b45038480d001480b40301010382d100d5401c9126880340701154103e003c02002030102c14514100040146015a0b050915402201d0900243e0400c500c071101201e0704241c00000e690359500c180400f03035006910880c100303c02008045540341c01c0080900800c4400c0e0b40058031201c54075440800c1c0c2c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 78294911 1250 78293661 78293671
    0xf0c02010e0106050102071a030903070609060902040b030a0b04080c03090a0308072a0504020a090909030914030c03060406020d180309060f09030b06040f2910030908030a0902010e0a0602060f 84
    0x242091070305000d00c282c2e0003400d00c21580f030700018684d64ae458a054030705500840c030b40100303140e04010700341e010f105082c0c0054140600840302008003401010800d6601c916002e4010042c8841c080001c010546201c05800c0381c2c01d00105880c540070380700c40041c1c8907040c6500116008000843e01505210848000d4110741c00c2301e0700101c0307940c00c16560898035500705214481c070840d00050381c11011842000850000c0014480604c0500c1440c80c0c0580000190300030090491030b04005519540350020b801c2503401c001402401c0c00b07031625100d02001c0d40c012012520526112801014840d56148103451101c0c0260344020385981000d00c020f1604603200740d800100042c10401b131002c40c1d00303500500e4110000b150009000300081c0c1c0c95402601101c80101c1c00218040340301d0300c0e1138908000440c603000080341c4042c4010340c103030700c01d40844000c48005000c0103030500002d14589807a5210b04003450050500c1000c00380100000b075400711460b0007036001a040a824007081040c10281d1603000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 78296161 1250 78294911 78294913
    0x501060909050a0b152101140a0e0f01020f07060f11030403020304030b010e06060a0c0201090f08010c030e0607051909030f20010c021f09080a030e10030903020703020d060f0c02010e0106050102 85
    0x4102c03088001411000703602c00b44aa4001e8007802c1d00480c1c0d44c25031040c0d2340aa13004900000d586003d1a001c801021010842c031580d004000e401c01600a061003210400300349544594240445601d400b402004461060100c0035030316015011510401005148101d00c00c0e4002d60b90f40b421890612007802040c0c0c01500c2443d01c00d402c0c480d0640c1e8140c15a80072409614188694032002d0004980c1e200d120b0b4400e80e030441448801103800034041d085600c80d1542a20140702d19596074403190368512084030341000041c400d00c0719121041c0342e5901644944c0302c5107428080d250301c9443d030690304045201c00700c0d46130700410305405501d0302c9020907e20340308090a0070b407945545034001c100780e100c030301d40c0c02d507451030143d4044900d007800350b00c00c48040d00032071084070020181498040c6c40c0a5481e12514402c6001400e014001c510034010341c000650b2590292004d90b24540c288980c2003d528012682c807a101c0520110180c030710b2007890480c85541d800401e030300b2182c00490742143ca01c2e800040c11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 78297411 1250 78296161 78296191
    0x190305060303040306110d050403020304090605090f012c0708070f0804050a03050c19050307030201110310140402070812060a091a0909030f03090d0306090c08070c0501060909050a0b 80
    0x1d503000300070340303040325002a40801c0d07606001a00000c10312a042440515500c0d004c1030106050340000a08280d0b60105400c100b86038403036040000036002180c071950700d800c6400050103882c3c800500b0300904251300c0013030400c2c2403511f4440003590f10211541c0300080c110700d0400c4442070b03101e291000d803180f16040028203410700351241a2600780b004e4025080c024005000049154100002d91800101e0b040501030061503191464403035001c118150015820700c0c140c0d4001c0c04040c02200e00606003121121007080c034001003d43d400c00c0e40c056190388950300380544000f294100004010001c8101665801c51402c8410414070640703030f4001911139840c014680031002840c96100040c4801101c4102c0b160342c5001d011882e51040030305c040c2c0d21810120600500b084001801c03050a4519207003030152984074501102100c80501a00c40090244008a12005e018090040c95a4010300002c0b641685600448055962a142c221070903802392500c00203001a54020359002440707940c480c61 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 78298661 1250 78297411 78297421
    0x70e0a050f06011b030212070303090b0f090703260309060f09061003060b06070804080f0d03090305031f4217090106091b021c1220070602190305 64
    0x3e04d0303242c006802000400d0300407030000d06008111800003190400030a50341e404244c03a006001d45000b0000303c83c542c0300c0201207010f003d081940c4510803420710780100481880c42d00c4801c4440c01e80d180710b1340504000a201900c2a8a09000b907118102c02d60041c4698104251041c001c210018001c03003003508620140a10a40b419411800f140c0c0c210700d0204070104104002841c91040c000018884100000c0020b86420040350303004884500310306981c1a401c907404c09900751a400800200024010000284903015404180fa85001001100007000361a2203009030201000008203c07141c103000445031090404d80258a60515040c144681072032510348060100800320f02c0012160101500007241c880c404d502a82c001e050101c1c0500c440b07a603955103c0c800128268501300140a1040c50001246550103241d4103130306185c0c0e441140c0b5401d040300d031000b0042d12941402c943c0d2907003041484400a80064107500d4050480140e4034211606600c0d10b42c029908900289420281006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 78299911 1250 78298661 78298667
    0x10605030a0b030316060c08090304060c03050a02010b0a080708010f06080616020f01020304110f010804170306010201060801331a0a030204030f11030f0c031207020111070e0a050f0601 81
    0x241c00c280c440701d0104080c1c039080006070442c051010008080c150800da03500511015030001c420f2450607440e1a01d540e01c5000030a502d92051b40120781c042003001d00c500001130f124000805c0310151904c00007132214003d000280d448442603001204541c0f11000c00d100740c10007840303a101c1b0f100544d03508120b4103181c604002c0d1074240041003040456503c0102460b010300902c2901c1410307215100031580c900d09450954070307a6200c80170080c0100d0100c1221394103540920526401507800c03201d01c040003040f1448000d043d5200802c0f00e411552907010001d40e000c802d00a4100c00991504032200c201c0080303400c0340041c00102c0c01d0f010781c1840e040c001c100034100c001613044883e04000290b80c0e03880701144182e005e0301c0b55500083c203200e2550841d009001601c2076044c0c100801b00c00381c0d4100081041001c0d41d0300a050709043d415080341030300c0c00d0240c0e240b500030301d503403803040c10324802c20120819200c0c01c00744180e002e5407803521600700708407900400344100b55102d492800b1410007030900340002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 78301161 1250 78299911 78299917
    0x902060c100f0612111909020301060f1b020d1103030409060509070306030f03050906190e01080a05061804060f2d0501121506080d020f010f05040809090a0204120c061106010605 78
    0x542022000c0c0589052070b00c4050314176103c1091b421041d508540e440b00504001d6200b4811074000a0842444490042c814000207000c80e1684c0340400840e06503030204041061100c004440f405a0b502d9030301d0741d540303060007d0001800e0840340003401e14981400d0041941c0d00415000406203001e40500002c1e56a0031020f144a80500e13240761620381040c04100240b1500307016040704200d504100d01c0c025409411400420002c3e680c5070401d840c1c0c00c0300342003610020f9034100d9021100e000840100c0300003c031320302d500c0b500030200400c800d0760820244c41194003494000703020401213001a400c00400c00081800542070400803c0a0b6142402c040f50301d2880001c002e1a20f00160140c6910030075a40000e03020345000d40a407940c049554030301954420030342142481c20350804038500440000d51007680d108981180307450b483c00b5000e01c100b0119150040c41003d4555003807001090303a12110082104075841240500d002c01d04008003d450070034541c0200c1029845800180003040d4031100f5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 78302411 1250 78301161 78301163
    0x1201060f08060702030a0f090b040b040302030d03090206040b090402090a030c03020a1e0608040203010f05010801050a0e0c06090409030917030d0f0524030a1a0618070c030804060902060c100f0612 86
    0x160625040c51305085400c420709270702060350050b0104020075803c25010041c000c0b6071003201101c1c84c0042c1e034038064041d20301940c00658010400e0208010240305000240400c041c020001441d00172124001031060503280c0065500c038180580603c1141400d602127800390216007006d04240c0910614030300e0007400360042000300152100450110f44094002c003000c411600000d01c450760711681214000c12040b1051000e8900346120707405403800102ea40885140c02403c8149000d003808140800703001848000c600f008085200003c040300c0c514a124036086295001c0e44e500c02d0544410300030386404c0030b25180420700d04414400e0303400780003100d034444180c281d21802e42c0c5c52920000904000c480e81018018006603c0783c2c211103851040d0b128428102103410712414030505140e5031081c2412a11000420205412680402d00840c0307040d0303101d48100e8001c10440115408035200e41c00000d003030344041d4004038450000014a0088500d554a0300400b001040d00e45140304145145400c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 78303661 1250 78302411 78302417
    0x60e09061303090e1f06110c0f010c020303030903030a11090306060f0102030408030a0503010305070b0304020604090b0604090f0e0705040e0703080c03090a0605040e0a051312020c1201060f08060702030a 89
    0x5408001c02d0b0040034a80000c015000c1482410316043c0003020f041e1045012074180722011900100300503020b519040380f100c4130303c0c0082c00001c000d80c0500142c111503441860510048440d00401a42c041000b14418030040c030145031682404240c23801a40c5d0300101c01e1480607002c0c0983c0340c80d0748002840e1a4006021910785030030a4020b00141d08501c10303a00311a0640c00002503088205410100a6040703921071400c59103140c0d95400c103003901740401d40d0002d501035810482002078003401e40102da82030800410141c94965a156020100c0b00c00c0b10041321803c0e00c4100b0340420641c2070108500510065030180411105c1c0a0165150744690000515242020a6242416104105645820070050410352003240c0302c1e040a416500244122101080507038005180d002031401600e028075041d004405c4100843e0b07a030f40c242c0f0343c291908101180b040c98030b103c685548403410610404031003c000107081e401c18042903030900726074000d0a000e52121003030111050340001110321444480c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 78304911 1250 78303661 78303691
    0xa0605090708130b0a0e070503030c07151205010905060f0301110316120c020a05061605041202040f0f02030109061a0a0f090f03060f0f1a0f0a05090a020c01060e0906 73
    0x1010950300916030000941381121050810110115562009040002c0401140e030880c0c0d4400406907a0f00c03401c4ea55907203a801010701007180104200391010f00b10a1030034071201104008000f1b2044503400d03400303068803640701d00500c002401c00110106030640154002e210b940c02c03040e442040c41c84054240c40e6601c4060015042641c0302c1c0141d1507030100c0d00d0030f05100340e103c114002075907490248000d54076401200046540b0418076800381042644945a1038101072405152601d0081030020503038100340c949403141c015895500c42e4030700c0072248050058aa5050440e145d00b1541290030864120f52080c1000c0c04c070020760b03c19916680368138a4041c00120032910210b441100f6503000700c1d404282c0300004010860302e600b01c0f080f40520000c00304005000c0348940806d403204080c41000400122000c2c03085810501c01e5040403520203804c18414a036684007180c03808404440100791254085140c0d645140b003802403d00030407030a5513007002410800b01c42c0d2b4a0700000b8010001d02c000c55 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 78306161 1250 78304911 78304921
    0xd03080a1d0f010e030a02060103030e0402040e0a0603030e01090515071b1d06010822080c120711030703030801090203060a03140d031506020a03110c03010e0d080a0605090708 77
    0x603421948000300395001e11003034141440c4400340e842c44401c100741e1565081001044660788000300399000903980d40e0042c0800d910310f840551314840030074070f2146c10680030000882c00e90003041c00680556014180018424035500700145800c10200419041201c501e0702000943e48030740501c0301526161780015990f01c1c0074609508184030040c400b14454410740b000080d001d0740100080800b00000901d16150366403640111f03420320003103c110403c0c0748101001001020003a83c112407007071080f110385144c07039042b03250740e85807428807100c2c0c0030f28680c0010a5410424216404540d425054008110035411903402a0035240c05000d4040d60356400f0001482c1c680e10191094010b41c1c101d41d400c0c90340640c00d404551500074500c003250100e8200010f1103400019484202c08072402c6c0c3e4050035090119941c02c81d0461000c060410061045100044440d0740a10468003400c88040c000e0058110410700640784120003442c2d00d41d41c07440d01c0b50420494640003441c1e42c5c4013480345400b407055914 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 78307411 1250 78306161 78306181
    0x312090b0c0c0910030f0309090f050103030503180109050106080706090e07020a020d080904020d06380c01230916051f051b010209011101020906071403040b0f0406080a02090d0308 79
    0x80717601c0500807200030343c404410b06400000e680140c800e05601071181081221290003600c800307210040c0059010000540c162101140070380c610300740e213400031420019503180c071030a403011030304520155008510100007080e0450307401307001404840300380701c010310b88440d0282d2655940c00c0302074004c5d1564907a800800050408581511b90028003c54480e003240d007261006018070700800c0040604d00c01d0b03064602031040c0b903003000081280495524540c0702d03103a00059400c100007603081c6648509030f0040c0140301906c4d00c88100e000e0b441c000d0b01e82c900200014070740304500d01c2203916028040018401c83e2103080031840c811885034003a001c00c842ca004100c900e807188032a012a0030703046914032075032800c0c1900100002070003642c1d170031143d90108002500302d00c140b2140c60360209003041100c2c00500d2010341034400b0749602080c0c80c01c00c1d59401c9440030640c400c0200341810300300010140010350b0010105a000500c004046043c80081c80104450021901014043c400120000744e61185 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 78308661 1250 78307411 78307441
    0xb0405100f09020112050f06040e030708040902090a050d0c05061c0203040f0203060a060f0e1503031201150801060507030806040e0d090801050c070f1104090c0312090b0c0c09 77
    0x56200104241140300c0c103400e00900360158201e0000302d440c003208030000214002da900594010f20300d091223441c0d00007088001d2408401003400c81c0010700c40c40000c00c0d6000003034001020189809070351020501d040048581c10354005520480485d1410004202d000e5215800d5580036501d01d80d40300c102800840812002d20481020342d4000403c000401c14000032a481c4288250100c0d036076a00d84448840654a15024a450b036046615042100360500702c0b403a9001400300014a050564680100b403d42c0d00450029480c1d41483d00104a80c0021038800c101c030000301e14020701e4035410010700404520034031038064200003107000812010740c0d031513100c43c0c210b68041c012a01c1c05400014081d201d81e05a1040c4da00f2546030a002402d0b200001088414141e030040c09420041ca00d56100d00400034010020794003d0b40c1c4601d400d0008000c5216640994020381016500402928000706944917a411150540100b0310496140003030000303001144490071100c448059a54903000381c5104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 78309911 1250 78308661 78308683
    0xe040609061502100b0312090609032b0c0b0a02090312130602150403020d14090901030809030c121b030a0506011e1e05060a0c020a030302010b13180b0405 68
    0x380740603400203000c0345003420036448040980a0703446007403040d103030130f011103020024141d0160010140446134085041c0213118210004003820705002104002c41d14003c04080e02d49125110840301c180c2c15490201e441858044038601210031a215640b06008030300701403c5800085e40100708800165424003542e000d4a42092440391a034142140c0025022014071690780903018100b03e800501f484100201d20480c5c242d0006d2441c0f0301c001808643c050200c05c2020000c00b07083c01381c01365aa440c004100e009500520481d901c1d945260105810545208100f0307212707095020482c42d110f00c0104190b100040803d101c08041c4001070302181c2011616000101640a42000456162080c949110141e0500400600c00c1c0b0f1b160f454028607400011601c50454401c84c0e002c02c80f5203450001450895041d14201c401d4110383d03130200c3d10115440c0c000b200941d44031001c40069051140801d1007200c5a03250070701800c445070801c50008658580050000055880000c0070f1100410440d40c03c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 78311161 1250 78309911 78309929
    0x30a0f05040b15190323030d02090f040903080c0307050c15010305010b010906021c090305010e0703030e06090f060a03021207020703031b030e100306121b08030304120e0406 76
    0x140c602460040e00300c2a04941c010000300301010030f80c00f281006030101408101600f407202070541151030300c01d500704201440f00c800c141d501c801c0030100c1d42c0070700207071441d80418903003d0703182c04e6050104403190301e100f81c1d140d000d9440d10140c2301c042a0710442c1290003c1e0410800f9560b521280300840c1c5030b03c0f13020b004c49014800ca00c805191031441c11081c50403640140020040801013100440d103c02a604c070303c03001a4005241f020f0200c60160000d01d0340d1825042c002e003100d0756607446509450b1028001e019035082520708209260700001e900764100070480d500c0346032580040004003c0b40070301c580a4001c01d0301090410240e03011b03a048a03803450115259031b03810714119000a5591307926000880000303202000e4a20720041000d00310401d1540342c0c484034181040f04050004004844000c4c0d010952640300c005050802c6900e075000c4c280c01100c20780d00c58540c00e9445140212580d000e490103a00400070000403c0003d0960903407400f161500440c07038564000040d010307200302e400545031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 78312411 1250 78311161 78311171
    0x1e071809150503011b051b0c0d030302180303091810050d0b010602010b0d08030f06010215010611062520150a1a0f0d020103060305011b09120206040b030a0f 69
    0x200d2038081001040316800c40c02482680210558403004205c01d0b01e214006c0b0300c041c000141ca0101c03001e0700008102ca41011102442d00e240e00180041121403000d4020907030000d940c00c40d018050f200714101c082c090b03008603d090307604000304200300040341c188010504140d0105031201000c040700001024001c20300903480c2d0060600e074424080c203114050156190501c04582c03801c01225103000507410405090843d03603020070b10240a10b00500041c114080c8507850744813803c0c4000310364043c00070396072014094074000c842241f80c1840030345102010080c0f038256018420014480c058001c1c0303546000984c184000c00c000403029001d041c1140180218050b03044600407441c0064440c4049010501026500541070302c034032140800030310f80120082008007041d00382901248e00d400e1040c540052000e950ba00c0380c0c1c1c2140c995013803005030401d40c0420300c0c2e0000d500c070504001801c4d041550200712030541e030005107075100358070454250450100024000390f019a002c079403000e00d42c16084c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 78313661 1250 78312411 78312431
    0x10509041a10270e0a0b040207050d091403030313060e0708030c0c042702121002040312080106020607170a02040e04050105010302011b0c0306050a020c070b0a081e071809 75
    0x202d00c81c09030405100100b8054560012600c0f050703002c03401c0710002c1d0b2400107136407640401c50026107100c2003d02d4005400f007103000002070ac200310f80b0b40e120090303544211184d800c00d07072844c1300c1a01e400c9100b84641e2040c000e10001901180f80011240e600400c006080491568450b080045680c00030724540004564807541c15030203d036102c00c400d0110390400200501c140c11400f00c0100b10840e00e40205062072800050130104a01e20380101c070310088520546052042009a900031382044941e240c02d4030303081040304c1e00001c0f01ea001d00124000b505083ca401c031402426881c03041da01049490482012401c80c914590484020345040e803082075a038907260410318007a04003848128001a1400103480c40014000c03110100103a0000000c806203255072500000f0f00400f51110181320307803c01c03130400b441c0400c0260000074086108190b4a030000c00388050640640100400000345c288500001d012010305042680700855080044046c2d5090282e0a908142c0360040d42d40c807850820114 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 78314911 1250 78313661 78313667
    0x8030403050106090f09030e2206031a01060806030312150a0305011e1a04020d020c0102070b0117030325170a0213090c080103020d05030904021204060506010e010509041a10 76
    0x192056250140700035014000c880045488600f00500040e4230b10001d00303000d19201403640100540f031580349484445407401102220103660007110745680300004c03860350200c611803560040030a414002c1c03e40c500107000c282c4900c1000c5030340d4125803180c1c0015101540030800d03491071020240c0600480d0b5220f1504074001d07c6022201c0d00030b0040d4031405034140585000c0c501d499820078554101319441003007400040e410401d540c50400d6020300c46031480350310034030142403041d014000a80c41945001015903080084050014082d0030410800249200711009261001c8035011aa40681080101101c030340c0c01c211000504c2511b81c0080c0042e0f0b648640141c00c0007000030070206e00075603030741e540d45c41103a007445002e0020032546001000076180c10518448a00c0c014800d40b0316003041c802c00141264445440c5164070502a0b0078007082c001984500c680c00384082c01d04007075040700b550002e0414050b0201032031081d91660210391054130031000c004071410001d4202d0428000058003d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 78316161 1250 78314911 78314921
    0x15020f030f07020f0916120f0207031e05040807050603090a02181e09060711031903150503030c0714010306210201020d180302040216050d08090d03020f0d0510080304030501 76
    0x1684155807000005010b0302e01702e02254066601419141151702d4000d8044d00e4603404003032401e1000d959000040c0701d0003418001069501d00c2507580c41d950003040d078681951504400700040c20001d062005201c407100000f407040558004443c0240c9076602c00c88420301d440e99100c070080d0050300e0b00c0f005103e988040d44005024054529003021804000703140103460120448030742d1402e90002000c54140d034042d801c0c031802d00c0085c0341a0780c5099804003500d5400400444047c0001e035407000d40500912241c1440b1000d0001100954609103007a07181554842076400391122810045407c0c00c5039031b0196008400404107900546100036048c01c47c004d0903c0e50440c141e0142c05142c03840a5001c4c03080c00004090316003114110000ba0441d02448001d41101d10090b00d001408030405004c50003c115503200114942d59446607445c3c0302ca01e4601344000b9261407004d141c0188000140810410240d40107002004000115a503940154029030221640400c00c0c50000142c0801404019046 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 78317411 1250 78316161 78316163
    0x230607020706020c010203090405040804050d030504090b0105090f0f06090409030e04111216020307080408012c0d050304060207020616030e03120d0f060b0315040b030601030b0115020f030f07 84
    0xd45290941e00c075020313a11103002d4038516006800c00c0001100600d0150b0000340c02900403103a144c03c05450b0f4001c2008684580304c16400300f200401c04016107100c6010754a0300480a180c418208403144001c6a51803040f019418440c10000401e0240740e180c44082d281c5040300144244849030003805c0c060060300c4010716440c0198240a16141c146100c4c500315149609035400d66001030390f902c2042140c8210400301c401c1140020000b81c2e011500341009000940701d26000021031a542c1c01c039401d05101119042a480141d9505c000e0410a01290b20611703259181072981e5603964a180050080c8600715000f58000320108080c90100e5420944114142c482e482d60228002508101581d84400c0b0044c1c1a080b4020440890162403a41103140c64200c1c204000c035440342c4a80300c1490ba90011588400c1d18084260f100f0803038036240c0504600000242c024011650540c0c07281059040c0502901d0b00001c000c09401c9010761003000180c5800820302e06481d11110048041081a401200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 78318661 1250 78317411 78317413
    0x30801150e15180402091c030212041d091204140f030d0302031009020702130903181e06090e06270f1501020c09070305090109021507030305010e1003060923060702 72
    0xa2483c0346042504c01c8031840c0000a0081c200003c41521103185490818800c601318000c07031011000b00b51121024001814070182e407408402c40d8410041031508000346400c9d203e5200041090100e040d81d012034003602c10440b0107000103c10400841d8074082220301094040c451401d4003c01c6981c19070156018600c01d101c82984640e503100d29106a02840d40c004c0d50061200390401004803199114840d142e00c21b0400ba0f40b105c0030090110300ca208a039200c2c40405020f0348034002001d41c0d58003030038040c18150074002c030484d09081500c21000401095036019004140b4006030b5900d1800c526008030500000e0103481d0300c1c0c10340d07028000802c25501100b107005d14202e44103042d8004070341106404c0d8050b0100c0056550040224094030010b0304884155681e00b44c040d015032100300030381e4003400c12140708960b02e00e2249001012034005038000307100c0028020520407500c94549070700b02226081000481d02c218941415464103140494000340001e03102e403031140e0454003040c1a403186074290 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 78319911 1250 78318661 78318697
    0x14090d0c080f0a120c0f02030f07140307030308010b030a020f0c0f010605011b030c11030d030b180103030801030321020301060c0501060501140708250812070903030801150e15 77
    0x1c400c0c0e511083c48100916091080110540e072520401c0481c510324010b1340e9002101102e0340109042100701c400381c40c003640141006000c0c02e0b801d070000000304401035000700f800c1861a10014501103060041c0e100f08440000459041140c940641d80110310442d031a80ea1810305681142e944d41c0c402040480550800100280540c0150a10340300030075500001707117400309203075821601542035901c2201d46040c0c0030410301c1c46460401620144298540f000910700e40d41d0410040020001001c40011074601c3c0b00600000f41c1c0701c002181100d41c18140403044401d510444088080c02e0015062418404400040c02c01d900100d40f0b132803940500d00802050340c4030001165600c190a1406880010400c04030b40001d4062001f0072101b107405040034070410031105180d02e28aa0743e102a280ea80d408140c40380d010700c80e1001150445c40c0e07030500000301445c50341c02405c0c0c207034144944207280c1d000b0480d119a05005071130070581c0c00f6000300300903c001c84542c1140c0072904010304403031030841c0c40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 78321161 1250 78319911 78319933
    0x801060305010b09010f1709070303030b030706050913090b0f06040c020105090d0f05070c120203330603010914011d06040809060309070905100504050702010510050114090d0c08 78
    0x2440707158140c51411803050325014099005603424040741c1c441c40c08120720818511481120b5003815401004040050031030b0311b1035400c00505645109683c41e100740c006000420044d50400d085035400c0c00c065a061007964008203030a80180503000c4003405140c648400c200070b018000106a200b00800c80e0104001c00d80c4403400c0742211011108190203601c080c210701c6d04a0300441600e0706841040c9485485d0820ba030b542c03558040083e038041e820030b00d645490581149414040500f0340a000510010744d000603d4602d00041c14020324840600311100200703065450a4224504190304100b000007682c0130225014000c00a40038843d0250039210000309036064007203040e900803a000024542854400420003c46502c042c001c1546846481c0d40007880707140781e02480d4802d5140c6408800340d10301d05414001074910040140e41164501070170801c021444040c1041036803807c0c645100e0320f031030381890741009125000159500120042424041000710300c1c0040c1501c03401419588802c0003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 78322411 1250 78321161 78321167
    0x30712140417040f0905060f010513060c0f02030d080f01080a0b0c0d0b12030901080106210902010504080a20010906080705031902070f20030a11060702060415080106 73
    0x10031800c032108040580116000c50303104888070721900070001030240340070340c2c602100b00810000c0d403100c001161102c3c20000e0b02d01d000881c007043c0c41c0007800d090780303000404103d0071012803c40c0510000c4c00742c1340b4165000d0009440341d161a150303000d0f045640c94980c4d5440644522011121000c50301c00300c0d8004110294081103098801d030340100c0400b041d44035441071090940082c94500009030340ca22507120199950b0079610319594004000d140d0f01d003100c1000414505050b007010045c4004100c10302800088e101e00c1c520200110000081d00d4081d03480100ca4511903948406901d1113110413060074031165046990f040c0205c2d10406214089100064440e104144074440209020000007083c0d00c1c02980111360022180321408400344c02403200314102c0e041802d095603c0c14000342d40c08100501008002e92449008404500791510500001d595800300f40006000000030820445940c4440c003e58032036030340c0240000d0329940c542c3c3c0c0200c4001c81a00f054000500751030000031314580 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 78323661 1250 78322411 78322421
    0xa030303151505070809040e060c07140d0903030f030b100e0901050f0d02330c0607020105011404090c0315020c1e0606040e100f020c010b01030e07060807050c0d0203030712 76
    0x1c140c3c40701820840a5100ca0805400c030700102a042034451000307812100007404041d1080c02400c401c1600c0c1e40a44c20400341c5404c45410400c9503a0107201c1c5011030320742080007442103d61502d0a100c801185d00012405400c40d0f8405941141d0f04648041115401c4012a09028800e880e80400c0c0d030780e201c0c100400004c5041807140c001c1145401d00000d8144503568203408002d40465200b481404d400b00d403860100ac48a0800101012503020001301e41889200e80004052001740125414441000300300d0540800e4148540d650b40d01c110208a441241c00c4015908646903180e901b114803d400c01030b5000d14100032140c0039001815041c0c4440c071008a011180c0c440c010300701c0307603183d02c1844000d119151080360248a0003a070450b0f0071106c0c0c0a07090b1451300380803002d6110b1407400c0f503141c2922136084600c1d0505060000802c0c0b40c20000800c40200d031520b190815490300c1c2c99800791800e100d190804c06050095510f020b801e581c0000c0254002c60140d40e5001180300c003600700c071003120 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 78324911 1250 78323661 78323699
    0x1615261608011a0304080c2a0405040c0b0a111e01150605090906010e060a02070302041d150c130303020a0b0109021603080601020313080a1203150618050a03030315 72
    0x1030220f5104401d0494040142d030f88a8810790340c480c0f405a80059803032501d0003140c0e46003001422040040c200e40d010000c40c107212001aa0700f1700c6542000d50f00e030103900c401401103a180d0000810920440e612900c04c0c244110300c03980903140980060515030028000302e10a818203503080c041c5444440400e00070140881c0d260b99219410300304141c080010803500a041c8c82d041112469481d4115a40c3d100140640f540540080100510354814030050720104500900b0100c013018610340803c0340462109540480350f06000a03594804108008074080d094901303010b0384840da0003004068002a41a841d01e0080001c1801aa40c842e003d109a126036041200b2861200d491000024040e03042030381c106905006580c1411111445501c54000d65030180b0f4156102040003014855062490f00548a40e0314051081032904002c10031240046e100b004204841c1b0302c82c1c0f04002c905540208040e000c004c0c00f170b0252550364280100030b403000b010312005803030022000190b9207140111414041d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 78326161 1250 78324911 78324929
    0x60f03151a0a410901090b060901030207020307031e062a05090102011e0b0901091505011112030c0c06070207051509040207050a050307050f161526160801 68
    0x1640c1807485501d40c82024000b442d120b043c030116144030060200010042520303c11060b411407555001c10070140c8501a03000d00015490220040180c0c1c4804040b0742040d1820b080141c1d99401d00d10100c1e1030b00242e64800751100c2c224050585650b030101d036003000100c2c09641c00380112074500e0100d8415041e40c280ca814011502142540d02d01d020300041c02800b001400009082c1c44841c00411808a0a600038440c09903590ba594a0074544001d08038094a1996000c000380328080316000002e140c10300666051007950030310012407080410480109010026180b80c803130a1484041c142c68000e2140c2c3d02c4c45024500000e10ba0610010382003044410083c43c02c51700240301e031007103a11075101c00e003e540c0058082200c00c001c40c1c2e0030801801464812070055549003001e080103420414860760100765500002090780c1000c4104d007030035040e45c030030781050824599050310590b6a070800060201178400303500d8106043d504010b8020348106044440c11031401c0201d40201c4401340c0174090300500c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 78327411 1250 78326161 78326179
    0x1401020d0c05010f091202010f05151908011401030201081e040602032d0a0605190905070e03150405100c140702010c020307090b13060503030307030b04060f03151a 72
    0x300510840c9001c0200b8003610002038851039110940056600050069402890003001046034503424403500040d0074054800b0441810b000002c00080352150400c82e1080c501e200c0048080404d030007506c4000d01e00900204104258041e0000d24039500340300590210b046400022030f100030307140b2440708603020070f1505082981c4075950003000750005011003e074050600258002014811360400e198001510340f19001d00c1c0071032400081e00d206810240c00f401c0310b071019419541c0d03d1a08007095804001c40403899a9900c00101d80070455925407a501d8882c1e038802e02c000d412010380e0781e40198064810350340c0b02d4034100c0142080e00d00c1c0c881a00001020813180a1100c500ba00140003182e10515000c0040d911580000e4507040303d40e002941020350f100030031982440c1c1040000710040c40c0c0c603420700a461070140080d40300c0c00b000701854145a21a01c0da43c3c12941c0300d601c810085c0000c034111342540b58803400d1680e81080d87e5621a001e03030340303410100f0211000c522140b0708001c1c0001c1c01d00d43c3c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 78328661 1250 78327411 78327433
    0xc0305220c0819050613030c08030c070c0b0a09080115031113060803120a1b03051e0a0b040506030c090402060a300c111e0a020913020109140102 64
    0x140003000084166988072500d400401c0082e014444984411814112124402c80609065081601c0070746450308541518200307000003078208100450403500a410130303840e0387d0789007005140e92241e21700042c10016501c001181c9424604081d205d40354150707039000540c41e26408220301300d5002284030a01c0207402d002c01c02c0007407902141700441e2034016000404c0507030030487c41015610f454204008a4001040071900404000500781d445118041c09201d054114104404052100c0803568101500d800004101204042222503610800031400a1500c0c02c84000030007810000500c920450505010401500c0d00084017010b8182c02445c020158a8641c20010203070702018814044c402c9491400381d59840c0800301150340b0010101c0700b00c0f1340c146c0c400c503a02240e17030b611101c10a1007102000700d600b14000085840701446503036030603014103210803042d5180203400b0328000e60000124041012407407a07000c80c0480036100b82c0740c1e914440e0712038000c912420000301c58280140e02c4003034144 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 78329911 1250 78328661 78328711
    0x6021b06060603012304020d060e1018111b1f060f0e040203100203071707050a1d03030c10150b04030807020f0103140906070906020706020a06021e040609090c0305 72
    0xc910501d1641c0c5c91824801d010081016604051040c13800307182d940750200540d80078203c01c96480710b614240e4244040c205140e4888510342c52600988182da180c5120302510214012140d03940e40c2d2a81401c82c00c0f42d518000c40d076802201c1048602900210f510441c19102809100c00f41c40c80444544401030904962104a03030740180141e90500c203441c0300e1241a0400c1c130055015070300d543d541ca0450054202c000741c0541c3c1c040d16940c10000b0420000c1460f03544171000c609481c02d034058001c031040b51100004c3c51802955040c3c425405180030405400e1301513840303158543c0c60b0741006000c9542d140560722a9008520001c3c00080003000810014901260280008541410700007801c1d000780c0400400078104464180243d0701c01000d000060380c000d07410400501c26440106a02402e085000b500e178196982c0c000c000c03640102d21100410b10308140d00b0f09035020801060f8450399a210014503885070f0748191901c031480d0000420600e4440d00a40c0d04c6045591160780b00320f60044010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 78331161 1250 78329911 78329939
    0x30304090b0102010212040b040506060603040b130c050a0b030a0b03240703060e07050a0e09010501140c1509030d060815150a05040204090c0e040c080c0307050d0906021b0606060301 80
    0x802d0440d582044010b000c800c05240d03550086000c0c21071403d103440c00f882e01500d04400030f040c8034854102402000002040380d840c403275129220300100c1c19154004e00d08022035207507a40040d513000655203004285103818001540c81a04440d20612900d2501d0040c50b4503011051541e220030440842e10760f8032010b0003460b06400038594600007404c260f8896911610308130580d100c0700050000035444280b40ea03c801c2d40d03000090201e48405555140c8400602211080a10a4018180070035414900b00003131104194091801c0c1c0c48c1545480e10b000e0103900c9130300c00303150401454944800498481c0c0f0001b140a0b05030301d03500c4121030948500b5550103074407101d8410a64000083c00002c600c5440f6400a0070003418100c601045a00c0d00800240c000b04159860704d0065141030402a5255842400c29400c1a04564407603a203440c2c00398100d40920811003c10005401c1090000402009500400d203c4940b52002c194002c06050142c0d1603a034140c80c0c0903480002400107201c2c0380d80345246 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 78332411 1250 78331161 78331181
    0x20c190b0c13050612010303020c040510151107030c170a080a031805011b140315010c140d0203030a060611060105040b010203271005040b030a020702010c0213060602160503030409 79
    0xc2c01111564400c00140f460740000d03605d4594003d0400104205a010881060400e504803000e0040323140c0305012400c8100e0a05c94281204002c005420750240104070b598402c0c429a4181d0321403e840e400c0c0752123505a03034030812561030800303250030b45481000b0410ba5006039011800910b4040110800c4020345854031000095141c07090380480022400d102c0c60b08412031358480031421000e480d4010b07100c940d50000c0d03c0704c050380410400c00102c02e00d200d1450420300c00d0030440c000d1210f9081040340201c54494606403403080250045020b60000007951062241f2a410b0000030303110581100e4043d141c0e160f42d00207611510040c4940c0ca003c2d0006030603040306104480c00d2600c062607015084401164204100c1913486401070300f800c0032400600182098104a07141516100c403001603480001c020300c0116070b0114001c811680326440684104c3d4009242d0194244088114402801c0a105a03409445000310050461040441c0361003211030040c059410145400410700c090001486 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 78333661 1250 78332411 78332437
    0x1401050108010b071221090b091b0604031511030408030412050a020607080910020414030c01020111030a090204090204020d0212070e010f0305100b0301030c1e0506043501020c190b0c 80
    0x4401001b0b1090f40c450003046034000e182403070581c03d00c800032500300b9000362240200f80405003910031194407039500312412298072030844070a6006400003000100951029502801000024081400f005d28003442c0214050044211201241c020030b54082c4200240d00d03000d0703000280000d520034002d090707059008038130038182c40184120f0410002264000d400410b5490aa140d000c0d4440c2010801c10b18826000e00007007040c03029500314188680030003403410015641360311825003151900d8101c500150703805041035485000580d9050f000c1d400404125002440480000d05030601c250042540c180741030b11040605201c0f04405c8024043c0140f0790076030381034005000580008814000c1d030003140900032040c00707030341000701d411541d01700341c0c039035400d40031802d1028001d940c1d51608680407289890409402017008a440c15502045020504481e40d20f8101c1e0b08030408040d00181404d60032141560b07541034842e080100c01505002c0c0260050211000041c440c04800000b0010360038201d0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 78334911 1250 78333661 78333707
    0x50d1704060509011104090c120e12070c12030f0e030c0105030a02130e010e18010e030a120b030a080903011107050d030b120307060f050a02091302090d02041401050108010b0712 78
    0x49281c5150750b001da4030000d180c50b40c8000308141d56500a1480e62049c85281d400d01003071a9940016a07134480004004c07980c51400030b040701c00c00c031190900030f0040c641011230000200e0981806416043c0d03210031000490b0720121959500c2c40c010a0403010200146c40c0d10341951200c3c10898001e4000f441100d154860040010842071003e00540b402048543e14455292810083c8001c003d190020310300050381c10254150251030021003510200c00851806004844640c101c5a014148002c0041d800d1701a500c500024410300100030516450294028407180e04458a07180251049030800f4080b600140500702030f04e40b180e0083c03068250000d00907441038440c803403220305691264404841d480d550304c0c8080003880c1c2c2c1c1c0c0956a400149481c3c1182041540c00c042102111620700c809807096002501c82000e40d81c5001c00c5803a141c000d0b0081041569007400c04a0341c07c0c2c00e000301d5010610030000000c4100400c01210320442c0d004105030614440d080c0140c82c100d00480307a4840c104c17188 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 78336161 1250 78334911 78334931
    0x108240712060e04050c0d050a02091306050f060f01020304030302032a0607020a03090f0b070f0501021303051e1911030a060f0504200604030b06030a080a0804050d170406050901 78
    0x19010350000b0309045a040c1d8101c4c1011701c0d05d40d141c02e44540305203005114046080d800303d540444c0d607050389034041d00c12170610f40e0380c25400103000c4140d0380000c103d54030304405e008000483c0342d0107521828054844200d82c40704040103a0340c0707016074840180103900400c020408021030840f01c1501d8100907400c1c080c0811240c045070700701001120464010b80c0b003000350b642810762191050004085101484004509060300b0514910030650302811240045070f1860801c00d0950485050f4030140e003040d41d04903144d02c1d041b519481c0c0400103607550101d012020b45803001c0411001300d10034040c1c2100311121042d0340c0f198508212603d52035814090307003d000020515a00402056820078a40000d661816181c80c1054901960240500c5030140c10700f00d046484030350072101525001b440c50079640c1da811000a02d0301d0100381008240100204001100396045503402c0d00a52140b03040c1c401111820302c08036102c5000300c0407160140c50240c0468041505503121640180720200081808114 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 78337411 1250 78336161 78336197
    0x405010e0d0501020406022410060c050a0506010f08060a14070c110901030602091c15020c1c0305160e03030706090305120f01140f0609090601090905040507060801082407 75
    0x10398003010241c0c016074a5140c8c40d01c80da801004546d1442103041030141001d01107001144194002c000501200d1a810020f201082160942450b40f0804840f810768584d041c06000b40030382d102d039000d00e11402c004a01d00e00c2d0a8082c8004590310361000000641d203401d0222072541c450300c0199072001c007420b21100da546a60111502a5000342c00141c1d1f1000f800092042031003150b83c1c100c2c83c44040520f1200000c100c811003003c404401d101c00f503100c00c3c0f100545810040710001e00080065180740d0007102a03007681003648140c40c0700420004489000c0d00c01c2d162131244019050341500100402c400269050340241c00041c0603261013410078400c0040903042480c207441245001807080c2c0100b15208010384000d0202006980120b908043d00d40451139a020b125006c1d07118410600020343c0030792042d540c100007842e55031024440350030316003031041d02c60485002d880d0005142000101e640500013403a0808500f50380243c00290025203420b0a200401038a00006c00a00d0360590030b1443d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 78338661 1250 78337411 78337417
    0xc02280201180308030f060a060507020a0308180d060b120f060a0c031107140106060201090206071112030a080603060708010501020a0308070909061d130c060806010c0606090504260405010e0d050102 87
    0x801d1b0300030409800c01c2c0342005003030465a4005802c21400700842d80040e241d1304114401c0720382c4a1801074441c2c6028000203582c5a01c0c2070b034260440c0140c8440300502c0500d4111683c107400640d6991600c1000034a01a2940554991511190b0010000c582004215404181d0010f5580360015160008285020145e80107034401c1e9030008000c88640c8008600b032040000503c9140020044a840303580811194000c406000c0c2085040e50721144064640322611107091044005983d90380343d031094003401c0e00d041560280d0280c440d04000440182c018800c0c98143c401c141c0040070803207a181e42c21070b0f03102401400342041008002c00000d1190103806001c2c003a0403030000000212000c1c075122000034000a1440c118201a03a500c040030550b0b09840b0002d440c004c2c41c0071103490340c4442c0140c803090700da6240201084d1928400045071101c4d0760101d4000c510074001003880f160070152005003180c5550540c0d120600070802045258081c1110060040001e0001402951280c4640b801c83e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 78339911 1250 78338661 78338671
    0xe090702060a0515010912170304290106080c0702011e0c050115050f011d15040e0a0e03090103090c08030301080c01090909080322021002010c0228020118030803 71
    0xa400842400718802d82805403550141442c0c1058001d0421440000c041e401184101d4400c115503c0301c0005110480d81e41040b01903001c40495aa810076140c0034042d6144804815441003c042046c41c034911250480d904071a0540d444588540b1140500c0030719503c881c104134144820815600d03001c3c804092504da00024a880d0440e40c1c994606200c1c0c251a101050704000c0080d4203814810340da94505480060301c401c0c6010200e5508080030784030300813560011280c1c45110725554503200c41c8c40100a00903500499051030031500c0d01a008420307504a00e0b26000d040d0020301107071109512940c0035004103806070314442080c43d560240141181c1c002e13040210300e9000a03040000d81d503000390395180240b030500d008000e0003c4c1d81c0c842c8959400007804d944491100d0109284084c0c26501456180c0ca400602440c00c3d00b041e0348000e8002d05418100e040540a1403420403a40542d070b1340300004420002d4240d04010300725600440386241c2d10301200b03182220a0b2000300206080c00c000c2c604c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 78341161 1250 78339911 78339913
    0xb09030a0c03061d0105060a090504080d0218040c031503290c0403050d1404090b061c0c03050a0b13050a020f0310080c0d0302032b09060504020405150102070b09010e090702 76
    0x35625a10400702c40d40d4070321300010016030402c024004140c444050a00c12226608000100c0c1d4846141c804e501d40f1580c00c10501850002c07840c1c580e0500f800005620b404000c850803c408451070f071090f0f007074034441d043c12000c0c1c034182c800030404a02c010110382000d2142c07001501c1c0e00b03c030381d62540e5101d010a0350180c401400110702841008800c1101d8488480c0c24140780e108003140c03011000341c61169000d00b8103516210308015525172a00003c1d18010380c10191900004254860b06000400c0f42a2118000908082c0882c0c0202014411040340000151015100021315200380000d401d000c1d1055100e55401c002c482c18007480c00014601400b20030031081400d501d0480918a0400001c02d0a407095601c03801c62000a0740000c00c90b040709070304201c41c14207036545221403421480f640110091031828204800b04010035075004c0c0d4400c03032080314100070301e4803220903a070002c5400d0252a0301581c4000010300c0188044400341500e4401490280c0b4800018000b181d01c8000680b000805 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 78342411 1250 78341161 78341171
    0x20a080108061803031303031803080403030605060f040902130e280c050d05100e01080c010210020c030306090408130909020418020a05010c05070b0a0e10080601090b09030a0c0306 79
    0xd0204244030300c94021041c1110f0001c0345900c2d010558076440301400003041042031000e00f10426000340c02541c090100f07641d10141070481801e000e004650100e800b100003c2c944100840c40740780c00410b0f170744443c0000040900301400e1034402d000079804400d00040d00c50350880009521941084028480c0205602540301c1c51201e03080d1041540d6606400c2d01701a0a0050039000207911409981195202c00400305007a00c1d8030351a030010703064a402a92030700d15a40f0000c2989000011810740442c003e0707088901d0300000015503401c034016450440312680041000c90024075101200c150018018000d05182c01ca8004041c52014041c0d030000124a449480100c00d501d030a2242460310215a0303101c41c811151640011032100ba9070090f5410f000b00041001d080c000100815005032148102c0d00fa580d402c60000a400d06c00c41811980c440c2a0110100300000d00c594070b01400f03440107850b400c102606014860145800400d011a01071240400300c801055490384131000442c01070304000380d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 78343661 1250 78342411 78342419
    0x3020d26010f0806011202090c030403050702041b0f0e06070825030c0201030f0506030a0204020d090f1b0f06170a02070204090c06030e0106060c0b07030207171c0506031b03070801020a0801 83
    0x208100c0144e00611107011640c11150240e181c0d23042c0143d10103481040282d4998840c0f0303055480d8020400040d400074503001c590b0f02a88140d86030104000c18544400102c0034400c00c040b80d0b007200e00b5074900d4105205100e21070010f07440101505841c034400c1d03c525840341c80aa01100c41100448040d1b001440504040040d540c141c801c0b250a1640e26809000d05d150200100b60754428800d0000d0003554001030b00311350690285d02c0300c840c0c01c2d40b24498124549030b0781452004c1d008100342030341d07500c040d10100040003c03045c00120126201d81c0c4642c40700e400060321514a480000f400c2c1180c040d0200a03000050b9268800d21300018828a290f005c064140364009049491002c1c00e010580c2c0340c40b01c00c0c820950018409100154003101c02d103d507581d5040b0880182c010340e0300050100d0a2000708203454800030001c0c2429107203e445a0388a1560201e40100341c58080e02c420750035411106181c1910841d41c5002d0070010800740407107000c0ea80d5031015508980c00b00000c00000303a01c20300184 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 78344911 1250 78343661 78343663
    0xf0a0b01150e011b082a06010b1309050702030405040f020d06050109080a0605191508010b0307030c1403011512050111071a1305010203010905040210030903020d26010f08 75
    0x40000356092400c281c02c0018180080c00103841c0c000c0d18810040c540d00003c04018107003084984004555400c1d0084d45504132410100091501001c80070b40600000401c00c1956a4184c40b0503000700d0b951600030318034201d070300e00051002824020450008000c00704035901c89008480d140100e858006a0361a8000d0f0314000300e4001c0e80000b410020721050030094a00c0000703449a8140d0440400101903e4000c0d001d26a0107219501241850800c00100e41c1000404111001c03549071030020b00080b50041c0405480d10420b0000500c40b084111003404003d24024611002890180001440050140340d61070954450307403203c101c5031040e07244002000000e014030190002d480c0909810401c15940e0300c00064450011400d4489000000950301074691081c01c1c1c2c0c41b038020000715960350311040000c018100455040c2d001e2510b01644111080c0720f480b03002200c54259020704003401c2c00320710072205444003446070145501610364000d04141d000203024000d0001a01d580390300d901e007000c19 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 78346161 1250 78344911 78344939
    0x30f0604050f091c18090606080708010e04060e15040b0907050114040b070f0b0a0c0e030d0c080904060305070e0106260c070204020715060306050603010e03070b0601020f0a0b01 78
    0x7100c0800c02c480c24041800030001e20a14820003c42c4007080b4a000910119414080b0144010301c0b8440c0c1c14002540a02c40da20a07026201f0565800e50300ea580d03541c00784e9280e0028404c61003109410000100401d480e50300416407083c40d5010f490f25100420381d81c1102d00320030790341a10799015603820301030842c0040241000500d801e080c009030303002e82181d0070740460080c0c0c45540d2110b000000c045041040c0c4004020709680e02c9086200d180c01c005003464020f150a80c0c00c42c010805c0150b0710865850b00050855080c80140d0360b40480c0d0155659529168108034450b43d001a214100403002440c117011040250500000c840340c03a43c0f411b4070040118800c1100020810358a04441e02c00807060780d001d523400704d285000315a0f1000c0034030100c4d0080c80350380c0000c1d241c10f00c8038401440480f185c6c1c11003022213015490501032a15071004042c201c0f401c0039018035803a4010001c0740000380102c0a4580c5c01001401a81c0b03120707400d204441d00744440c1724400c0750b006003900014401c041c43c200c40c4c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 78347411 1250 78346161 78346171
    0x60203130f1b15020303160915020304090c110a030309290a050a020304050a0803060d1406060a06020106060e0f060702280911040902360a05040207260d02030f060405 73
    0x84203d216064806501ca20000d00a05d1101c07030000380303c0704140c0c00784440304014410808a800d0b07900c1c1008009440f03422600a90100b1030500b82840315161107082102000441040940b1082c0e0030780e603003a00146560803003100c81d03074550740340300b81c1d0200d01441001860100c2c1c1c050b00c0452070042118002c494000300901c4c0c00d58070510610011450004541c0000da0f44240159940d481d450001810101d04c0c100003042d506444001584003180131907a82c1c0240c00c107039583d000e01600c42c00c003039099031064010100004c0c0014a418402c1c541014544a4080090901c0d4a0458241c0104160f64010411a0a017108503d01501d940c2d01c0b46030940f00920030440308104146111003e1007041c4168820591051707004501000341e04c0e4504480800103869040015501c540d141c3c0c4940180d0352801c4c103c1c0710b001480c1c0006000d0416008442c7d0207640001c0400c1d20301310001403640503164002c02040c1100051000b03050392012440154064210380c6c1140042d8549002040140c440c0206 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 78348661 1250 78347411 78347429
    0x90f050d050d0f0e060316081e06010c0602071203060f0902041a0a12091b08071203050c0f01050103031d04020702030606010e041e0c08010b04030807060203130f1b 72
    0x30010040342000c80c101504540a03d08030a9214040d00111811203800442c1a030010002003803000c0074091242043d805542a26001015a641350444034120600e00c00c0c07600d501480400100c0d1903114510648035284562401418100355440b10000f1030100b644a10200790b6400040c0b21186001880000070710311414154030b0a41800d4291119550008155441220106e0000141d0f03025821451410880b1401084555640d0405042c0e01320000c081e120040d10800000c40c017000081104000d6400704500c41104046980e001c841070303440301000e595a030150080141c941c5800f07019003030086010340d0320f894440c5c110440c2d001d01800601c0c549071040e8070400c18180161004100c070781d0301500c2401c10214004081000c103000d0300e15130131403244501075544071001e00704c05035000d110041c03d075a850311035581e21a4020489403280b0301010300703040c80500001000400d1a002584d00c403032210340030782100700c0640d1226444040000119050134450111040710203444520310700501001d8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 78349911 1250 78348661 78348679
    0xa0b10080f03090103090804050303030901050414030403050c0d0503070c090c14030f0f0a02210906090f070317040b030a020703080903091305060409050d230f030109020a03060b0a090f05 82
    0x880c20560342d01ca44500513040c1511002c010307091001c190290b138010500501543e82c1d0f407400c4a0058024041254201e41c44480c040f185010b080d400802c2d90b00340d81d480303402064020110003c0081d80f040424084403188000c001c103c00040d184800b62008001210011980b18400c501c05880c1090b46082c0703491140080c02001200e84003036942e940c10481d014000d000780d484010201c0f000e40700d03418950241040300700e6050366880403103003420710070803025042c1c8031a070b1a00030b80356842d000c1d44484100f241d4040b0900307001103000381d058040184a00e4060616265443c1b594440302d4200300d401008190380420054103041c4c101600b00e030b0110342400610300d00103000300000c074108101000036800541d120006116a01c1d5036105400c01e6802504543e11a4022900140a80382c8541c007504405c0b20140340c00303003482c00b000c107481e051303502103071501c5c211380c00c1502c140025040ac0c1032100400d52100340000e03805c5000d20040c040000150748200e2110b0410000f9550000150b12080c0910002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 78351161 1250 78349911 78349933
    0xc0f0e04020f0306090703111306110a03051207020102070203011d06070306051e0a05040207060b0a08010902030a1e02130515090105060f0715020c070515030709051c050a0b1008 78
    0x60b40440744c1c04103046440907510345669500b20001c103c01040c0043c021800203840b1003104400c0c0c00401220419030325404c45040d100c06480e01c600311440d0040100e0783c140510903074020041952a8441c400388001030410700c0940010303003510f0304400c507500d690300c00c00201c903d0020140085980a402410306004880c1b0b004c002c909200c920144039440e48554410f95011550b40b21144130051070024000e64580000e0b04040d802403000da00c03030a1080080980000e203809040c051045131540040203015442c0c0c00340c0b1140d12074040480c2c20401c1c000800700040040e6943d02c0112601d290038440040c4900c3d01200325084854081000c07441000c0300c600421032503a0b400211010f45a0000303081340c0324101c0c0d180016901c10440080d00b601c900118001101020019005040364000c8440345440446e404501c0c4541c841035030174400260080b00c09103e281003119100c888804d034580d800d51090125203800f401c2210b0000d0864020b0064024060210484040709024110380342c040d100304101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 78352411 1250 78351161 78351187
    0x2010507020d05090105040306020f03070f0c081c060b0705010f0c09030c090c11030a020a030201050c0301060815010e130509010c02070b03010905060a030f050a231207020d060c0f0e0402 82
    0x300490040c200140080c0c211380c941d200c0c4003135400455202c107065490342c81d200d104640d2038100b00c1c2c44900103089540800d070300328403d203080c20b0300b6030f0010250761900f110f000c10302c501180401000758580703456410000e0203034407040061400a0003800001000302d001c0030000d06031184c008821080000351041400440c8492600728121034403100e000940060503c819555041207040d07202c814000441d102d8210394011548406c0a4401e40c000c101a07910502445071a020130301403a00005c41003000103400c0c1d2132510f81c407800044141040c140700c1421900140c214410b402c01d41014917203c2e414403408030000d01600848054030f0000d01089420040608014081481004905a290004601d4507110588504040c41d000f0341464408401810513554884542c6000c0310000b800c2d03416203031314000100f070788207400501e00b01906061000452121094109160603070f4040b1950540030009221845442031400241c0c0720b4511115103688007814550502480c140194010003c01d061000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 78353661 1250 78352411 78352423
    0x501050a11070e070809160b0706020c12041202090a02030105030607120605060a0306061704020307140303091306360c1803030e04110906030a0203130503120f070201050702 76
    0x11207140c1241800401441e951400c14294040102e42c00c402c814014401d500011952050004004940c445611003107d1002c103035007407140380701d0000c0c10701201000402c03540041441c4182081242c51a02e60b04214894640c07003540044406040004108118104000e000c1e6200000140c11800c545c94940440d44585008080b079081240c4912100310100b099130061000d000d003d400b894071102d0b00c55001d0b0052819014100c04641400c0040001441e103a2030684038035400350142505614002003030303030865a04a141a8540030900c0903090319100c000000705113615031480410800c0c60140a0300c000c850742c2018800c0c001d03200340030f0942198080e4003008015002e001c0068448420b06080750728030125594440100c6552400000341a8000e2411413140d0080f50104041035074040c425000b881007240ca19000030f41807002502c00001c66020350741c4a04005c1611641c1d507404c0d03a8150441d0700c1300d00205103e40c4100248140c11f0382c2d10341584d41c1301b00140020003050070704a01c0699505 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 78354911 1250 78353661 78353677
    0x102070c09090213020703050307030f0c021f021c06060801080a03051603090b070606030203010506060921160306050702070614031314031204140d140702010c0209240307050105 78
    0x182c03156804411900c0380840100380c2480c1d04002c41d01e601c0b40b0710b00184540d0041d1009d00c0001c0c01d00ca00501c000f881446100c2c1400070540040011200000b031103443e802041210700d0340c0300d909000c4a000030f40c4174010200c251022007000224241820000340c00341b10103800004e095400302440302c0000390810100c84500b2018119510b00e45c10f20307d0101da4602590f00012180400410f040d010440c80307030001703029240308074000e010700c2d0b585c0c0041c440c00f4094000800d5201c0310f152070300c0304204012003140722801110400e550024402c031462100030b4010b540304483c025a100104007450340d040c089640079003c03d19081c1c0d1624004800e00d121404081c1c040110540802d980c01d0400800d030b031605203801851025a520352880c000040f12956007100d0a481c0c60f500502c102510001c042060f42003d040ca894400c651020703d89281c500c1d4001c1c2b1400c9040c0031854140b2400760b03591100080c0300d040c0d0062480810100d0120002c00b44404202180c060392000c1020710180ea08201030714000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 78356161 1250 78354911 78354929
    0x9050a060c050313030c05010b0d0f020306010501081608060a0e10080c0a0b0f0918090d0801120201020703030c050c090f07030f1514040b0415051507050a0b07170903030108010b030102070c 83
    0x3032001c07400c02030b00514040030b49c140d00c03c80c8401e1400c20000c00d003201800160085041c0d41d881ea0f81c1c0d100641c0c03071010842d001c1840040854036520154002c100035500603401501d06003640361180a8031002c48030507500c00c50b6035001050200300300141001925000324054801241d03c901d0881c0748000c601840b001070b1769500c0c000c500b1003503a0301e41c11a01000481c24a540d80c0300350500c0780d100da45840d1102c801c0c100040f1590300100340044140401590303254180d008080c00e5145442c111140c4107801012112401003a001482581e25044264014507441c00c51701c9540c244403902030f0440303008032990502503080800701d40d06070599000000841d0075007003001800c03a46a500040c002c240c45154660711910f8082c0040380614501041c00580b642920302d400c1a20010401020074041e54000503c181c1c4020308281c0098141002c540e000600b600305200501d10484154041040c00c80324038105a1010004200451090040100200c41580210700d44600d41d1224040440140241045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 78357411 1250 78356161 78356177
    0x15050702060d140c04060e040603020a1707030b04080a110c010f0e03010905010f09170c07090207141c14070b0105090c0405060d0606090905010b180301060909050a060c05031303 78
    0x10325882da41003007280f215a10140b8005207045102901310303420030300076000021031056074140305081620440054a40043c01403c9075490300340c0c0303110039003c4121400554010304c08004006640d41d0102e50082d8419400107850700c01441e40101004650f540c0032050364005a080105070b60454500950240d1070301e000c8116000c10408203000d0315100100918540c40c0070340035000c110450740411042d0307100d16203040c08000c0c803c850b00750b14003503510405015045800b0811201c40603030b00810740944592400c00e04680210452800c142c0e0705018030084410000950000540c0444103801e100c080d2450541441160b844510712000d050241c103000d441e030b00c0e010413505c2860a0542d802490010704282d5140902644080544001c0c442e0340d0106510040104003680e03213000e010b06840114004600b84942d1a00010030101208081e6800d9540c074640071800483c140a800b00030350081004003528a0240303080e0086414203000c48013000010300c01e1001103594240c1244009805291501c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 78358661 1250 78357411 78357427
    0x1030312051810020c0d1e050711060316030501080d0906200607020d021009030c0201030506041401080a021815130e010f0507030c030e06061908010504030305040209011505070206 79
    0x2d0100b000001401d6911034411000026025500149410075408043c0c4005a803000c00590f580c0c4841c1501700c80c00300c4509003500040d482140070380001805400e0b1801d00410240109030907034415550700c0d0440c4008410251170a4250080c02c0c01080c66034011300c40c02298110060a28901b80204020402e0007400e0300300e00d0303060510030380200315040103803042800c0241d800303555203925251881c0980030b002040230440d000751180d5440302c0e425448034500500c071640118014800242000d40c0903555003006142074aa06103024064500000100009080d031700400c0f114580d90200c14500e01120030400c5400030b20006d017442c00d50416100c000d0380d041391800960103401c040f00001c5040d841c1180c02090050107400c8075000b0394450302e00300660103480c0c0d4100c091766084c2091480ca46d0107900410941d09040c11110012580140c00a01c8a034032610443c2c01c5d9030b0180c50582c0041c3e05e420a01007903107000d0003524010003031004041e600548540019200307000703000c8068400e81c40801c0c192 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 78359911 1250 78358661 78358681
    0xd11100c0605070903020102120906040e13050d08010801061e05060705030d09030903020a150e010e010306050409050c090c0307020706051c0c2115140103020c12041a030103031205 79
    0x40d08035940200e0500c00c91402100c0204201003510099006100d100c0c01c52040001c2642113400b0903070007404c0b107850103040212004a07100e02910b06003c0881420700500850302c21f00c0700001c01240c982e505d5099500d80000c180c256406500700d06004001c1d42003d80c001a4032410b1441220016500741d616291142400d506500910054540c0316080c0128002010b07800319600081c1e80c8202c694840140d101c290000507250014208804202c82c0f040015456000740a0300d00c00712814500818200c0c0c68402040c2640c42c0c0c004200c5196112450010080c03505000c0075511644a120443c02d601c2d00b000700030b642e9503140c82110140701c0d00042000e20050704207040b10317040040c01014000000e500700000d01c140d208480224621501c078000840c00000c0740200b990061205903a55089414110b48c1c0d45440d1441301041d040c140c0c00c00c40440014000c0c05664864a15540f000c1e481c2c81c58100e1340c03e43d14031000030386071022004000500009030040c441c0301c2c40c400c0b02c480c0000e495488141e06 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 78361161 1250 78359911 78359927
    0x5010507140a0b011514120a05040206090303070302010614061e030403140a0c12020304050d11132c0c15070c031e11030604030509010f0203040504020a0c020f0d1110 73
    0x7400244a120012803000c10300580717114240c81c10b036110a03036141144002c48442c0900300303043c0c6074101440c0100d0070103a01e64000c503401c940020641407801c84000c002900d954040e0038124003513511040d04100007204052101c101d03440c195000e9241041ea4420280950311119481115010100204e801d05201705070070b414411031056281e42e607000c3d01101400882042c1c60450303a0061400c508404144088161400c884025003800d08010459882000e080c40030342c0e20039082144c921402c02e5015460050b43c00c03007a003040d1200c4d8446406416503030b2202d46465449507a51040350480d0a60301c6820104d0145082003000d1611800b042c9070110556000780d001030b16811101308014a003502e401940d69105116440c810110091901450340340c0c801180c0c0a00461401d004150a075401a6200020080107106407480e2036165000507040ba0030014020340000c8258215008604000060102c820310403038403484034a1043d5620004000c9c025001c2d80035540038444200594010086 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 78362411 1250 78361161 78361163
    0xa051f18030b040516030c0603020a1205100e0c070b060409110406081f06030c0501141605030702010f020f061611010f0b0301050c03010e04020120030a0809070f05010507140a 77
    0x2199040d64034101002c0c421420382c2c0c207071501c0c000c0d0b0718041d0040301d00a50381d000f106c2c1e104050380d100c646401d505130025000034000109218a07522911490f201911500d0722909022151300a07050400e010344840d00303401401007040d524108100300104d005213a1581c0c0c000750884000c5611019803078400d14900b0310014040d0070600302036020581c01000f2401c20f41106a900703d880041410003640c2c401e07581c06210241001d44007a1050055500c200d04ca0741c64207000010040c90039088102c202a03405016105031040c0e000800c42e5000c544e44801c028000035003a200415881d50040d040907180c020143c1281c0325110303208404240103025111550942e11031030020041e248a008942014084504c0042d1003940703064005003040b49100c0c00c1d241aa0310050f8040401c0e50f50340c2c01520580f200481070280c00401e419200074840c01000240485030860382c4030042c50170001a0f50345040300c59000480c036040058810f0120b642e010702039a0301250440040d842055841c02c03c80e0a1400c1200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 78363661 1250 78362411 78362447
    0x7051309050709030f03030518070308030f0604090506070e030c06030105100807031b030b0f0118060c1703010b13090c021f0b030d0207080c03030403020906040f0f020d0902030c0a051f 81
    0x28170710b09050301680420f00c201c4036010700c214800c1c0014001c60f111551400010700c11b0f0400e001117110b9601c003890031a40401d000c0d20008240720191143da00e030403803c031141000a4404400c070140d03800c05205d04007074114252071450441d418140000d444104100c0120200441d05001800c840d120341c00401c030038214520460000882c14600802070b04603811034500400071046c041103d5417007468200741c03164082d4919211113041a0041b030b0b08591101e03085d1900d02c940d8866030242d1107164010b6008040c00c0780c9980d503c81c5e207000d1103800715105038085007070a840e011140304c8454020030076104e10720303c07081e020707100030980c0300848010311903c01070a403d0700c204500c5c9454140c00042041c01d80303c02a044942030555401055a00d00c500c0c00000e4201c0300c850042000307803c2c90342044075003401810380420054900c04450701280c000c614000d034031039203960071103042d800c00f440155120300301624052041810440480c03182c00c0d4607628040c1e8842d002400825080c80742c01c001d4105901e00d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 78364911 1250 78363661 78363683
    0x3070c031e180f0e0c03090708060a09020f0f0f0f0105070c0b03180d021c0509041e0b04140f070207080a1a0105120706030c0e12010507080705130905070903 69
    0x41e001444940c120340c4124810241c44004501c65501c0d03680c810458501e42e0141005648580d0112040c3c0c002814003c010310403980081100203082c04140c0c0304143e01940000c4007a4140100301c6000703622500c0314003517294035030304410580f594283d001c80305409451201442c100000125014820080c0103006045409800300d4000500d5005501440820440f10f00300c12828001c2926074040000d142c02590041c0d5111166820b2101e900040100030700b4118242114a40803500b5600900410303040c0c10a8404441c40f080e1281c030681c42408420f903000c00000129074075002000c075000e065400c0c44000000060090340c42004140060020082a1003000c9518074040b040f20b1891100e00d0390b4881000008100b0742000b498801e01d81c07102d04000c100503407030100168010000c107c064000c012000c0283e808035101e00b4504103000c0ca003071000141d5440d002d0801020004040c109108124041114000c8d4540889145041e00d031100e5000625482d201d400340c8400e2074560009290b0700710b0b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 78366161 1250 78364911 78364967
    0x9060f070501140c1602090403140a020705040c090803040b030603070f12030e040e3c0a020301110901080f0603030d0923071503050a061a07050106060305060603070c03 74
    0x640000070398084803007070800c0f2500c415a100390103000b6110914014184154204058030b05041c4154005000e0304200d80340d452801c01c1c0c410030740c0c051035440c030140e403000c4020403607402e2511885118403014546807102c5401c09501580300e200324402e54040b0640400461010380c1e06200c4640140030b118000c00d09980d0b0b4a24001f030241c80c000703003038021401d60802e045503070520380035046072010000c000d002c064421800d00130034403403507501c2c10f100e085401c11840d00c640c0d040800c0300785d000c8200d8014560302880744105403d540c0725401c0d0400c4035030140819003a5980150310f003a00822800505c0e0b4241da10907010910390301070f411000c0c90312420003040c0b0301031190400306864890701c807490540c000e580340e08a80340d560002e0301c5004940d02001142c00342d01c0d03100c0c0d0301c00340d0085404000800c11554030b6004803550641b0889140e13140100247d41c80421800340704000c020310181c14140042e141c86000070301280001043c0e034060181c05a00b0104043c800d154416070419480711100840d011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 78367411 1250 78366161 78366163
    0xd060519060306080102190305090109050d180f050303030c0a020102070f150c020601051309020a080f0607021b180603010212010308040602010c020a080706092103140c09010801030809060f0705 85
    0x51031240902282c503102000c95641300600856004040401c10358040028088044004050007003821055550300d0103200c00042c0b007130040703000c0030204d5a114a02e0418039115645c00c98078a5002c40c0b42c07881d01100c20090783d00e0204c20303030b0f91052254000c207494100148003a40a8480e10400801c0c1c1c08100c0c11a000708000361540b4241ea2a9030307a41040721640500081eaaa010b0a01440354805c840207882c0301080c0f4035401c124440c034030140c84442d0380fa6682e207001d854020841d5403001c1d1030300110700700220541d04000942e4800040000300d90461110f001040d101da86010742940380e85003000004950340c4094046519400d601c2103001003a681d0fa0a041d41140c029006260055003498503488415200041d4000c00a8004101d41e240c10780d15600c0030700801c2101c4084035480c442201602c085a5400040c011401d444d442c0443e0055440085400c50f900003002e080c035000043c064035800c0c0e640300e08000e040d80e9118405a41e03507002c1800040c1540101200c1c40000c40000174480c0070000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 78368661 1250 78367411 78367459
    0x806011a070c0f210f060b0f06030c0c0105090601030816170a0216060215010e06010e03060903030412050a0f1d2e0516080304030314131101050a050405060d0605 71
    0x10205198001d81d8425421215004244035001e00034418180312140403031b29a9102c2462808010602e17405644504007080c1c8a80048401442141d0f0128220204240c01e0294551000380359001d0009907040d650b0320b2001e4000c01c51a050b945141041100401054078520b04412020b4040c10744c40e80b0181c08000d5441040f41e880302540d0000d0314001a0450000502e0101c50054040544280e802c00c80c00c81c5500400401c080c4c10441c02072030b101c080d40c4041c4409030080e180240915940d24040c103200300d4a8840c6001d60b0100202000071081d06940301408036140794803498a01046003079462102c036590005c5083c141e2029102150904820001c400c41c08040441c000e13680580c04441402d076018000c10003d040b05003240200403001a04400c01142e1040c860300b40061901030035501c031001c1c0c41c012070f545918404450110001c2c021050011419800300b440d1071072904c20304160007003403409248030380d0340a54808200c05c602c040b001d800110207485c0240807003101107907845200709140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 78369911 1250 78368661 78368669
    0xd020d0e060907060906021e010f0204181a09270d05070311010603030906080403020a0b010f08100c27090203100e1605090f040f090501020a0e0a0806011a070c0f 71
    0x8402d12100160941c040c5c03800004441103600030303201540b69840c1880c0c0400d101004008195a81c1c04d62000d00005031001d04080c0c0040c0c44c4082d51240c8180d242c40031284000903230343d200b001c0720095440d5a03139007036140c2d43c1c81460070305423030941400c013a0703100242c80c005441400c0501485540d07103000c0d40c0c0000903000c540c0c005d6540351140754205c58080d08a0f00c05000107030010701c4030701081c00202c1c000c81003d500640b00e44125981484a82c50701d40e100402a080003c0d0300d00402c00402c4013803001c00008007007102d803900c01c200001c4600d04c09031220209841c18407030000000c031100a0a610380a8210040150010079540c0b490940a010b107070360900e006502080c644140802d100503d58290742da98100700e074450502d000001e4040055901044283d15030060300c80c1880c0d8403c81d0a40584c002e524403507000540c84400b000000752080c0c542c990024050f000c410350800c03056800064240c1102c500c0c005001d50351440da69022594403d2082c003030842c034206030001034840e4040c4040b404032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 78371161 1250 78369911 78369913
    0x140303070306090911010521091005070521090307080d0e06070809070e0a090501150905060f0a0b0702010203090d11010207050409150c020309030706080a0501090203040f080d020d0e0609 82
    0x12680f6040f2400031143c10800c05003100841c064081c4003540030f2401480c00080c0303040048054403c40141041400f01280c02010079007081510304209903076801015040155402e040b41841d09004444141000c018401c0860020150110300d000400b841141c0d2032540200d5420399811541024202511803860800c1d118801d410004075100e105890060285401c8809003040790315050b01100d5569000e0200310400707a8912400c000100700b445017501000e0b5002c4040809071a101101c402c0380c070010000703805541400a1020b140c0e40d03001002c810344421861443e1a00c8140c00100d245003c1c028403560003d40a440200611507025001021083e0990848008030b4951052106642c0350940041c8002a680784591002000d07400044050a20740b0449041110000000c0e28100c2e02c0d5001c2c00118071170400307001c0224481c0c0240d40c0584580d0506500c0d60800c0c0d5903104c0842c0c4090000f40c0214800720b034100402aa036012107030991a248810700c030b580103905034180c072100c00760751045003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 78372411 1250 78371161 78371171
    0x905060f030706050f031b03010e0406200901050c0c0a0b0c010c0c021806010c0c090c020606040204030807120302040f09051503070501020c06220b07021806100c020d1403030703 78
    0x201c0c600010200c00303481c102e42d41c42d424081d032008411102e0300040d000341b040c2d5208060404d20303005600c0286001f040d08241a001c45e06050409404840d496403c504803080340342180140c20302140c0807540141400c2c42c025035141c407a40c1000e4117090701e100d56a540240c0076000007558104500249c901048014001c00c00c404080d2010344030031614400080d001031364501c406054111102c03034594001d006041c914031201c41c0f0395038110000c2d101d0b08006902da42c0c03440c410003c0341e070410402e58068401d407011407a250850f190b0a429008001d802841e07107800b0701e10307101601d101340c056030b000702200d0009400d201c3e2030340044c0c0c0c060041203400c256400381344001c00049280000394281103400c1038020f03042cfe120554003404050f80c84001c1c0f0450109180082c6840001712210400080610b00a040d4452000384108684100c540000340c81201245040c00350550300c104400ca1518a5414603110040c45440030030b001a40500f000b900401c250520317956243e802100540c0705040c160f40400c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 78373661 1250 78372411 78372439
    0x31201090603020307120201091401031b020f071d04080f19020607080606070b1503010e100605120303091c12050906060103050a020a0207050603090a0b04110a0911030402130e07090506 81
    0x2508406c2c20b04c000e03000608a4030f08208102c561051001203580614000c41d0380d6024100c10b40342c50310108451401640301e900d441450901c10b2150304003602d900035401c64400c40d448940346120502134005082d4000004003016000400c404840c4000c098420301000941d0710500a0f4071900200e89000104940f070001800520b060012144041d900000c681c003107840b41c1150803000c141604a0b59015984c3c2d402c0084044001c200816410300c401201003807440c10b000c1480392001c54002c0004c1154810300a10900c081c1c040789454030740b039075401010042c1111440c2214600c1000516180030f40c5000140840b5050206a075072094500380ca0a002a8039070301c0000049200b102401001a08020820304c0649407402c015504001d042044038080841515075000c0d685003a03d0450f1441507020050105d030500c0b000c100700510000004101ca40c10b10300c8408028071009000030707c110883c0c00301c06411171241e4411942e804062007103460b816290003074480208401e403640c0d4030690f41668800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 78374911 1250 78373661 78373679
    0x3060f031a06010e130b010306050d150605010309020901030f0c050406060f02010c02030a1205060d060c0809060a0501150c020a0f08010f0605120307030813150906050a0e060711031201090603020307 87
    0x2c0484100649280c10720b00c150505c03000200900d02c0c105040607101c2d41c000800c0e9994001c0c210b8010b0040700d4154159461600305401c1b1942540010305050824034001d015a45084085046035000f00401c21941810300d803540e100c44e5160451a401443d01d500803a58a50082c000280c00b02d02e6002080345441404060b82c1d40d0150041c202c0002e8060749084401c844d00b030300700780d0700800c0280580c2e002410550310541900d2200c8034060006052038108000c4079070805c1125004046000c0c00c00017941081440440d4014014070700c002e0004c841100c40864580d042c0c1300008160090b684c0d001c49444a07819406000c10806c140c1c0918107060012440d841c1403000c440c0200c034020011071805640e640d069548840c01042c1d046544546007030040450b0003c00130000c10050b207040040e40380c0315860007030215a0060500d1001520307080c4020112600096400c0c1c215801e4280341c405400030017020740c51441855040c00c5150715020001501e0344003600040300352442181680c0f5202d440700d440b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 78376161 1250 78374911 78374927
    0xb0109030b1f2c010f08070e0603030c07030308150402040b0d0902180103060501091d06072f060603070b0f040b07020109050d11031606170703060f031a0601 69
    0x1d406884600c002c90000b0b80b4040c54400940071040c440c9819a42d5602807110b40c0062910041031550305440d011a0054141c0030240903060b4901c0700342000b41407801d1a50b80f0f20981c000c0004000c4410302241c60385d9010001ea81448400d20100d0300056100d1600800d002001d0b500c0d44011070085202e1401854a4000d480a58504043c800d0902241d108004080c104040050342c05c080064092020f0380f12008840303010b90701801000c6000e515000581c001c40350800c04007110a03061490791400154086042a040216480c240321051407100b650003175030841001d040100e000c5110030145034500818a1489081c0c22020f031208683d403000c800505200d412140b070341c0315204000600c01c0d40300700e101908005006140206801d500c0d4404a0382120070f1081c284c400e24440390304d081d90340c602008408440e44004d0b0a4240041c0b0f4080060300090b80c415480001044040c00280f0442c4668007000060424180c21410155a828007409001008100401d001407190004025501403101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 78377411 1250 78376161 78376163
    0x90601020318100e03030d0c080a06053703031d030d08040b19050c03060f03010204061b1e1202012702040e0c040c12050906040f080304060f020a0e040b010903 70
    0x15a10050382c140e41041100b450794510079090104a001100d0305803400c0014100d08560751744005103034048030b8000f911829004110781c0c51079007442c005128540ba1108240c5070b002280140c48601114246552100c98200c01c5045420f030700554000301f4036a00070890460f4030038141c28510070503074400078036848030186c1c07002c00c005c1030031500401c0004c1c10191029a02c40c2900c100d68a03054500304041c1d00703030b64040c0e0b040d4401d200080180489450007420105940d40d0403070085140520307010340948221890502103c0002c121a103000078003981e08441030943c209611105c2c0072009900d01400b82082034000000158680443d030040908405021007001008043d113031020740c883c0c1d00b008003030050150110854014007925885541311400f560190329601c1e00d0780504c107482040c0d000100c60703008004607021f502140610011840e046032038901c09420940c0e169a035582c3d420040b014010110110154520001d480507403240c0c40380c1005101e0301c0445041c880001080011110382044e800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 78378661 1250 78377411 78377437
    0x100b04020403050d0c05030c030a09050f030622081605010507080112020a090914010510081b09130305040b0a05030f0a020c0c040213030b0901020a0206070207060f0c06060e13020906010203 83
    0x3482c41c49285c060034040c034106110f0030499140440c0c13100d1603400c54108000f400d000c1103185d00148a140703404010030030703603080c150014000c078a00055041042c04480d20080c0400340040000018814801c00325a805603070111480d50491040c6016402031008580320b0740050303a080c002203100d4290901300019144c0080c6002c95290802c00382c0300045c11032110441d0b003c05d0004070703460440020b000320b1784610344141c9800300d0310745010380300c3e800c02801d899a24030303080d81090400d0843c0d9800a8198001781142403000381a0301c14034040c4c581d0320803500300c0b018404000c20240c0720590700030000e511030300381510403591503119480300900381e0241e41d201c06044e80102402c400141400e5010300f00980e0b0003581122050b54940341e441841a051314150181d94001030340342c9025804000c4241c000c1c1c3ca40c8000c0220514100d03000303000103041c029103401c01005440070410701c1003941041c4083d05800340c90341c0c1c2c541072004545400104c030754004c0780104007940c00102298000f009444051284003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 78379911 1250 78378661 78378673
    0x705070306050a1413060c030902030a120302130e150901060c03120b060d020310140901060f0e10020309011706010c0209130b19050609010501090b161202100b0402040305 75
    0x25540c0710203400c1c01040032403001d51300c90b40400d01c0c3e807800030168012020110f024000112600784802a1070b04200c1400904d4240b15010b0b00580f00020302d0710310180c10105442e040101c2100032030107403045126851102409050115007041c039607107451b018829240f055208101b40f130040c81a41030091103042c021a14000c200c5000c80d0181d174000c041c541185a00260200c51180050311503003100311054441980402044010003080c1801c00107081c03041e29416405044500144418005004103400c2001c040c0841900d103001c3c8600c035411800007005104203825041009582c0d800c1040300600040048100c0503141490003642030140d1410b070b6501251a81d50380070321905440160803010850065005000420a110449405806990050602040300c40480c0c0250750010f4402403080c01004e0041001d030b0703040504101124844000b007512402c520406861440b8100005070050780f492091410031030340480d07040c041c0030100030100030b90f07041c51007408201d000380e01004200d98861 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 78381161 1250 78379911 78379913
    0x10f0b030703200a0f11060c070f0501021306050706150503070b1b030d05010302030d020c030604020d03021606090f0e1303030b06041a030a0b0607030e0913050601030c08011107050703 81
    0x30740050700c1c83e042440c96038110159441c080c0742d003a402030625070000707100f07800800140c607031110000d021030301248020807079400c0540d201d41c101d10a104004110309401d0391200701b000800c1d01607511240b4000d5032003c00701d035600c6d0003074500e07448640c04552591404161007940c0d407150b000d01b400e445014005041460411031401401e500039540241e00c0c503204400445505c0c02003000b032850440c426404034403035255205052814a1590740700702035411041c1000c40ca51400900710740c1c42901202d5100303017800a03007010703802d14081280342c075801c030340540000c1600c40d00b000054080300c44c00c54800302c540741d84000006a09000361501c41c1c1064410100b80302180c03081d0000c16128000625152405503204d5010310318041001d840e8400e1000070003000800304c4644a101c10008080e640315280440e1507400030507034901404411720800c2d181002c03900c0302603048170591140358401e08a8003296101c0c10114501400d500c00e01c000f640c20003d000c0c030302403541c0d426a5104c6901c24000c04449041d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 78382411 1250 78381161 78381167
    0x907110a0b0c0706110703030623060d0f230a0b0d080a030e030301031a0f01030305031f09020d1a12030a030e010f0c0c03080106030506060a050f0c160806010f0b0307 73
    0xc090b10440120b0742c02d0240700d020132403d11035540d401050864107039480007107141c0075068400d42d6100c40c0380320400c540b64a00c85107249800c80103d1108840b0280d94098002d40e03003004015941550716100e10b042441e80420184503580580109880d00f420565a0781d4280f00b000d403514055210f03081941045002c0010b1552400350000401c41c1c100414800d220089691468100f60310a85003191a40d0628901104084601c0e0f040940030b045055550704684020b4a10b10018080010340051001e00503220340c1102092405041444001d66480300c0c2e83c0c01306805050503c041000041c0d1251200040385454800c082910b4881c802440c00d000e801d00c1e05600070f11603400410401d5480e001401c1c29101103110741482c2c14101d07142d00705000c2d0b546c28020325400c4160048400e00d440d00c014090b00d65901c00c16181c900986182050303403040c62003010109409603c40030100791180c0706240d41c41d002e1902014050f600c8003421200c143ea03a0300046800640e013442810034030501040403c00040c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 78383661 1250 78382411 78382433
    0x501030b180f040303050903090a06110106090f021b0c0d0b1815072c04021309060807030b15010504090902120d02010b01020712020f190305010504030309020907110a 73
    0xc4018040d1842404086450400c007800700d401c2442203101904010030181c043c483c8035082000c0c02c00031070401080f0710104030031403000d0080c8418400a6000f00ca4581c50940140b405480c3c0303803105124517840d81d00000040d401c0454101000000c0500402e102000090b41182030b4178000d204103042080c58490034142c68000d014103a8040c4282442c00c01100200102d020258403003040310311914001c40000d042d03d070031041d070b07481030400ca0060507414006803100080c8001c0417140140ea481a0140010f02469154044145c00f03003032100020ba0740c0d2003c200e03003003100d0050401c0c2c40b05039201d40c0008502c1c055180442e01080e020700c000d1007103001c140d002410071031024108041e0303810101c100c0340ca8850600c41c8a00140c0d140c5440054550b8180014401048003d441d00104007255000030058910001c0242c0100d1080c00b030181140c0c034100340e2000841d0000300801c050304041c00c004000d820411000c1c0d0041c0c0003c1d020a103403031302c03070341c1d00c141c080c0c8603500a0040c40c042c0c0da80b1000315003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 78384911 1250 78383661 78383681
    0x7030308130c060512010501030b030d030f1503060c0207081207060207020a05060d05060f030c030a080c07050d060209010216031a0c090307060305060f04060f0e0603010603120c060e070b04050103 86
    0x10460021400004040c01c40c15005400d072602c442c5e4a03074880180c403141045058120740d0400d420145d0b85002030710700040150761030b2414240410700341c903282c403014001d2180f92142060100420000814400340e980001e801c160749a01395004540c94111050b9103003140e403180c0781d2a0340c00300700b28004a00151b0190210f40e100500c0b10b241e080c3c0c0e484c001001c41c0c000c48000d01c1c201e5510024001d4a14042c401e460f2821029009849070107110b000080c0c60715005000905103400005210708241c07414000c0902801e0000c001d41441c000074140384000b900704010050140c4a0302411050f600400484c1501300c0b9408941031a401798070b0301240b40001c0b0090010600c0c1c43c030511860020740e50501000300541013503900040c103480d01400b00008000110300550156280001c1840481c0901034103a042d41d840c1090300d000754803003401290040800744d00182c60b450340c2000c40d640c1c1541c0543e9820626024100030302084428140040d15608036103c0c00000101c1080108515400f83c0c004c5d03101c1c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 78386161 1250 78384911 78384931
    0xc031801150306020904052d060f090702030406030608060103020a05060d0b120a0b01090c080f0c1e0a03050a110307030b0d0510051905010303080f0405010e1e010c020f07030308 78
    0x1a207106007224054922a800c1182c0f1150045800c0c40c00341014030039180c0c841c8070900034041050607411070f2508100c0803d0580560865000000ea1ba038490032621200564058410062071902c41002500c94000b4010040040d0070180d0001c1c01001c00100d59050f260000c1c0007502e100d00d0f00040011a5001005c0808400d032590305941c00b030303a102400703007010359290300183c00105035520302050b49080503008184101e2901c0c5c07183c600c6c9540309425981c05001c44074400015150203001c1a030078003402c1c1c0c01c800e46c070a00c072440c031144007a120f0103070000c1000d40d00e00f4846070310360084680c1502c1c85000300030032010080c800940b00c81e100340c1003514403070800703000c0319905029a110f80d401e10f46030521701042603440f41d007480b81d600300001c0e440350700000d1940b0400c0594150356009000c198041d00042c20b42260740c0110b000c1c01001e50264844030303000400c440ca81c0d00303031021618002d03c50758080490365107010455140c140c000704424155001c044050107103281196410f442084000d0420b801d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 78387411 1250 78386161 78386171
    0x20f1506010522030c060f05030c180a08010906020415050307080c030a020708160c050d0f0b0a0f09030801050306010f0303020709150b07060204090513051b0f032d0102030c031801 79
    0x412003d12918007450241c0e031802d4040741080700143c00045480742c1d603010020b0420070007080303a80307840a5459810b80401c00c034800d1468200041c460440c260030240a55182008000403c140c55004100319502d8513a84402c00c190a00241d40d180002c80748100801c9140002400c0c1e00404801035500c161230000041c01c0c00c40c16110707106103400c4003400340b0306542d1141c103400131312009041220050204403903800c0c0780c83d4256601104400d07903100042c01250650f000c43e13031a41a070341206410017074041c020000c049141c14000e00c00e0b0403e226403402400390000108400d20a01250f4081c0c81e01a00100451441c280c1690020728003544c2c0952010402c240c0410140703105001401e0080c0940740250715242000d01c0102118800f07042d80a1280341505050001940070039080c410042d0302c11548101c1e100a8089046013034170103075480e41400b41d200c0f80a440304040583c2c4a11b9400f1851500244071038612045c00c038407080e620080c038000c082c400901c648000103550346445581400100b2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 78388661 1250 78387411 78387457
    0x9040f060e030a051308010e0706031503080f0a080105040e0a0f050312040c0f050102030703090302060a03090204020d020705010b0a0501020c150c15180d200328020f15060105 77
    0x411030f0003400c108000540b00060100068150703003400005408110000c0000c06849001a6074801d400c1c440d681c181a10b88210101090080304100002c540152865584e800c00d43c072a030304030758810304101000c0341c0c80d0b900200c5d20f070606101c0d00b03400e0036035000180321401c0c0c81e4540e00e4040c0807060041b502da02c0300300080c035442040c0d00d44c0c003406a0b1203100500d903214200011005005425000035045620920200b400f00750312010b207004407074050b00c0066480c100030400310080c100c00700000e9041800042c420060080c04d5005004841c0100005c01041d40444204100301c80c01d44929030040c0c4c44844202d0301072400e0900904001b40c4c600c8241e160070a01c42d400350408003001d01c421044080c0c5020845808100c110400ca050403505c09021141e801c0c90001e01010344520000f007840b0400700c956180000d040048a00038050080d041e0f5405581c120710070481044905040014004c0d40001414030307500003189040803600030310000791551082c0044441d504407809101c003401200741104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 78389911 1250 78388661 78388663
    0xc1809020d020d0f06050108180706110a05011407020d0c05070b0307050c011a0a0509160305070201090b0c040614030f0f0402130e070303091401020c10050c070b0d060e040209040f060e 81
    0x44540c51840f074021417000c0c03400c2c0c009000802d0084c0012401242c13122032000020300070411605850f424100400362046100300c4510341501100010320b29032900c0d6000741c2c4601c0d501c01807481040ca0f5802c071054055030003801ca44540e00403000800a42c0101018040040037801a590000c05803801d641060941c40d03c59096444940c0c60310054a241d4002030420304115103a0400351105031082c40b01c5007004008035542e480000b0300303003007015658004911901d100f034004031038464004840d14081d00b000d81c504142036120b8442c4001141c80c4034800760440c0d0002c03060700d100740ca0710018140c081d6030344007406249010040040b07a0148081050b802c018842d48180c03c120f00100c401066005d04500d0041d14158507a0000808981042100400303070303074001000000d004059800051100f11754005035032901800200c04c2c00ca005040740880c529281c0e1014001c0509001001e0125030364a00b400d255014080c0c8010790800340301e000007400716440b07107510311145110f0300000811a400206c91 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 78391161 1250 78389911 78389921
    0x1809070201112221110105161b05030f1c0507020d050d030f06050a050f15030c0a03061406030f06030a05010203071106100b0301031b05031605040c1809020d020d 71
    0x82803d500e2424104224003034240c480c0c0070b801c0c2e202c01303490f40004984080030038001d1000010f050a0030302c40340d1202c2e80d2044065808091085054005a4070300745003200c0102072840b40744920f150401070000703807441c00042505030081507801600300f01c210340411103003c062820003401400001c00c40b60700141c486170401000b460064010b062400040c00c0c0007070603600705606000d0f803207061140c240b289550700c0c24084211340e011242040c19070341c42c0020680d280154028404e02c600003000f0030501c41c10304001040c20040ea950100200b80c0c070b55891262104401103980d40004080c400907008186808c8420f40105008045a0602c0c10595400d82642e000b00c54510003e01005103010301e550080185503000307410000c0a000c00c60900f0401045400b0511000e000800041c0b0040d01140301e503912000641030181c10741d002c000058041d40281105441202e000d18601411907080a00c280c8040c921222102c440840c00c034a014035220294004076803440b041a420032200d18140900d220b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 78392411 1250 78391161 78391177
    0x302131502060a060302031c020a0f03020106031a090303130609140102040f0b030c0f0a050c07060c02090a0c09030602180d0c1a0c0309060d0608030304060501140105180907020111 79
    0x400000d20165020007410124050801c5021070704000060005036008607002e120314a484042100c9442500012031078840c1c12000681489a4001982e090540c190415002d6074090341d2052805040a21410105082112040e0160f007017403001c03070342461401d081d101c3c1c46070003800c0c0030803003004039201d6014500c070b42490000c803a0743c002030030040080e030422401d00038a0543c2c0140d0441c941a241c00901d4403410700c0180424600140180311103000f0030690310010031000480b2400350725100c0c050103410300d032030b010303072082119a0019922120390300850040070400c2e91428001451544c0b4039001e03400501141201d10804c0b1480788030b54884c0e170502d0314100e01440c081507025180000107440b562012124400140c0104100c0203000000030440c0c0241000303036542aa55002900740c5401411b0070341000300380780000010b03c0103010388da4000c0c074182e428021003060350b4009d4a0066600344940540c1000c20070302c818001c0c64500d8002c0c01c0b01d0344421035000101d808a680101414a54061a9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 78393661 1250 78392411 78392429
    0x30207120c091a0901090908040e0403031e0c171e0709090e1e010603080711040609180203010c080106020c040504170403050a0b01080601050f040c0311130e0903040308040b0a030213 80
    0x30f0350302d0385413500e403c00500428080a0421128042d5292041d0314803d501401c0b40c2c207040740c0049001c0510070f0344883e140050000c0c240b000ba1150301002400703008003622440004040301c11103402c080d03c8154490252005c810320b102c1480111003900c504490081000090001803e00019108624001c5400400c541d101602955114111810000340000c94648260b8036001084c00003071880c03000c03185e8070340c0c1090a01e88030b003d511000501071304103900600850360412201c40d481c003200f80c3c50541c1c0c061003140240903500140204450b1100b0910035140103a1081281a0003420070354486a0850702580d0303c0c94542000c0030b500a503d03842944200d41545c0249124418000c1041a03d8090503480c0041c0186504d000c0004580c0c040c02c600c107030310030740d5542c1c000044640664031402c00c500150350641c0d110080c806030b82d03d5441941c45203624901403980000c0580d00c0100440e002d4075401081242403a00302000072510303800010b921814503608000e2a01303000f8240311f040009005001c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 78394911 1250 78393661 78393701
    0x510030e030412030207080307050c1e15040e0603061006180302100504060f0504060207030602090d06050f0a0e01060503030a2601180c0203071212060306020301090e0d0c030207120c09 81
    0x403400031b00d003d01541c440c80e82c0d50801e10540300010004503a144064804580314030144040b8011480075190440c0401d0f40a0710445c00714640c0c008100180c021180001d14500440d550030082c1038459904441c0c0c003c2c1c040b2046014800c4500801d4402c2c1510708602d001b000198507907002c6152102060301450116070080f60400403154000000020305442e4030344641090b01e07151000e5a03606072804010440f980216400c0200d4507208a5605482d40100040c001420034070071068403401e01341c9200a00c242008074610346024140189000c4800103001985040d00010088451803200e00c10706080900040041809181440000b8040c10500086a81c2c06241c03920303941c1101c2d00305186805540060005101041f103100080108410074113000f500884000c40c00002821283c00c010300700d501c04800415244032070b92001c10300c1490f40f012035040308c47c801401d48012407402350090045e0b003c95010301007500542c25003110790340b24401c5485481e450301080b0056031811042447c0600101c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 78396161 1250 78394911 78394913
    0x180204050c0d230702070303080c0f0c10060906060e2206050306090c01181202090c09030111071a0606030c090406030b04050a020114091305060d0609080a080f010506040510030e030412 81
    0x7120b103d504401d1a0005010709851540c4c0506078000041c80d4140122010030f082440203034407811990508400d00a4540b0b8411040d00f91340280078034000c240701d0603d400800314056010b442c0058480100030884c1151400c4025501102c4100991521080303460f005c000805850802102e40590800005408451850000108420080113650401c0c0b0380d143c10401881d892103544586d42501507610380f0040d0769280c42e244142c407800c191036806d0b6107000544582c14005a0142446510034603d088901092018800c494101903c00e035074803030420030210308501c66000084c150140d000d4004919295203849203042070804540030f03245504904004421907034482544242e4282c1c0012807401d100c02000402c1c1864240010031084c556120041802642e40e80c4c081d4104590103d800d002c152030502d0708400d541c00c041000b80104271030f5008034083e41401c160181c181c88010b0041303414030b440c100c10821030010300070711103060559500080250703890510081c800b6040d2492038108aa0071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 78397411 1250 78396161 78396221
    0x602070b0f07052a0a0303080703020a0c0507060c020916020303061210020a030b040c03140612120a02160801020301051309110d111c0c0905040804090501080601090609180204050c0d 80
    0x501c140c04e9100390405501440000d80142c03038035420100d94030700141c0340c43c69180103407401d050485010f003940c420648001501c991100d80c80313800034429030302d08489480e2080504002d44a1841d000b004d60820b00c005035140c28480c600e0305401c41544212000701504d070340b20f0822a448800c2c4000081d844510201e100d0603c1c1c0a600030903501c902e000c019029211500c44d4038140044c0c0264070032440c0060201d40094200002196501c0f0740e0000c0d42d4810a220000e940c946d1010100e2b080c8001e4000300182c0d801061094a04031903000d07241c440310400102e4401c00410b54103200700c4c0c5030200c406802c6030342e4565140c2c04007401c0c4105804140344614500700410310700c1941c0c0200f012504400e0410010b0324901034542203c0d0300c58804240354440b0b00c0c0c52103450140381c020321589854040005449030000401a0403900354105c1001131903182d42c094015100115208811400603242c200b00509150b0310183d4403183c50f00c0924105126000401c065554411b51000ca50131746510749214681 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 78398661 1250 78397411 78397483
    0x105040c0f02101a03190614100306051e070f02060108070f05040b0619080105180f070e0a05030706020705090f010e0106080a1104030b09070f0602070b0f0705 70
    0x301401d01d10410880250001c0d034880e0052400480c0d030b034540e0b0002c0448400311250700d007880d5000301514109076005207030580b43c00c010f44040e100142020b8904140035211207009010b100c0360100c3d01461800c1d61540f00152201806141c2c00e45045a980881c4110b928110381c001c2d400f50f9501040c52446200003032428006801c00010707500000e00401c500c0000459013422a01e09403004a0150820300018805000d40781d102111801010074030440281d01ca0030f035505844040350004a941ca250340c0e10204854203d9080540ca441400840e0f89039000c1c12105886c0c410040100d40c91603242da001c28185660303540024007590180e8401c1c0060f28001510540c405e00c0c4400c20050b0b5031425501c00b030200e4042c4912014480c94030301007034140c022500302c100c2001c02c1c10314032a41d40d60740e460100e44c1c0310400c071018151030049400c042506150000d6030030407100654028103010341041c1088605902248184544201c01c000740c9000034010b000c01d1100385034107103070041480305044d14065104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 78399911 1250 78398661 78398681
    0x20a060c0e0609041104050402042d031205220801022512120204050d0c090e1506120c04110406020d0302040b250c0f050f09040b04170d020a0503010504 67
    0x11400140001e440e4880c003058454098040390081540b8000c1d4034610080c4c4543d410840d0040c0c000500852848a03081140d544240c80403404098460f04004071040381c001c5000c020b1203054040e1480c00541c4c0f06002404a20030409a4031607500d0503820200ca020815a000e0011650040b4582c0c4950b04c8005401002e1103400d88421183d000d1a502c425100c90741c03840200601ca552595101e858400e5410f44e40a4000034004644010a60404003400c002c3c0e4071500700c51600300b81000e0039801d0045104010344d44481c4c900041a240c0d0400c0001c2c0002c03840b007640d041d00c0384070900103155070780380610300d000780c83d2096060740c450400d07070000d00780b0080300c0a040906004100400820341640c08644416192070992071203170042040010032503500030406001b00204110204208111a55801c01c03a1401c480e401c54101c0401c040c400e05640885000c1e081030345500018010843c0051400c0302965141c80302442c0615640000c0103d030002c40700900092000300041c0542d0606104200c441 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 78401161 1250 78399911 78399917
    0x6030f01090c06230a0201060e1609050f030102090603150405010e0f04030f030605030d1106130b0105060304050f0d020115062d05130e150411160503040f06020a060c 73
    0xda0503a482d0388103010341d0740c8944400c11a82003220320384046107100e02c0e42c9580342c81c40c503955145004031000f030103010140110b403e41401c1d800414a8080c88648a0400e400c01e80c076144d200303526110800560707081040c2042d8040d5000c010380c00c8203669400066202d0f4001f0300320130150301480380c01d1100b1070310143c1000c14034200c2901400007101061248640c0594945403481181340e1040c1c0840140c0102d5000603010f00c0752103007860344035411103405092706c02948200e812540d209203000c7c1c4034441848001d040860034800501507420300400540d8820300480842d200c01ea000c003841c034034001c0d5482c000c40050755107480d030090701c4081c940c401c4000c00051825100d44641d003004400184404440807030302d000d40883c030a070154000d01c16615003604403041804010b40e60b018a9030b96400845803201d1701c9030714003070f07820b81460540319448461002c1751100d030410356250001103605001c0e940c1580c0034402804001118032100000e400600045d034081c2c1201c3c10350f0f2a0003016034064980420034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 78402411 1250 78401161 78401171
    0x60608060c030c0a0c0209040605150f0607020d0203070b040308030a051e0a200a0f02011b0c0209040f2108180c0f0612090c1503010b070201110c090f06030f01 70
    0x4107800e080d09032904a00d49400550755400a250192908540c40c1e4000b908010800f081009208140e44903070710411703000c0214000c0700070304010481103601800460b540716009110344005401c1c000f607148100c0d88050202c80070b49442e01c02c00190707034005078001c0307a80c070600104204c1154054080c81e90822485e00080307044076980d0220040001004010b0303900156a40e1003084a411080d1410754011011454a03544040a001c001c01c0880300410180242d82000603113185980540c1c01c9201d040c642d5980c0c645030302a1a801c020300080f01520565041140100746004688061003038903c40c1d400401114080e440b2402c05040140002c040310790040c66090f5006c1c41e1100400d089080650441d290001c810341c0d0000603606000d562400300c10b60305280308200d2500400a05003100c5202140c0010f0a0f841f8440101d4440c4800d00410301d0341e88080c4000f0005500860090203506001010b40c0e4a9003e084041041e0940482e04480030521140500405007014801252885540002840 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 78403661 1250 78402411 78402421
    0x140d0c170a0c0b04080301090c0c08030a0c111005100506030603060402010e03011e091a04080406030f0f140403080a0e190204060317120c0c0615010201062106060806 73
    0x410840340040303040366000c000800d10001445000045415640404441014145070601c81003603002400781342c944528204901d001c442c000e030080440140e220881502d10354406000c03030050242d41d0340300801c2c0010b041403110a03010a2111326421035205100199625005080080b504070540c88140124070820911959031800300321164031a8082c20003041340c440f0040801e00400040010480042e50518110f003800d1480c5c0000500c1b600643c007000241401e010440701007141601d004000013010401003121034004d40040d00c08250180300050b06064405284060340c0043d0446100800614100810145c01040e07a40d0815000c040170401400c6c1c4000c00350b6030b00b0502d404d2904e49603c0500300c1d400c5503200e820040241d80d105040c28034180d000c008203490b98014002d4260f002e2890750014840c130004000303440d80100440300401180d01c803d880040728800e166040703030455403110b201060404d260902d01a090405260200707845d00035052030001c440d140d4001c100213402c07460501c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 78404911 1250 78403661 78403673
    0x302010218011b030c050c060409090c080f03040314030721020f011503060902040f0608240601080408070501090b090c0a0806010b030103021306080607030b030f0604171305030703140d0c 82
    0x12079040d030500300901750000c00d0402900d444071380801c0740d522140009010681c4a0b42e40c20125000341f0a20303041458684481103107441343c0713400c04002d040d5441844200085a403c0102c1c0c0d410114000942c1e06d0f02045850300d91031078424400101144507482c3d410300250364100b0001201c040e1043c001c01031080c2c201c0501860348614480500407580301d494007003d540d900c2c2c1c415800300450490820070140e4030004951642002170015900d40f0001b007103c1a50b0030444426845440141d41c1c2d012039548179a0760a0702e680040d40c007030f60959a0360701da510003d030054400d14003d10030700c0b0040c103019084100f0440d680c2203a4008461503000340f80100803507040a41600c0c19203604a808003900c1d17030003000410045c1031641c004203c0e8407454040c004481e8055024001c2041e00740e0a8400d62041d00220315503a0400f541c00402282c43c4e0706618a501c0341440c06001c03003010b04a80020000d580b0400130b4a03064031500140c03001d08004407a945403002c100606036800045041c00300c00704d02561945 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 78406161 1250 78404911 78404957
    0x403021806090a0f060803040e010e13020603040201120932030f09040509160b04060924030209030312040b1e070c02040b0103090f1406070903050a0f0c030b0103030201021801 77
    0x900f940940342c00c2c2e08190b00b91590800005041c10310b080702d4031180d407402d407a4941042807040308003840c00d07803010401c0098802e00c0100041c2d0040e040d5171560f01c070b40e4011900c030359405040141d4583d95800003400900300c0f0421100030901c8426003140802c180050400f14460075003200c80560003002070340c03041c100303204c2910949401100d0000d4a50b5032009e0440c00c0c144a0032202c4d03030340c11080c280400e00e202054050402e90305290789241e001360702c80e5910180d8441c0b599403240908403034180071164a119800801c103452010703060300c0c20800302c180d01d4840140c3c1035034115810000c1a04001020108800c4200303524814440c40e501402c05002c003920750801240040d0080b51208a01d6007264001e800c4641c8481d4010700348240741c10b55003800c10300d541c001e08285096009102c04192080c0c40f41910100f520b801c81f01074403051003290f07154404000490070866411040000001c0814103104c9454020740c001d07000076075a03010207820600c41007450a20141480000c102050416102d600a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 78407411 1250 78406161 78406171
    0x4030801050607050c1903240b0105040501080a0c03180b010815070804080904110301080d031a21010603020411120609130f030207090c051305040207021f12050c040302180609 77
    0x1038102d1300f424582510004401e0f54001600c03a100b64000f985022170301140305d40780d03030a0400d0204509d103900401151a4842c6d40f06580c0080d1000c004145004840d6002d076610702c2d0503040000d0418000040c055084407181416250b00000c0001000424024000f01e0382c501ca6000c10450586880d2074040c0140ac0d000e000904044000704c0c0d80585521035a00500202d4040344841e5140d6940d88106541e82c1128500780d80000d0404158001138a500c00c1c100700c0e40310303008150080829000d00761955194103103049203090340d2261030004c00340c1c907240b01d4041554024202240c0e1246160801c09610707601070041c1d40038042420070411080d034020101e92440d680104072540c030300b00d0f506040f45419401d4101580f030714908100f600c0c440d0b8101000303000106510a102c0182940c5108000c2240140d100c065000880601c00007803018403514240d00c0f40c0d1050170701401c0340e00c110100d03004a0344100c0341c0540d441c800240c18015031030f08040110210700100310080e00c130b24090004c141501c00285c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 78408661 1250 78407411 78407419
    0x3060906320901030c0303120501081207080f030c09120703110609181611060c030c090a0306050114210c010503060d021306170d0203040302010c02040b06070b04030801050607050c 79
    0x81409540404841c0000185402031124250f941c4030309105102485902c411070201720041c40c440c03120311245c000c5a0490b0640e4028020f5a1140000c6500f1030f440024111115281082054203072241321000d14000c400d04622561145080d005016076980d900b0380c00c484591220408000068680108100141d030036114607841d29000400318901c0c3c00c4100c0d083c13681c0b00003502080309030507203401800102c8001d940c8404590000103209074075a2002c4d11f0380042c50104000280a04000800510503031501400b4210503030b40d0381d200d110481e1002c0c1c10550340310207800c0700d0a0091a2641280415030385414145d00c803401b952181d56510800d86103410b060000200004615594a20501100701e4000c0c0c1004800d840e1403079240010301550240000039002802c0040e1406000900500403054640040d441d160a5800540759010718030302c200c2e8450f440d80d0000885403265806030070610301c1005403070411b007024036018100c07003070580000d401058144070540c080740c0001101c0100400a1b6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 78409911 1250 78408661 78408719
    0x6041805060a0f0e01020307030c020d05090d0b04050f061302010f36050a030303090c09200c100207050a0210020318130209030f03130503060103030504060f120c020a0303060906 78
    0x4401c0d0103031001c1044d81245500c0401046801da8150b0412801c071209582079815400512405031034030701503141e5580c0c0107641d0f42100c00016071015610707900503001e4003c440544002d501c9181c505001150800b500c003221608071011540c00c0050480c80464a0520025420700200d001000c100340d050b00c0c40c014204809140b2240800e480a1405405e000d85440361031900c9040103405000000c10441c1d20010800300094010094811034045048441c0690031402c10000d007581140c01c1055079501a0048804a4035103600300c0c40100074062107000030f03242032646401008030b01d00e240106241550403c10121210206104280a41d1720b4221b1300d04903a002e801001100038060b914456406102c2c9580d2600342c4c280c000080c1642140f214090841d2a4642c000c5c9901c2e09820f110081c04250306000a10905019850103510101a4503010f005503c1206164042e6410300081c50050b0f0005401d000c28035034135015200c050720394000103010041c9017002081a400c08403042c07401080e006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 78411161 1250 78409911 78409931
    0x90812090d0c0306020f12060d0b010b070602040e101d150d0302070302032506032306030c03070f140103020304050d0c020a17030a03050603010c090302240d0506041805060a 76
    0x4500b0340d0055a00102d045445582407041030708254407240074408000c054400040c61450700d100e2014036240e01400d294080d07460544a40c009801a00003107030919000d00011422103110203c2d540704012410140100500d04074804050381c2c821003002104066440c10018000301c00201001c040c1000d4501e00129496030800724201409900025414015040801114051011100d0100c0710018204c040c06a0343c08013501214003100d00d4202180300c04001c1301280101c8580c240c1d0046001d0f00756441107131110700080c10444a03402205050b0903c400c14010300d48506140d0325050801c3c20700314554100b0b0b403203465440d02081215810000200303284811500c8440446000304850001070b0001c50030f01c40491f440c1d400c000d03601c0000a10f0080000c080c1e00e01405500c80001c219200c8038030444c01c54007031000a095060002143c441142c1d5800b2a00120308001d143d047d140c02000221420250308100035540040006150301d992689501c000c00c8012600c0340c1c01500451000440d01aa = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 78412411 1250 78411161 78411173
    0x270601110106080606030d09140405101203030507080610170c0910110c040b1818160e0912040e060f0409030302070c051e0103180206040312090812090d 67
    0x1a1003169a55400c0c190000751403840000c80300d020341030440c240c6440c40324010040351582c1052044034814024004500300e182050b60141c3c3e0000e18103490400780584a502908416025400403400207a4600801005603480f0568940149007110070141483c10f10744018240b203280300454420461402c007003042c84024000f114a0120068501d000c011502031014011209510802d0124050344080095030b160501c90184c804500900300c149200c50f03030340f40801a100040500a03c01d03403c444107080d1002c1080020b100c0d101040701c0c140d10504240744a0300240e4081c01c2c02e40242d1045078560f0000802609441c00e48070f02004030b0244d5605c10001032110340555480c103030091b2a20754240e0915038980c0042250a001f100c40380302c00c542d60b20902486ca41030008503400070308102890340c242e601c26041103211031401d038481d198590142d00014460b5226510403a070940050002c1c440300754000c0d84070b900603d8035501401c164000d0341070b101c0007803081007a403601c6242100000010811 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 78413661 1250 78412411 78412427
    0x709050c120c030f070203040f060e0a050406090207020a0906050105030c030a15030c060806010212180609090109060510032306030f070b030601031118010f050c0313030b06270601 79
    0x10000418803818105180b040c645603005680c4107483c0d0220300c00291000c0d000004603002c90303034003054a141c883c0c50100d003102c4019069401c075030302954000740041c10340e0b5070f0301991016065819006035201c0091040261500995000426481c2401c03810000b45e80c00c441981d82c007640585040d07a0b613a80392104c000c01004190108a003c0791034010100602c40250700f01c000743c90480d00d030000b060300c4220040e42d81e0200e10b9200130050f50108407020b029000003244600e08000544271504055805c2c00090201800760001c00f21150384000402071490070f0000000198214182040784c0341d40c0c10050303610b8600c5841c0580a060107400402c4081c0c078200218030070442c06000752901c050719090812855030098cc0c3e0140040d042032454588464000c040710002504c81420110f448500e000644442c011395a19000344542404220800c40080c801490001081410500e40c14114a4815610000a04464003032482c01d22445402c60502c1483c0304150201144111030341d0f00c6800407654a6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 78414911 1250 78413661 78413677
    0x80703020103020903030d02030f10081542010305160801050d02011b030c060608032109070f06020a020324060409020f061204150c02250302040509030d05010f06020709050c 76
    0x144008204a090381104ac1a00c2c01080e00030040700e00380d0342e5040303056512507921990804000c064008101c004480b90703d0301e50421003000b0890071030346d003845246030040c00c0104081802c3d02600030703c00456900d440346650202d55041090030740d03001c4000c0280441014000d40b40034140359440394056a0050035042100c580300c0b42840d102c071300d803480c0081160101d03050440b800303800d085000c1a440f1012054600c5c01c091400c075691040c00d010f00c45290004d0140080015001d81c02003c41d0241e00e1078141c001820781da8004003250034591042c10720344203070980302c0c003400400d10280031000c243d070b5000540c11200c01c5902280f19007183c00015250f401c910900e41d88880009141d8448d48001c03c0d60500c00c03401a4030340014849001e5920341540d0343d1016090041c0c2042444030100c281180c00034144240640071401402c0c1c80c1d0740444c0c100c90b41551400c4055001142210b20303086540246805040f00702c51000b80d4a14100001c0e58800d2075008484400f5110380015118241c1c44c0c054810030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 78416161 1250 78414911 78414937
    0x5220f060902280b03070f0c021f02070e0109050112020402031509160e0d050a0209130c0608010806130512090d060f09140c0a0b0a020a05010507080a0f0608070302010302090303 78
    0x24055403c1c0340d410b540229148503a010106480000310450b501003920301c41c08503620b440c040381c080701c0401c880310301402101b01d031302c4204015103510030000c0c00d41110000c456034000303004860a004001c80d4411050303104005840c10503006000c512901620401060b605840160712521410b40d09040d40105007c1241c00009040800c1010803030b0801380300ba44289074584669204214080c4840806440000360007548542c0240c4014145031040650141401e4400000c01010340d41e9911034050590005001a17a040d0060001d200144040c0e40c100f60200c080307041009850303981d1034131000042c800c2c0c481c0f400042200034042d2100f04010380c040b0b600c113200b000044005002103004002540090f1070b01603009103500f03080c807000580e01ca0241d2004216001c030500d4000001c80030b41c420b880007821401548402c41c0010024018603004059a45640c100d5160100c25001111041031000181e1030908000700117409021444905030f80d020710b00541c1c2d50018002192551090388851030700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 78417267 1106 78416161 78416179
    0xc050c2d09010b092101090501091a0402091b040803040902120106081909080702060309010b010e0102031309020c0a08070305041e031e020a1a07050105220f060902 72
    0x10035281c05c0c641007803c400f01d0201d103007521503440085034542e448440340c0781048001c564600a2052203041070011340342c550000340c004400508100c40c0c1e0181c90601036082e00c1c2600488000d818804210f9903120b5455102e08000d500c0307a00b8680c4c0c2d00c0b100c10b0010480912038040d640c06802d0711081c1c002603c150150020040003110300407520007404000500060700d40901852142d0031410001500b48914070006d40070007032000403117045400070024280c02c00a00410081960121840142c80d090740600352440d000380008050261f15002c5a01010541c2c400010401d035100c1142040181c0140203a940c5441131501000f0305501200e8000340c0e003000c4d1024000030090000b09440ea003e80e60760340b5241c60241c7ca4000307000c0f02000142e0101401400d000c0c2940006100310301c081c07595014511042c4e11402c002d401001460051910001c0c03000d0350f00045900781e0018104a2 = true := by decide +kernel

theorem cover : BRFrame.Cov 78237411 78417267 := by
  have h0 := BRFrame.cov_init 78237411
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78237411 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 78237411 ≤ n) (h2 : n < 78417267) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
