-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1203
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:44:54.116833+00:00
-- url     : https://prove2.me/submissions/e0e50b42-673c-4a2e-8d2f-cf96b7d9b417

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 216187050 ≤ n < 216366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 216188300 1250 216187050 216187067
    0x204030b1e07020d0807050903010b0a0b0309250e04020a0b070804032102060f100503031809100e07140702090907030b0c0405093403020d110c0303150f10 68
    0x20484402400740e26481c2e4126070394044e41910601003011000480c0900340924040e000246e40100089840680c0e24003003801c807016503020071034030800441030180103802400300700840400728a10041c1007407891888400304809108040100b80c2580c04030b010f548903c030801e0301800300410003d035160503034035000350f05034054801a6224410606031416112044c0c250302203d0302254000c1560751140300d90000340481c050403551070181e20302c6000419440501c00762813411541c010400340024404148060404002c0a00c2c03141000c001040c000411090402608500b80386411040e5030203200c5c0d2440d1038850fa000c040d50001d0709178200a5030b1000040c00e034003628840d203203500190b01e031492441600d000d14040c841d88003407544000303400a040c01010001440c44d1a0711091f5445030883c107903c011008140140000340c0000c1d002c521030340036000f0a100e0034844c1c0b800c680b03800c246c0c0030001e07160301019203c0d181f400303521900c0b1025075075110726681100380700030807290f6003001c0141c010b0680103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 216189550 1250 216188300 216188341
    0x3071e11120906181c0303020c150112140307021e01031416050c030f0301030311070b040b090415090f0204170c060703050f070f08090405180c040f0204030b 69
    0x400c40c0d0700c0c07070018060401a42c0d41a07101034011410b00c00d03c4104441c1c0042d102c038040c1d4110740382d40e900d150102c2407030718002c600600039100141d6800b103207280c4504020a000b4041e094140c250010010b04a01c2800c045255410605141140d81141040d80c1148a600e030b010794000400000103a102080072034400e8503030030981301000800c81014101041400890340240f4a04500d20000e1440f80200010001c00303091806480c64500c100c40d40c0580ea0304280c10a4000561902d40800344601c00c00c14031b405405004c00741801d0510300b000e01c0219215103540c05010f90b4480407040e5a07821030342c6801020345040042486045180090b0800a4104d0700c10078500c44200c200840340100301280c0410b12075800382c6200e180641035102a14584c0c00001c3d4400c0e102010069000811103088082900f03620515416650f08007240401043e540d0107010401c8402520f000580c2c50384002943d0021603500340d4003c202500300c0c0c0d01c0d4400a010b150f1001c3c3c9070460520801c40d60020403000c804008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 216190800 1250 216189550 216189553
    0x80f04060206060301060807140102190606030b01090506060414030a06091421040311061201080a060e0606030706180b040e07030c0203030c0a0c1103010c0806100e0a0b03071e11 78
    0xd0382c0d80c0f0101400d8803c03600c45d6008a41203203805101804c2040c112070103003403041c0110744003140d03200b01c50305032100060301c241c40003540c6180c00c2c01003100c03500155004110b5840248800d05242c00003480d107110701e2080400c14141411a080640c13014800d0b04006070300f001c42004259414200700010200c040301c00c20b2503005114032a144803c0700001c4c030807014468a16581040c2c00c0da540e012041c40e840031140c0d808002800300001c0040f81544450180c40c0d06000343c40482014501601030311038a1080c880c682e00004200040c0b5140050041e0445030030b45030040d0682d03411082c1000085d81034002c1440396900060215080c0030350422640503101d103a40801007603900c1d010890b101d000075075444e90514002c02120202c0703032240072230048403405030000032003046210000030700f180d641d802503070049400903080111a150420203114050b0190810846031490780300050480d482601880c00a541d02101045500d440781e025100c1c0d140000b840c03c28400e4056001400b061032085038100325 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 216192050 1250 216190800 216190813
    0x50601090923100308030c0313170c0d05030c030609061c140601090603051b21060709170309040e0c10020a0605100b03180a0203101a0d0b04020d0f080f040602 70
    0x30098501c6180c0b0403217070030402c080d0560300c8203032021917294009003496000c24182001100810101c404d8403a41c0400030110950381d01c135565103641013119442c0e00400b440420b10410008031520402c0300d500c150211120030059840301c00155a20b04003881c0d01c0801d003010030511081152188003070312402c41ca241112410ba0740c818961081d1412030000a000741c12139941501d41c58000da0740c074200020000d0170960004001e06c80c0203484400d0105000032a40b02d80c0603c2102ca400c80d620740d02828181c08003100461080b10400d5032441003503007050159039101c6c00c0201d1041300340002e07541e00c07000801c0c0c0100c40c03604140c02541d400b110070003a9121850b14012480c0f040d82402401c0c00c94900d50728042c15a50b0f0500c5042c0030000c0c1b4611076a690080043e40001640c0c103100840c400040784070000742498460071200785040c0364081040c01382402c41c1c4c44102140c10003068a0b8416811140288051080e00e001c81440d912030320028103000300421389000b910003480140c0192452030b401c40700c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 216193300 1250 216192050 216192061
    0x60b21010e07090302121002180108090d0f0f110109080a021005010e040807080c010f0c021506030309190b03010801050a0e150601140f040b0702090702070e0a050601090923 76
    0x1401100341c2ea06000b1565502003000182810502c04500b00030007411356041c50400684a01603902180311111400c4400000c00c45960300000100d07004076203c0c1c010514280804006001501101520b00c14080451007940c00140b08034149254562520000c0c40071a0441c64603016940010504e000980076440400c10110254803515040780d00c0c14000d080b0985039515440142c1d40814416a202a010040c5810400090007040c030704032481500000d900f1240c0d07000a0418021070706102c1000303440e0050020542d0004191000c02004031111050300b0114540000d00300020703413200b0510a000320000600010641c419889003100c11418030884400300d02282c0c482d2072008044070340411004c04500716500c2500d2400044d03a600c4e07035503403800d034034044140066006540822052140014200210304140c914540c11220034002044500e041420020240300700410603442a42c0d07130400104142c0c800c1c5241401015003030410031500b100946a01003d40c04c0c0d065030310312454810041207 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 216194550 1250 216193300 216193319
    0x50a0b01080420040905030c0a03080a021c050c07120f14030103120c030201020405030106081e071206150302090a0911060c25030506010b0a0305010e041e06060b2101 73
    0x1449607038401204103200640c141c40b020b20a180e20f0305207801550301d40e174090000307508100070291524518002c4c000721090307160007840391000030540b0aa0320300502202200648000c0c64600d4070103440c2c000f04265450400162a5002d100000790100001c2c03010341c44480d400244400101200b41e4490741071180c07403150030082c4d210a20004023403d0106c802d240c5540c0c8240c4800119034800d1001514083e95100000e081d25a184c00c010300a401103803502040700b201c80c1003100b200c4c1c83e810260500702d240610b825204c4009280240070f09407241d81150528120302003401c00746a0003007010f407242c2445c2131810004c1ca07403440c0c103e036841c0190205501e90324154003552043c1881d400140031000032400e088501c01100300351040c40c03280e03080022000440034000760f03000e0446101c0030768503000c101c2c2000b001d1304c0042e0310207000701040703000340000304080c0140005041c48100030715850b0441c601d4030000501240d840034005d0000401c0070400e260100b4400d441003002d00120000030398a809100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 216195800 1250 216194550 216194567
    0x110703020f0402071407060306180603020d120201020706020a0806040f060807050d0606050d03111011040302060f0903061906060201140a15031403130e04030206040b150310050a0b01 80
    0xa0351084940000485526094004020941c4150302d1030281c3c01880c10402d246c51503541000d0701280e201c8109120203e4406e001240150103114103120891864001c01c0f260340b641240038002d506c406440b01880c134001d4044070754581d849a001c565560380010700400100064a509108074200300c8081c0c40c481443c0522802c0e105940301a0405600d84030400080b58030300c90301240e90380c0e1901ea00085507560540c0740c6400342d0082e111500c04c10818901c01c2d0801101c104900e500a190a20304021311000c041030f902902d81c1543c07455542e240084000186000c1c1c00d61503036252040c03c04102d013a00812211020f00c5448000074000c140d04e40030241e0070396181c120380c4000e9032401c20000f0880c0c011038100070f180d01448044204125281c1d140d900d200040e0901da020749901c001740790443c580c481000500141742c0e558a822081c1041d50700292201c60241002c1c010705541004654010b1080c01c859031030a800034100c9140001804650300682402c1b40e40c610001d107410481d118650017104034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 216197050 1250 216195800 216195803
    0x17010501020105070f0e0111010e06010302040b0603010e0a02072d0b0114010c02040207020a1a03011505070302060a0914070306330b1c1113080102090a060e120303070f110703 77
    0x109101d0610b8105c00302c40013250850118100020034081d04003400080c422503611000042c0601915811401403205a81d401c1c880d183c010101000100070404032090f10b641c000c6180e09002d030381d5041c1401d000205180d440c1c112642d00c03540884800201d00242c00c44c1e540a44244013510403070380d0b50405d03462035048408040b030114411101290062030b0941c02860380510087c0701a040f0b0361520001000031920031180074185d00004010701a0490240d1440000400d0346405843c080c9079940080d110680681103100300340d210040507040001d00680380d02c40d81441011511220354908000300544004001d030b2000a01c95015018030621052900800c400344c00a07c0030b00520f4600c080e2282c1c0d100c06550f806100524034002070002e0b05000745210781c502f1209054540308050690030415003641e000042c1a8410040b080d80c0340c03600303403019003101c400c2e00b00b001c2c088151501142e2682640c000842c0240000000c0103020342c0c101d030040410b40380c240c0d80e0405201d0b13091500ba80e5848035020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 216198300 1250 216197050 216197057
    0x12030e0307052101060f0f0f050604030309031b05030609010920030c010c05190311010f09150209042a090e010501080f06040b0a0801050618040b04060e0f0604031701050102010507 79
    0x8000983c41c070305040c00c1c20000400002a0442d503172903d0a807009140d4009020b4403141d200c040082500100c0e060703001d002c0864034a4038051942d600600a07031030622000303080a011703a80c60010b00c84007e0020000340005400d4070014589108041d0003030903486000c070394030320302140b03c00e07041c03464143e590007480c4000d0006d12003581040d0042d20041020141159248500b140562000040c2c400c0655058402d8585503412247c0316016030a4034a4880c80c420104d14124020000c00d80d811a98200501e441f1030050341c540008000c500501800c5d81314001c040018020311101c84006101040291300c01e0f03440003481e5464801d044400c00080c4202c1c2d000859001c0401c2c01209110b0701c1c00d41100c0001c00000e41700c50560046507440382c6c19444000c4a96446042202e02c9c20702c0500c0440f070410a0039885443c1c5400d40d03c02800c0342d0003810103050b1681d503aa07051500340c0c041218541c500400022074030302d4540780c42c008015410b8bc00c042c6203010030080c0002a0b42d401405014002c042c45c2d00e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 216199550 1250 216198300 216198319
    0xc1808071a0d06030302150f0f04080a020a0209040c0305072405030709031202060709060c020d0b0417030c03100603020a08060907120e010e013c140112030e030705 72
    0x400351110119014800c1c00e0824041080c492407032202d10a003001188250007500031901c2401400361030342402880f5002d00b501807410000c1c107041c12504180d00c036a00040d46600c0300003013202203150015400c00250010301c0340050000303100040f02e00004591007102224200740d1500c0d81641d404000789c0d4882502038010746111041802000999804002450500305282d40c0f03031111180807034088481000741c4c118606120b240c0d6880ba40c250068000e50600d0005110540d001c290351844c05200a0410140c0c10046030411031340c405da812980300200190341c0c582c20101446422a4030030f40d1115003070703000c400300010401c1c080e000f6187d4911958a804295980e4401408480c020040c5910208903201917038103c448007a12030060800001c400000c0d1140310500b000b030844081c240b0401d000c002200c2c40090201c41c03214a40d904a007429a0020745000000b40d5101400489090454441d407030b100120365800b10480e54140725020344c0d949589001c3d0002415101d101c3e5000d61500418143e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 216200800 1250 216199550 216199559
    0x60f060f1605030d0f0207031d03030f0304140a080a020106080c0d0f02042702010e0a050a06140702130504030e0a0e010909050a0203070603051b0a02060f040809090a0c180807 77
    0x484103070a0a030049082c0d9142c100d10450300c40403902d150301030241da1940442c401d41490361080900101074086484076505042c6040000c1d901d02900800701c0580700c001000a08000002036440004c5034851300315200e0b66401c0c54440d960380c1100402c20010340c42d1180c00214030800080d940346408001e8804032050916442d11154441c0008050746c08c46e440301c44501d0701103910914203844002030180326100f203003180300040c0b841614a20b090302c40c4803400070900042d40d5000104049401d03034102201c1d20542440004820300403600041e41c48801008042d0f03255405402445c8244d2091399031580c01d800c9002081101d180900070440280d44800c01400701062603840b14031a2401403049800039010307980000c2c03400819800100002c0c3d214024410b40d85200c2d0786c5c40401c40d1104800381d040000c07041000b50f030ba040050824141e04070010116082c020500221416440090310401c00c614020030f0050240c503030f8408010000304140c42c004a42e4030070303a8503101500c188801421155182 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 216202050 1250 216200800 216200827
    0x2405030601110309100801050406060314060f0a12051b1c170403140d080702150609150d0506010e01050301150302060a030b060d1a0a120b0c190305060f060f 69
    0x40500920b4640300c10014031905a65400641c1d500340c3d00b40d9511051581840b0034802501c585500401c145410000400080d0b9080400c40da4040c130103641100d5131245900000d040050250310210383c0c1e40305617444500707011001c41c111490551a0200c03517441c02098007071000c0c50086100340d00b0900d0a0302824800a8030944044240c203c099a0380ca040c03945a44075440e01c0e20003511400020703403001d041c0710006601b05500c9130b0320000390f002404c6121110061050101d0b401440c851044020300e00003008494040240303c040f10008d020b90201005c589000703565500203014010141c0b500e440001041d1405000302141c03030074990f1085480300d00e16402e011a54005181034814141c444918111130345422014010700924100049005600704240301c600c48000c01b40d5a000c0d105900c81803143d803819080ca80740319503001002201ca40c4c0e80b0102002e41d07020b041d1003500b00d080481c7c41c03047c3e010b0f41a00041e01452086070040520140041001460310030284030018000040c403001a03d01e04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 216203300 1250 216202050 216202067
    0x8060105160c0f090f0501061b08090109030b1501021606020307031b060c051c090f0f02030c0a0f17030c071503110304061d07050a15030b0904030203042405030601 72
    0x1160006081c0d042d20395140000c0503003680c101c1c8584035501c0140917500c00c00e6010300e600401c03203030400b04240c00b00312156800c20f03010110043c082101c00517544450f0f03440340e40c03014015a0070000e0502c00c0d003041003040c140505a07500304e42c0144254044041d6100a030b44140080b1a001d40080d490241550740640d044181400d4000618180b07100c141301140d078602800600c60f12a82c0c030656a2121103a08001d842c1c5040814501d130b51500746410700141e1850034140c811a08104002400c1802e403000a180291101d1000d4021094080c0081c411071106001016507a110540f4000c0b00b40b45101c50350399004442444c8842d0703000c107004000100039821042a40c0710725150200e403c04240d00d40c0111523005803000c41d115551404190941080c18980d4a030140d00c41d8003500d6094a02000075111111034007625a498100e001c1c50344071a4020347c82010f506c1000741c100555480d0500300a03446c0d40003441a45080f09041145502c144e94200e555140d10049441e0142503445041c01105e0051 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 216204550 1250 216203300 216203303
    0xb062502060705060709080a050304030b091609050105030706142b05090c010813020906100e040e010203010602150f0103030e0d0510090302070602150f061c0f02010305070806010516 80
    0x50821211409621241c0040900c1800340300107103030324101a500249440400c1d400f00ea00d681000b0101e40000c3c402104840850340c2014041985031201a001814019000104600035800242c002514a1a50040c40c120f4500710103440c162a60344605a0b88202c48408000c9001c0d0200b000110086a0030b8035024030101104883e0310b00d0b404030303004074200c80c420384111500b5809803079000550b40e0300c500c100341e0051400d8841440340c041076000c14400307140a406688a540c0100282140c80e1240300360800040e4010301c148601c40c013100340f5600030b41c801e01985006015400750540031159100e4035500407201c504088805a2940c0c404540000c0c40540d03407170780301e002c207502540498400c00050b8840c6840d1600001c2001071860081d1502456034440002d41d0081c0c0204600c2e80b40403110180c0c8800b0305020103e40c1da8134000041d900c11200381180c0848080456100240b1038864286c903074092013a2010001621542001c1d40e00719411510b0078005130080000415036144c0c01c18607154103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 216205800 1250 216204550 216204607
    0xe0c090a1a030607111905060a1d010213030203010f090203030d021804020409050f060103051009020c070b03010b070b06090c03010909020307031e1b05030a02190509070309060f0b06 80
    0x24501500007a00b403038415511600024050000081c2840060028004001c2c1101486c040140d01d940c83e241c6402c401440c2540c1c13070355200200c0c0c030115003600402d501c02c40807100031907446c1301d4880c03900d001107600e004c240d000350710f0030710b201100e00801d00c80d000030b461f0010002e41c101030390618000042d502c51107444a1180d101d1899000a403524000351002e020101400324030b520381036030b80c0400d90742d0061001e4105030500c0c0602001420b02c103051020358000180150f03440d24144109441c0a469038000c044c40c0b40000000180c05400780301400d6150f10a64040c2d0030780d00e8560030421805000d0781c2000d41001c041004020700a842c2d44403080961000d026900000e540e07856940c180441c811076951403c10310007002c02004640c02003848243e0611140400580c1404017283c2d4800b43d0050080c0242109594007820200c8042e00000030131004205052a1500300300080241040c10b100310780d214108075a130704021040c0c0c0a0a4913083e00a0000c03410f009061001014090003500f00c000d60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 216207050 1250 216205800 216205841
    0x81b0c0901090c0f02010b130b0a2621040b03061801090203060f1e01050c03070b0a0b10030207050c041505040609141008030f210405100e0c090a 64
    0x4980310381412600810420301d000904905458014098007144900b4508591404501610130340c3c451202c0810f80408500014aa02280010072182c8a503500300690105240c0010000d4403103500043d4480c1d59072800340c0d550301411000748084800d1396510f81c4031242e0140300600c824000c0c1c0020b143e1004c0000d00f002005100c5840300a81048203800c03050304a82c0000c01c10607541002d6038002940d50302903c040e0960311410000c00750401e8500b40c1c02d81080700c0015022004801001074a044980055402215003440480c140082107050b20650041440081c10054180a40700356000c0a07000380240500007103036003c1000400269401024046265401160070384507440303103402038401e070b40300040c0c1902084040039407a500240b68080c45240c03590103019031070010054031545450740e0b81107a00d4500e4220000c00c010141d0494090800082c0100030500ca00003910307601c3c500c0c1c10a000c01c40b00e00b94680903a128040c00990540005048010441426080d48001000180345809618 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 216208300 1250 216207050 216207073
    0x3070e06070606090b0a080304090e01020909150a0501030c1211040b12010e010803030405070314010b28080c031906020909010308130909020f1c140102070b01080a081b 74
    0x603039411460040d01e445660700340c14440b800c0c15100d400300030380d0101c9500340460b240000130303a038a100d5400340c000003607140e40c10808404030035010360f03090580050200311980340100241c03040c050340c400258440d00d058080011294024403c1e081005905c0d0f4070300c548035a82103118000f4010b18580500d1107942080000745944810003e090100b233000501032448d407400720004000d4406810407a120381040080c48005000003403a0300c00c03a80d0204004c10100b4041d605240188800e40c000768003c2100c1052029420781c902d449803240030a20320030055140c551184650710041c0c441c0c1142c06900c800d00660950094000b0140071a00c02c0304007501e414654008186e1420342030303108589a44010075400200e000d05e1213200301030004050308200400d01c64001070305031020445140d014049000b0140030720358910840044440c3c000080b20400220403a10f80c6c002e5100200035100c41e0380c810004034214001042c02c0300040c2e04210303140d0034060140042c2d044628142104c1c84070b03210f01c10302c904 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 216209550 1250 216208300 216208309
    0xc04060e010c05061f050604052206150503010504150303020c0d141b03070b070b0711150103050d1b05030f210a0903030509300904090c03020315010f090203070e 71
    0x6104100201628401c0c50b0300d84003082e510180c50301b01034030800091100744940e0700d40d89881c0f000c85c9282c1c1d5014500c002206070f502c0003040c8a810003810300d48207091041d0500c0e00400154100e40040d82c0c20400031090401c2c032200e43c07149000060058014401c4420b03503141016460320f540d40101590704e00144a6040240fa00ca413840c4c5442c1d040e080100d1802d91840c1c1840a00000c0100d202c81a20300101d55417180c0181380000c01d66011302100c47c080000007402003245006440311104d10b08059610be0070015526450a0358003800900790000450154400050349160b1941c4100114101007035209010a1600561105900035455408048548000300c504ea402000c900740005a002d6507400d005064400050024403c0da000300355105150180600102d240703801507424114030081e042119000748176803001d0b298000d0038070380ca1400740400e0701c140e202103e20840031209280340601c05521201424403c1052151441208108031f40903034004540c0254545001e40d1149140380008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 216210800 1250 216209550 216209563
    0x1e040b0402070f0c0501020f121303020d031d0409081b03090a0e01051509090a0b040216081908040515150907050c010606050405030706030207020d080c0f01060e0c04060e010c05 78
    0x43c1c41800b045400355050003121580300000c2d040130f102401814200f1403466940303228008840501e240005018626400c620310303000041c41d4000e11005945115080041101411080c2c2c03444180d05055442d0b00d03071500f0f100da04511584401802e007000c1403c2595240713003882e40240d007958002000340c0201c039070f264103c0c01b000d0b06040300690758650400e8107104040700000341405a0080c2000a5261940d91105184d40121400c038003040b03100002010401a014240000c4000d0064007410010400244081e041c810707031400c103411210700188011500072105031800b034181d800035110f031f07a1a0010904266800030044103544107501610340418244c0d0011190080014400b0034141e850050038080c0100400d8103281035800e103810080043d80301c5c0c21521400c030916134009030740411500c40203042085c1f1a044015940c40b031440d01070b495210b001c00c9000380610352034160b0102d045c1e0321106106024250b21403c50341020700309041510041150300301c10781489102013507100014002c0000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 216212050 1250 216210800 216210803
    0x1e03020904080a030c1b08070510020d061a0405090f0a0608100c02060a050606041721090108010b070c0504020304110907020708070b03040f03051c020a0302040608010509061e040b040207 82
    0x283d9240202a4020200e5807600c21040400c000751003d90300c4403130a000c0c0341c407041760800800e6584000c103241c0a0b1404846940983e0150300105004404107010360102080340e0b101ca030151164100300f082a00c492249024213503200b0751590108104410742c000700343d441044880c0c0005d010b070301da1603030318a854241701c5507049842d102e5205450055040c0049a000b03074541d0414000750420000049250296014044118496089041710f4076010443d84043c1c0719440c8264a61840c0351402d041c1941c045030390300c2c0c08036440000015100102c441218010340e000b414800d00c0e14286000c20010350310207070042d620340e040c0708110180795a85002c064050038680d002094400c0c98143c40d241052141d0740820310034001402048041814142e00d136401e1680351030300721f0361030030035103040303281003a5585001a080388041090b25080d0342680c005c100b03550880c1c03540c0c0750726a46e587c100416010200c0707165070030401285401c8542d0700c4410079248400070050010408146c00c10114080f070b00329080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 216213300 1250 216212050 216212063
    0x3030403051f0e0d0c200901120606080706080a02090a051c060b03150c0a031506020304030312020a0f0e060d09080702090c0310060f02030f1207030507090f1e03020904 74
    0xb081e0000c00a446548030340100d120242c0b84407500c240010746030103030b0303400090111014411640e08a040035401c0b50a680740060480d191035840740118802d8500c007030000c0300e0061034200c0100710b400340020031000710381681d0303141c803926590040e80602a420100704550050040c074008580c03603413a00b00d41101d01d0500f401644181085007048002d59a40995850080d00030040805010a0113070450380c0c02404c00142e0307550b661a0403422401052403041d00c100d440c0394100081841a030201c020400c0300e0203a03032501c035020009401c040c00c0f40b24a5000c000407403c00c00d43c45080a0040c6509104140300604032402c00207201c00c054140d501d001021a0295800282c5504520b4072801c040d401c0650440814214644192126503840c0940034010610007408100600a842001102ca01580442c84e898488484420351504101c2c280c6010001c01c0c1440c0000e40840e2141422a0442e9136141c0c14102710303450705000740c0481c10000102020001000d1002c405a2140e080c880c0c0980e1142c0c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 216214550 1250 216213300 216213343
    0xb0f0d020a110106050906010c3815011d0d0515070f0215062803120305010602010e0c01271703030906180607080a023705030405060112020303040305 66
    0x20782c42c0c1c21229941c10551003a2000e00c28403d0a03640407540281c0300b40d2006400b44a104824130110090110518070800c1c80400300000c405012038070107080c0034051514890700f0b440301c4c24006580d0316407403102c08142000e403840600f101c0d14004501c150001d00407000d40301840182c000b0305091090460702803000c100e1090321001000e504000314480c000c082c903030ac040203040a10000300c21194a08810054240084c62541c410040003000001141c0c03000d085103400464900c00350107020244180805035190106a20354200045403c00d04800141c0d11240183d500c0740c0b00302008250101540e000d00d804820100b803411135000850040120b0704011600c0c4e18200c042703507103050300040007608101055006120041030001d0f003d50801a40d06100ea160798130034025400034010920392a040c1c100900d0368902c10041284000c05111f0920900c0c003042d291500300340c51620056500405c0c43e440180108031401c940c1c1494074400c1d20040139285032550b40d4075114a85404c03885040303841c0100a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 216215800 1250 216214550 216214577
    0x9100e040e060709090501080a032d0903020a050306041a070e0a0902040e0c0a020316080715050106120b18040822050a1a07030f18080102040806100f0b0f0d020a 71
    0x2c0c1c110401001c0a640902147d03041002d5aa04c4451809000b8180301e00010b030140a40703040618210001d0002c411958618602140140b03007080902c01603000c0d0440c03590205460401241c145e101750303013002200b004d80503030440160100d200203101c85c0c03c0003000c80380042c16544065126000b440f402c1c00140e02c4600f804040c012402c8040c0405c071907140104003021602c0d801000756070b01c0055800401c40841580e0601c10020320400c94020000c4103460f00c0000e0402d8070340d1045068400d02c1e0380707211600c0c007407001e9442114440200b1a5020001d0b081c010261861100140e40c441d22480717089090a40445001046116190305a070171070700c8055042c00030b801c1501c0d00030700500503505911203142d8120050003240c824100050104a610f4019100480c000c41ca41412070464468001c3c0160b82d0b040c495000b908a401000740c9402408042000e441782c0507121002d40e405840c40344440b6185c611910002c1d8070101003c5410b51086c00005440110b40c801307000c030f220b000d0f10795001001d045c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 216217050 1250 216215800 216215807
    0xd0c05062701030903020a12090b030406021b073602030403050a080903070c0e07090302060408010623060f07031b0b011701110a0c03030e010e0a14010902010509100e040e0607 77
    0x122403260b041514100516020a500254030100982c000c0109503c0c054101011100441d8a40100606a00000070300080182544c000c2c00001c255070042c2800b9000390400b551a8601840348a0440781020100344110580094255200c0200d660a06030907170250020000d0f42c008981c00e6020400c04105d000c1c2d06a040007a42d9030124030000998500f150a54540c20392004600504d20003019030800116001d00411070079000d182c008011545855690709101c0c041c013440e000340100b8800200c000050310804034484120810010412400c0c40c0c03a10002010681100342c0607801c000205088800c1050451110524180036450070011981070004007003071540c00032440c000681c9055042003401a1101c01d44003d8249894800700c5003c85080480140c09106042a9503501c4c01d5aa01d00704840003442081c00303407140000620080c4e041000314200c9480c1036020340801c0003000032038040d1074011b07880700449060f0b00300503070082185c0f80406c0844d6180c803400c16007540500d040c071001580 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 216218300 1250 216217050 216217117
    0x3090209101809050a050703050615030705150306240414030609150907180506030105160e01120f0c020a0308090102040302010903080f221e060c020d0c0506 69
    0x344402040e907030314a40307000c01d81c480c200304040021803960703030a0420801c4803c1c0403092070640c0090403030380c03040c3d180e003000c6403101d00a07200300c0104030020f20100c07000c0c1000724041045a4000301050300501484490b04940da100401c91ba51001c035518881146544045100006085811840d900c0703a040c4012a211440000c66440c03190b4400d00400c40005d0001031011603641a8165503e066140c02c10694030b40200d6400001c0b900340b12041504070740c1d40c181c0c000c130701c200c45c00c900910258960644908244500c128000001038000e15171a809502968a0310b590340c070f840030001551890040c00c0d8040340d045030001d80044c4c04c4141c58005255100e94050341102a640003146130520750350001c0c0402c0314521004141200105280c0301c140741010981d61003032040803550100b10002d01c40850030381e199000f02c40007442075107050080c2caa10300d8041c6094070402d440b040290b2029400b002502c49070a00111160341c20303c0404070b032546622001e0841c44202142407550b40d210000b40c18003440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 216219550 1250 216218300 216218311
    0x2160515010504050103150b030c030d02030d0b120327060c010b01090b09131a0306130317010b1204021f031406040e0304170102090406030b0108160803090f040e06010603090209 78
    0x10b0401d40144041200601c1000d1f40902c4031720001071841c060808a42004401120b055042c01240b15000c0f9032078000c0000c20705aa039504c2c1c00c00004800a08001c504406441803010940c01448010012180205a48401d84844106080c1d41403000000b40c043d511661610400d40d458114030092035070030041d0b010162414a07429070a081c0342ca400f05005802d259811809241c8900c2c1074020b203921048090300054000c0c0640d441440c0000810001802025084000a1920300da0f10810b40303000c1e5459050321b181c070241c0303481d182248180a44030f038400f40080e030380b000940001001083c002c3c1114052800b407500c0108922600d011940031805008140078002d0f8109078040080394004000c80d07040d80c0c81141e00048941154041900a001c0c0005480d0028034003100401404011404079049440680450743ca154a06007000d00103d114464202030742c1c018001a5103920340354404401030000504001100e21036641a985000400c0e030048012983d511040c1081d4102907003810ba029 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 216220800 1250 216219550 216219559
    0xc13120f05100507050d020904023a02070210030506120105040c080d030b0a030b0415050a090210030e120901030f06090509010b03060f0f100504090308061011030913021605150105 79
    0x2803a011384050031600c079841c1c2c0121210742c0091091800c0d501e9605580d8102040c80c42c200d84d183c41e00356582e4054444c020a80a0240d041516844c01d500b6402148c45095010b8400720301d030410000140c01400029003084e510059448410a00400901c20540308900505440e0b0031580f070314802600741010b00c400314040604001680c201621914010000c03a84c0c4081c141c1d040d9542c82c00e001401c403105119118070f80d0f00704024001c100c40e0b26000840801c0c0201c0312248441c0040600340c1c1200c0c0f8000c040e003c183c2001010005e807081d500b014058241d0181000f00e0300d10904a0024210b41e1190008480f1030b40d5007050184081c0240b090742d02040d0182d000380f62a0038581188261508010306a03000f811244001942014403800c4000c01440c0c0a0703c2802210304510340504246030490320b041c01040f080100340c4102e8410b08280d280701440c1130282d45410890000d010005405e071500200d51502040201015081d41c5242e00705980205d01030701d1b000003180e80301007921b07406034401d5209 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 216222050 1250 216220800 216220811
    0x21070f0207120b09010b0a08010b0312041d070e03030c071a12180a08041d060901060509211507020d0305270c0406060504081c080c13120f0510 63
    0x50800810050b030710383e048550803080e40d0303400d80c007540900700c0e80a1241c0c00c0100c0420005591205400c40f0540803000c4007a1001a101381400d20b4050240e0704c04ca032114581001c40c00001c00840020613086200e0740b0382038001e0a21040404d2641d84209d4074942c040e4408001040801d0702d403054100d482146500092a159082c0c0e00181c0441c030140002c00d50310b804402c44800307402d0400c1032400f11a400f0a216450300d85e02e1050700c18074610b681079038181841c40800071307076146401415181602d581d919181e0170100380310140010a960030240d4298000d1700c1c6138861100d001082801541420305040600301e19255000034201180c018a03507080c14100414041402018800304500d50700a0345254071888a08441500d07100c101d0344183d801c213141040104402c1da20000070000c1e10507040441c2d40712842c01d0f01c90081140360300300c0c50000642c1c400c041004030306600300805144030302017a0350101c1d940304d40e10302c0113a0302c0341e2000f01c900e00b9800038200c04110040c0503402ca484483c2c40104003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 216223300 1250 216222050 216222059
    0x18130b0424050f0315070e0904060c030b040b0603070e0a0306021303030239030319050306120304030506061c080f090925030507110304030f050105160e09040821070f0207 75
    0x2950305c8240390024000300c00c2c10000d4483e6104183c0211a9000204011518145030030680028401c1154480000342840d120082074240303802408081c8501074003945c13550380c540d46c1c12034518483c2000035034081e11000c4004041140c40c0090311001d8244541c50460034554500a0324020110304002038260384483d490600040030142c007039500002c00c02c0d8040320554500086d085205004048034110922031000305410342c0710002e548521004c0d01c1d0402019903e40000d603803405244001062644504002410b600300390007815040c012008200c0c0c00040302d6a40c1140c19000450006c2d0600008162079a051070719112158014080d0582d44108040001100381248855491032041c141c40f8800314145521800d810503c500c0c3d41415252a0340d01d903d03103202004c0405500341c0f0207608040204241c05180030203109284411b40310b041060700100103021900c41d000300140c1d86000180030781c0c04010346042d541c2d100e40b802111466010324200c1006400704050050f04021503202a80900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 216224550 1250 216223300 216223303
    0x5010c0e0d0c0b09270f070309080306100201060e01330203030718050423090c0618040f0c080405060106050f070816020a060f031118130b0424050f03 66
    0x1030701c070340b020041e503103911903400701701204040800c0c1c1380b035100500d00310b066590711814054002d03001040c28003980c6c0c035a0441103080c2c80340b487d0050090001040803c0107031800400c0080300c1c000f40e00001c200d0541d101c800d25a0341d082644483c00d0001884c0d5140f0008407020342040070070314161400c00c45503060450095890100500640c00d000e81450800c0c540d07a42401c80c90001d0200170002c2c88003c0c2405560303425001d8002d140c4001c400454040380c2c0c200004641c501c046540500906d00f000040c980c5503048007880507042c2e40041c2e03601b00030382018078980114290200d107a25a44864106031400d1407074070b41d059010300b04000c002d1202928001201089808680d0040c1000b6101d8006c0003003403602c2d0900c680000c2d80b1030202d05000494581064101d28013180c40e403002c05c90f40c03480c1c0d1002c0e4568400c040d602c1100c49403009201e515403400e80c09aa400300086000081d802c01200c000c2021503008800790242d040c0701c0c5250915050050010102401d0b040c0d41c0300240400840c0441d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 216225800 1250 216224550 216224573
    0x100b04140a020d0b03030d060e060d031b0c0806070507030e030a0201080112080c030703020f10050f04080a05090d061b03110304081b0d030c03050f190e0c04060305010c0e0d 76
    0x1074000d40c1c000610840c001d1a81e00456080303203008080e00e50700d500d40c03220080145150311030f003007003080120005216840d1441030407000640503100c001140000803c1c0340d4002885240841701d81d45200d901107400d210800c609031240b00c50307485280d945c0925082c05010150f070711042c03a00c81d501c00c01c400360051340d000c0001d40c1101c2c20361460f44904886858451403e02500f440044140700116030b25061590001d105042d905403074084d85c01a00300740403035000383c1c0c10841d4508542c0350034101180010300c2030740003408004414903119090046080006401d041000f40c282c40003500e03049601d100070101c1c08c494050010fd801c081001c081d104005411900005101134960303000030503035204180c0300000032000c0d0b0b0004030540e40148141ca0000d0002c1910340242c0c00000d2a02c0002002c0e10b071003141e034034001d604440c0c01c901c4180b150307074181010386a49c086074038030740c010003102c0c02440c2c480d4003c000140d4490300003c00c10b83c0600100801a6248203040b40c0300741c003800b4409002c00d10b91401d9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 216227050 1250 216225800 216225811
    0x102031006030203100812070209090d02030306010819140105041125050102040315050108070e010311121c0c050c0f06040603051f032001020609190c17100b0414 71
    0x544c0369584c420342c81c031800100d03501211030b0f402102081c0528a2040c0003d00000340708480c1101035458000e031481e40c03868540e0b54440984c0c01000401e03541d41c0192603040e80b218941500d43d1000c1d0b0044141070550348000b48106d1410b1400c00184410700e0036014501c5a50400c14880b42858850890b280075080032182d100054008050043c1c00d000080d0102c5001d9500101c556001504003883c92000700310901c203103400c5015159010942036003100840303048a030410400101d0722600703c1040b400075643d4410016501c82c9513003014114001a10341070311140e641c0c8034080c01d1001410030504166244a40034841e100c450b813040119034407403094805a1b44a803500041e10394407110149440c4060361315003016404003420010410251414030380255038a420742994a079000001a40c0e00d020903a01c1c0f80c1c15130014140620300d1009413145540050041100303204132543c0f20782100485800d01c0b802c0b08560029080d41048910714010030414090a413002c01c0520b141d01c944141c842000b401c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 216228300 1250 216227050 216227057
    0xa05060d1104020409061206150b0307030506120d0e12060402010801060807111603050c0f010e040b031903090f0b120403080a0914010b040609060302030a0b041704031209080102031006 81
    0x6080700b0707107407541514050001c5007820400319403a514078143d80c0018000494803c0c1c103202c120140f403c0c1c0c1541140458100442c102d04540f40d120041d03000c0c00006003c55000742c0c0d0042a9021003904000303102c5001c510b915a0900c01c4044028440f000c400c42c010120250f110700140310050340e101030207a046565030714200c8242e4949080441e01034441d1602c0342d4451082140b0065110031903415642220f115900300c550301c8203140c0501c0340e14500e000300d0b98080740042c2c52480950600d46c00217540282c0040c2030361803040101c4100511819200010750002e560f0100610084030380070f04c80303005824028448d0f402e284811183d8910103d00070001002c002c4070300c011400803241ca4006100e40355000300c180030680808440c0500130314040300814421820001e00003040200c9201e800107494025016056a1100b81c582d004030032070140045032884e0000341100101944400036001035886440300780300c1d45400020081c0380801c7c98002203002d034810402d03c9034400407001c03010300315202c508 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 216229550 1250 216228300 216228323
    0xe04020105071410050a05071d0301060305070e0f0705190e0109051c0b0c16140c060c0601031a0610200a03020309030d030c08040803101805040b0a05060d 68
    0x1004036228042c0110050461260803070b00e418201000c00c6603180c0c039040140820860307541600340402c0d00c0d002e0701d40b100490794650320700d81c54103035504556280384000340010070a42e0b9207545c0d01c0d1400c402e03944024000064581801100c2d4080803086420006901d403090030134540411034450307400d039540e0703d00c02d10101002000c0305034081c024050007001c00030414424806200400a1744202c10842107030480445800140c40f0140e40095945c2c008280b22180206a0260307204007506056085610640c410130583e9000d95071450020000c140000006d420b0343d514600d4803031084000880b07811503071900c0c1010000c80c0e403100703907540c0c1015400d0710f80100015510090f5030542a16200404058000d100d02941407540000090080d4101542110500403d0000032030460340e40104100000d4080d201090101e0b480c64080c44d049040200d190700e0840d921b441c07102403000c04000100d001034171502044188036085d00400e904c800d20140c24007551030030800045401e07040f040c2c01400c40320740d071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 216230800 1250 216229550 216229553
    0x110318040f0912110609032a06070207090c02060c09040c030608060907061107030c03080d15060903061a0901050d0302030d090b041203110a1d1906170603070e04 71
    0x1e8000951032000304404005004841c00d00341d582140112040f00442d803400b42e60442003900103580361041c0d400750082c506042100c40c440200680e810141e204103060580c00300380b011814000d00380280c1d5607400400c034540c03901d80014141c50b00f0030a42419274200c0c034100f04243c110074040380e8051804076000902d0421502042d03000700f0307154000540d140b0445040120415001405009640064503101d1480803007006107950750030360740002003a5124141c07081000502000c040c0862160802d00403450a404500e0401078450a038811400202c0e0102d0030024851544200400320800300319080c0b40c844c001000c54402d000610641e0f000301c0741c1c1c0d1055400c0c1072007441600c1c400b4540010501030a900d50411303019484056600f0345000c1108090b00d0740d660b00034030818070264640e141c1541055038403402510a0381e080e001c10307400740240c2c0b007070030595503200401c0b62001f45000040c00034060910400410010994040a0f0958511814428195000185c1d070045407400821581546d40d030303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 216232050 1250 216230800 216230809
    0x70519050a0c0c14040e030304020f010302031b0a02010204231008130c03050c010207120b04060b010c050a050106150509010509040203070e10050d051302221506021c110318 76
    0x3040d0107410381410b0080030070074002d0090b984010000803a0180000e00310b01e0011ba440b0300c015103000b50301140032650100194080c2c3c000c0d6601c41003000040c00c0116444400c217201ea403119010780c0c0181d50004003031000c0381641400012102e40e912450590800c0c001c0419540c504070b0116a003800003440010304180c2803800320704403865001080c0e5170015a07030f24140f5541d8191a900c00c1c094090302d0340201d209104803003c0cbc01000d410081c065926151920750b00000e040050b01941000b16249800b00401d200b0420b6641c074030302c0b8800000b400da14243c01c14000050050020317042080812029007145c1e409001c0d070f15100710444006a0741d40f1559800e5a41e1821002440e1300810302400c0c0e844255005400341401c540800c200344815139510060140304c01004d40e000b940a484075009210fa0318490380301c918ae8030002d140008000c1d1810b0030b007000645460b4022401a406030001d80491011541a031640309090b0034040105a608040d10343c5a002d8041b0280c01c1900d0106104041c0d40e6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 216233300 1250 216232050 216232067
    0x190203060a09081b030d0c0e0a09020c03070f1211060c07061503020a29030c0703030c020f07090b0f060a02070b0304030e0402032e0e0601030207020303041d01060206070519050a 78
    0x8005030a1013900324000c012540342e41064020100b001d1401c082e02145d540615545449480003c22a11841e420700600724001c3d0480d40c00301403648001d016030300001c0c0340440421034640c0120700c0b1340100700382030350010700e01500d2195207003154001d6801d001420321800c09540070b0682c0030303d007c40c1880640c4d260800c1550190300281d8002001940000c04a11003c00c0d213007046c0b25500e03801c03030004480144010781d205c1981d21098440f001c001c8140424800d6004e0070b1090040e1042e20048031030b004200d4074010b84d540020040e44e13940c0c2e8104d00c0c1762078811502010800150388079401e002c01040c002c2d44440242c41132584000e0008006010140b14005100c001c0303600500071522030420210700020720364602500e4100801c11180001c0b80100000745000310b46542100b164140d6803100110081e41003020203d03050300c801c3c0000714101107115107085804d1600c04003441107616110703000749001005004001842001c2024030f043c0900600046520451800c06c196a0403141404640090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 216234550 1250 216233300 216233317
    0x2040902031504050f010204080a020f0f1e032a04050c04090204060504060f1d011b050102040305010b01031b0207050d210908071d01030204050a0e0303090f190203060a0908 76
    0x340091107290745414110a801140104126172520a078030264908030b10450250400369401000d48100510707095000f0340d2808400f819290070300c2c003104003041140d802084421914142443c8c5e103401c5017400c003d46d01e4410362800707401c942080a80c402266440e03000c400240503c4d01d070707800100c500d2102402c0380c00a03c120b103000c55881365506002403094115005600c005011006100c0c3c00512134a4010011210400354043c3c0d41ca000c00107503106031600700001e01d820400803504010801c284060b000640c052000894120103010004089801e50000034103040c01d000d400d040c40c04d50020b000e0064842c01d0f10b2a5880c550b0b1030901190100029030004900d2000d14040300103c0c0d07220311150b0031103010000704c41c0c1d4107442c0c14420804180481d0a000c00f160510010000b52801d42c01c0716410542d0601e002403c000d009403003e055500c11602c0d001203a201c21208200c4002c108044030708400c1240342d1180c58039195002945941c0c0180401171002d8640c0a2035060290032002c545110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 216235800 1250 216234550 216234553
    0x313030516030305160f17060a05030d0504032307181107061a120c040203131e11030c09070503060a09060612140c03160e04050a06052e05070204090203 67
    0x1100c680c42d000300545422100c0c05030070400d404840454a010b403025040224140c2c40340e5115010030501100c00041c02403500d544140403070350019282c0c0f42400401c81c400c10642e0f90300e580d6402d50030050046d910305d62501400700307005021030086000c049002030540310522040c0c1c1036400c0c01ca8010340900301d00012400030240001e103800401441e82c0c045c0c0c1c1c40c88120f4540200646c0f95204210000804541804141e04640c0c0c8150591400d54000d40e4098aa032005900020607a204d4114854111a06050840c2006a01c00502c203145014410310300c0110018440c2c1004140030480881c0058965820310034040b0100f81c240e510130f1402000340025890400000343c1d0783c11300424881c1c4580e5500d20306442e0100800d0303190703c0110110b114410042501c0d207903841e5500030312041502e85a200301000752442080c4002d5403107000b000d02400b0101c00c0820703c030303050000300169215850409005052000407020003183c4500d00d842190384182083e6071030b500c5500224015000751103009616 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 216237050 1250 216235800 216235837
    0xf080712032303010806180d03090515160809010e030414180f010501200a0f080f03010e0604060b0a0e010302030a0f05010305010f0605120705040507120f0b040506040c0503130305 79
    0x249800e0400f43d4100c6880030200e480980340c191800c1c0d4916008160080f203504400300e00383c030240c025040700f4650340c0f1482c1152310b40c00401c81c402c2c1040806503402d4000c1040c20040c40ca0b035035480740b401c0790840c0800d4001c010b40c07100380c01142c0da00c0c4102e205407840340c1e101400c02c403d01d81c2ea440002e807203409801e1401c602c0d40380003a0030b480d9403042401414049101081000f003091b01092642007032000e0040207101c0c0405549500b050307440d51900c101c0740b580e02003050b022140d040c0c0e0701440c0201008500e2a02a051050804c000d075901074000e808040414001a00402c0e44580ba28800d1442800c0040c0e07203880b11107004018040d0082c04586080c2000c00020030048150b01c003140d403007900c1204100c400e48030000c00400104000c1c2810700c03903200300b000380070529041c0e0203a90040c07401c1c2400c10210305507070007500568450200925015686420300003503820079004495014208640400c1165000b010141c1540009002e44043d000344500c80c100305801745040310084542c1042014a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 216238300 1250 216237050 216237107
    0x109030213050106081b0403021c0c08011b111f020c010c020c040605030f0d050a120e06090601092d021204201c0f110604060314010f08071203 63
    0x2900e804c3c8198000102518001840421080c0d20200030714101c42c4c00614207481d5400b04084036a804d0504100311411416200009010162250040001d5800400e005035178040500c10342051071400300501100036100d851214021506000841d00e00000c2c80c910341200304182d009004400354a0304035803034006901101600000c60406850089a05010803138071401810340f122040c02900355160b000f00c0342c2c10f0800d801a030141420801c0e80c9840700030340f0a140204010b0b1080c0500c1c411054010070207020440c1c505000c00c9000d0180200b05000190700e0b541c007181d50010140540c04c43d400c0c50384440744c50001c1d9070100d0300780440e50004d0981e282064244a00c0743e5250a1102080024603404a082401c22080d284030700d4645140845030301e5000d80b10b5125800742110222280280c4100d64403250341e0f542c020f823014041c15980043e4000240d00b0503020704c84183c01c000e50076100c5800821810000140d140c0640d0b480e00f00c0b001c40060240340903520304250056030000e01000c0382c071441 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 216239550 1250 216238300 216238339
    0x1b08030c0115030b01120611040b18010c11120a0b01090615140301030303020304020d0b150102070909052e02030106020c100309030c08090d0515150108070c060b01090302 75
    0x44900102002001101029025000c0c0030b00a4800100100d900c0d90040107501c11b411008605d150041c00085211000d078207040702a0b0b0b100390000204c000c004100c0079070b044271120951b81520340030b080c512040c041c1c2c2d480c0d420b2068401c41c04240704503040c0208100d400c8080c46104551030b8031120403025540c40e100d451015018078000c80005101c0c0a4603c600e0724800c7d641210108180e6450a24590a580f4114069800100240c0c1c000321b0791510f10001031407010303600d8414030641d002040c1481d980e20009003807103019800080240c0c24101000c011803004500309440d0780106059a501e540b0000c810420031044400d680940c0d031021000044681e00840c104e2a400d80132207422244402844042d0100d6044080c054005155120514000b0b10b040000f402c58110003005050f140c1d03100e660b654541003100c0580050400d205040c000d1020742518600860032007402d082e092407811b600e0042204005101c00b806503503c0e80850006170340540c1c0c0940145030064101241c0003464012031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 216240800 1250 216239550 216239557
    0x1602031b0a110904030f1206080307060b040f0e030405130605120312010609060f0309051204140405070c150b010c0c06030903020606010504050a0306020903160e150303120f041b0803 80
    0xc0d190346161140079000b6160050b0114412681902c50b1020001051801c1b100441311201010060303985070004560f41034100050481ea520648020981d86440014070080d152005440c071255401c0c859031000190303000c81601c050b510240c3d005041c15209821141c042c0400380c2c409a080004c1d940203003100c0d000440104250f01c4418140c400740d136a01c3d98102d0710346000e480b8140c0020b4000c01c10f00d40c0584207410980109010f841240d056120504142ea42c039070082d072212280800c038590303201b00f50a01d07001e071550002141c1089140a141d82e11603404460b1010f08602c04240e5485d19200e245e80078803005250310780c12440707101c480c1d03846040240c0140b906450070707000761141500040c081e6104004960507180b003d400c21324094507556612029400c404021603141c015080704c0030f1010b415104c0c0744000c10054500050508100441a1a80f4088050140643c04c10842001e036040150b11003604080d035011111000c1d80d403824041c10030403003035080c0003981681d040d0020300310600002a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 216242050 1250 216240800 216240803
    0x1201060908010b010e0a1205151005280e041403070803070201050f01061e11010912090603020301030222020d1415030705090a020a050f070c09050f040203061602031b0a 74
    0x3c10800c01c00c0300042d605641c800081d55170105a0010034030000d00b807424188a12071041003210514040c1248881d00700408441c02c0551075064441000303a80f03041000280b5040300e10b54903007840300c0408109a01d410150213001511095100441c0c1000419001083c09035041400ea946030551481e1100e41d981c01901d01000640c01c00000c640c41c075024080d014100d90341030700d4285c18480143ca00991556021040c5024846c80070401103404d0f00a0103461800c80c1f00e0680c1c080051170780c01001c0d02e0f807010781e042401094414001480140c0750444100c1d00c2c18003075042c000c0e281c840d030100c1101a10620003090707802800c100001d00500180003202d401200c4501810011120b404c080c907075101d40e94451540d101a49001195200c1000d600034401d04c9040c6c94810300e08040c8002c10209540300c1c1c04106c404600e8203000300000f000c544242a0400041a03031050681825000039540b600003030501e00c8203040d50010940c04034005c1044442c0381303258520f8140d00802550045444c0d9070035810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 216243300 1250 216242050 216242053
    0xf0409051e100513020c071d011a0306010507060209040c0c020f120a0b1005090907060201180f0230070e06030d02100e07030c081b01020705100507081201060908 71
    0x2800246840001c4428807070741241c42000c80d014541801c1107401c0560000849903564200a0104825410b00455000d060640c0000c0303a00d501e00f000410900340140c0c810f0250b0104186d0b803110070b84154080320340204091078920740b664030604016000b4487e241c80f0039845445e20207011074854002d21076588050080328595050f450410034800314840d01002282c10f07810500300600051042141c190f04018010b054441d001d4440000c20b210040070b4030f0240180c0d0200f01c08022030755090103007020081144046226044c5950b840c055030150f04103000340b040010311810300310003e21281010107600350104060843c039080c4041c1d40c550616006c4d00159103050000116942400654615030081300c0d4018074811581034511030042105c0c1c4400c614500464000102154223101020040e0900d0b802814001e04044000000015480750482c1550041c080c100260307a50300611000c040110b09000342d880fa00c0346028200b52258074030400c4150042e1300041340e0140d00000c3c0b10b040d80e00340310 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 216244550 1250 216243300 216243331
    0x504120305070c02060f0903030a121b1707120f09030201050a09080f21070e19060807050a02071508090607050f0a030f0e010504030e01140310050906060f040905 71
    0x15011001c0c0c0701d0071100003020440d490743d520300500380311005054204141d00c00c941002182000242940c0c8080c10000000e4444004040c15190f85d118000400e444402401c015481442000d4054103080d00d80804088448001440300e60064100d010924041e1804104208034012154018a581c1109800641c80c00002510601051041c1d414054003c441c40d810980b48007142066540304146904995060505003002c803149001d40500442d5251194144004147c042c00081c1d002892031101d02c190303e00301080750982204009400c10b0140c80c00540e91190004180c1c44c1c61040d81c030407003d21100940c24030910b0340c4611494000c018071000d07190310741c072151400c484501a04114800c80103081001410309806640404400c80800701c022407119080510182100d81c2203d051700031944410f0542c08640e400000d807150313140c451b0805030641c01c1940804401800502882d4050940c00e03001c5080c1b41d442505641144049078030060741d403a2286040005441c058504455002e03008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 216245800 1250 216244550 216244583
    0x60b0c0f060108070b13080114010905060103090b0a0b150f0c070f1a030402010e13050a0506010c031b080715020408120f030a0c053a0b031908120a0504 67
    0xc220786040301e0300c120080a10505180b40071015502504a410210075080c0c00001c04040030300522010000115a1000075031400c5c851001b034401c0100400e0400d85400304403400680610b0398a9000b110f41580021714035803240100e040d402802082108542011421100080400b0000c001034014407003500ca8540d510b080180c030340d085c04d0291001944054551030341415030a806190300900500d0180d00b5054a5070108503440c180d00c1000e100700d515601006003080b02030084540040080c6011509141c090300c0060262680038900600707000e03002005410f001c0d80c030064919490b044080d0081d441600001078000354002c0c803842101d0701659040c0079110882e8010360f50000c4141d00e17104e1840d610310940400134412030b0340a1003880818020340e541418140046805052207100080c4c145410400400040c0d01d50219001e40a0070841d81c0056a1004101c001c14a0721210000c0b034500707043e180000080c01028031a40000100c00c0422421103840d4012a0207940a0780280c014032428 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 216247050 1250 216245800 216245803
    0x4060906022115030105060303040905040501021308012301140d0512130303080c042303010e0f0102090901050a0b07140f0d0f11060108120c0703060501080d091d010303050c010e01060b0c0f 83
    0xc43e601523242e0400d200412400c40c0703d1304a20b6105110300300052400684459900c0c4403240e036080701515a568810030b205210590110340c0c2c00030000302036410310350700d840c2c1700c0e099106442d5080d81c0540d4a0b00c03115010004104620102c00d0880808076403207116662400034007840c5848240d002540140205003443c408000700e5096034100c444030859030b85108054000018210300494141d941c841403101c10310824441c2500c3c1d50640e00026a482500e40200f118510060300300c0c030322501e100181045a41c0c0b0350411144035952061003e0254984c016290b0300f4405c10000c07840d22401004002d14141e988408540c038031210713030346620170b0300302050402079a155003d02031004141c1c04591403180c6d901103580684003131890b900844540686030b40d209000c0e15020390190410341d2240b02c816070415040548100078004000880d0350b0218280aa00300002d411711000d800c0c040c0000d030403403a0303107420f4200301e0700380d00c184d0000c1c03120303607940d000d00240c0760f20026000d80140285602146042c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 216248300 1250 216247050 216247061
    0x30f1201141c030e150a23040501030c021f0c090608040201080109050603033001060c0503040302010806041b021f0b0918280312020909040609060221150301 69
    0x402a0014180060480303101c00c1542c15100c2c15000c0c4090901004071941d40c141c3c00d502c8805640c109035498008050700030700300b0000d041c005c0702d8501140344d4003040c001840b030968007142c2003440d005c41c16250a8000f6805d00031101c50030460803580a0301141c07014003c0d041200001d0b10381c0c1d204000300b0350340c2c80210349540c0d05480003800503000d04010003c40303010ba000a034010701c0083c203070f80ca45040400b051641c0007000d2382900154032110807035055420040c0a96004009c103050849002c2065900c41e0380f030b841503020080c148420329010401549843c2c1c0480e02403202c09880d0b21803090700580c042d55400e0300790421010341284614002c100000350050340d07086503010700f07000102d44480d4251603072030a207080481c0c0144160b0608203c440c4244008800da0001c00b49603000140450070b005061004c03202e40c48407900e00422141c240c0d0b40352030400e26406030f00f00b030000505041602c0c0c000080d2048603c110306907908d411440d003c400322261070f540580e240105070494480000b081c18240c03107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 216249550 1250 216248300 216248339
    0x60f01051b07080a0309080f0a030c060e0102130308090a092d0b030304030308190912230a020c04060503011119170f04020117060901120c0305030f1201 67
    0x11000e000310052800e07900340004803240888140c6034069100c00355646403041d00c5105400041c101c03402009034920a01c1018414519840a44102007642c1c40143c80101c040704001c0c4029030b43d451401d000c240039070640d990b80c000141c01d5801c4954178244011035030041200e05100d1a0310820001e204080b0b441070382030f1040b5008225262002c940c415403c1c0407880300301c018496440d820f182e80e0076039090005001035403080d1180030003820151200c40d10081c41140d4540094604502c440208442080340382480107180707002100e0000c800e80a80c2554041030b86d1451001001c00c0c500b00140c2c01155400b03400c501a1420009941d03141c2c101030076990300c0314036480390b59010041d03d5030401003203021804500c1103003040104020b5800d180311002c58112841031449070740c401404119a404024401c06040841ca20504d41c10300741c001440302c0130103104501c2100c445641950421151020200003140c0250649458521403815004540e0003e50004c0200100c8000418100e62542286c02003030b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 216250800 1250 216249550 216249557
    0x603010b030d030903030f050a0c090e04050304030f0203100c03061703071106031f030507090b0402030402090c0a030e01020f0304030207080303040302251502012f0304020613120303060806060f01 86
    0x2c1a0b4500150024130040006604040c0c1740c803145d000408013800b030540258030401001608440b9910001c1410351142c0100c00c416038940c00388008203400005441c150b030f4210644407a185060310010f4500b4143c10044031002d801d2140191807941c1580c084030450f15014a540380080c01001e04d20744034402c001c0f00811040001d01d8102403824524040d580c4120481034094a001c84003034400880b4906a00850381c50303100394410b0050a4140c0541003101100391b07819030841c00d01da40022101341d00280444441100850340c106514400e80000001d0003c0a000b1507582d908894801442d034400c8034150301502c9130490020b11410000222441660168040e00182c40c020004002c1094003500203054000f40c80301c041000c0700e0b030002070301c00e03403115400005103100d80c41d40901d05601c1039980d080842c241c5070381591888412100300c0340d000354100c0c0c003960703668044486140c40340225048804031b030880361005001c160305507100c030064881707203402c40d122643c8001c2007100d00b941c22540346000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 216252050 1250 216250800 216250813
    0x19050301060506040602030f180d0506060301060e0c070b06041508060f06100906050c01090b01080a0b01090612020108041e03050d060e010b0703180510090f05121c170711060603010b03 81
    0x1609038101c007a04100100e5862009d61140a0700001d14403454108190b566400032400e2060504d003d03c030f210000c0103013001c07095140c41c0090100c0703a14010081c02511005c1c0850001c0c03520f03541d96010744c0d881c04807032103800c0e010350300d0354000c40d9076880456401a8102d20980418203625000e000d80c42d1807400c0d6640c5106060030203c0c01c131181d0300455600b00b515900c810041000a884090b224040c117100c0004100d40511b034100300a401c101a48050119072500c0001e2042e1000c8800b603442c102c1d02828848100d40711868113412254404100d200c074411008074a808141d80310005001c0e0a07420001445230303c3e200c07041d80c0d420350406e03c2040a80c400810402c000a1b003c0d0146100b6a2045050801225601c4007c00c0c001003031112171400040c4280d5040c851410941580c0015210a4601d61840148081c0850703864481d008065020410045118403441c03048401c2100c451100d1818401828800d5001e022a0000711700c1140b00c1c040d50001400900301446881c20045004004003031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 216253300 1250 216252050 216252067
    0x5060609120705150c0606042a0c0f080c0615240d050c0408010f02030f070c08040b0a050307030507030e061603060b1902210d0b0a051905030106050604060203 70
    0x603500842003816803240240840000c10f0b6139240010500f840c22a03842a507a501c03d4002e007402c000000300715a00c00da181984181d40c0c04003d04101e44035458030004200100300118040d6940b04103a14002c0100104003001010819010003600e03a440c100002c031841601d44200508910304040302c07940c0c0105049210b665805545043c2c0760102c0c01004e101860921524000710030380380d045480c1e01007a0780009003000080024404c400301461842c40460035420b09100e8006442805000e080410841d800a0000d0082441c00c0398014013000020540c0e5023125900500703190801c440c04000b00c3c1c513010009107030303600a00030242d12400c0e0300058035440d036078a400d5250111840c903400b0101a50740c88003081080e110b03c01403070031118603803054500700441c01b402803500091610200e150342d5040442d4400320b05110030383e05000c60700d00300424801000c40c0482d10301c1d4842e0780495805144405a841010480d00c29001035610540003032001c1d50b00c6030103018103803013588101d20050703004024004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 216254550 1250 216253300 216253309
    0xf0304110402070506040f0506090d0914010e0d060b0f0d02031009050304080a0506010801110903060a0e100207030819020a05070212010605061308070e0408090103050702070911070b060405060609 86
    0x300c03140001800141081200c0c4c95251403d603040f035003210520030190180c401d02404000c15584190800020907206a01200c001c000341e03007038407850000c00c40001054500d68042d102810701801301034a6601d0003125405c02c0c001034943d09031503078020700006040c600305041140b009210580c000d0010503001c00f240d940d440040000360404d403903032301040c000898040403c2c0f0400080f075000d00d00520706541401c130f0503421904940b0043e00002c100b00045c90305c0d500c1c045400ca80c000c0c0000750003d0404072a8500a0600041001d82d5000314800210502003607040744006001d0100c4840c060446515408124102c0c8244d45810000c41c5042c03154030014904040300d940080c0c00135001081d2a50344001240d100d8010620031160620000c07024000d107102000003400a0156508170b44060070f29446001e040d129a1100038105a220400680d44074002c000b040014800402c1c02c004100c405586200250080041111114111404101985014081d26003c1c8100412142c0742c50001001c02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 216255800 1250 216254550 216254573
    0xb040e1306090b070306080c090f01060c080d0204270e1902030a060203090303060907030b0607060c030b030d110c0d081209100c050301030605061f120207140c010806060f0304 77
    0x441e215900c60026400160554644a0180c5141c5d103011a1060130141d03450704042d44c260303406010700442010048e03000700c0a0402411500c190401c04084400350411400d10300c0303010060072802c1d000040003d01007020301c01365044071001100d2201c04050030540036098840383c200c0201320390300c00c00315400c000409a42010a0340d04c01002c0311031b104015554481071f0382003100d0140c9560000f00801607142041c1000c1580640c1034038007000780c886a94001401c80c010030f100581000c0c0d03505404c2d80d400340280d00c001001100141110440144240001c0c41c0000c010280d04190068864401150900a00c0c0f41d440c0c9902036407031404c00095041c0f4a10503c0010072080b200d2080c03c0f0b400740103c030b2500c112600702c0841d549950f901c0d810b6040c400103941015140d940101e420352011403241c400e60000a0100010389000642c0c00700b525031001c00b038041c030040640350403c2d214280e031008c040050b9010846100fa29021025a1007204104103400b4400c11001e0a070743c100006800100d5401c980d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 216257050 1250 216255800 216255803
    0xb03070507020d06020a14160305091309050c03010e01020f040504020d020f0a1d011704020f0f10170109020304080a0c050304030b16080c0f0a0c0f0b07050a090b040e13 74
    0x3860034078541d80c0009007501041002a1001a80003074010b56450b8440035402548100030541c1d4a00a103c1000c61100401000d0180c00c00c02c000c510f41569039548440c400078820044028080700300079050203502e680e450003c440c420341c0381400c601c4650710117009880303503180e4581046040c40e250800b440080e45c0851520030340680e00b0424507801c503a0040c080c10b8031a0882d9507108103201e800c0490203682c0c1c107298034141441444000c949042c0541d800082d07100f503040c0c840c04a03048034540803496040d0f02404840d403000688410045540c2d10514489011582e050b8070141640d0b616414030483c0301c00d46000c0e1040c6801c109060825006486c2c01400313910031406c5a15140d5203444100c500041070b00c0c407258050028468001c920742c0030308525000440c18910615288108910145074400c0e10014010b0000c1d000150007400081e144c810412500b100e03a04003149840d04009103a50700000e190380108500c6d020201b5020708803010380301500d889660044090700c0e0710416892500c0007140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 216258300 1250 216257050 216257057
    0x30612020120010e07090c17040807020307030b01120b010e0403050901050f0c0d05190201050c18030c030604050a021905010f05030a09050703080405040b0402120604021c0608070501080a05040302070b0307 90
    0x615114140b0900c1207080013a512030103042c0039810039404105541c81343c00440d04000400010040f030145e2407048542142d809500c03950740c7c100c40d1020034108803d5600c050039500d541c400003d17640c186e0740c450040091065600310840e0ba203822030401d00c00016140a00000c105100840240d405000248403000030f1108180c00d00c05c00b8a40f5038a09807110450344000780020a0b800160507880702401c0044d0f200c1c1c0024000303403070412042d125a004020000210690307020405000d600e0500120500c103a014080c3c604a160a003400e0f5a01d481f400001c80c000c1c01c5121669400c03550f40c803044c0003075400580d2210758044c03074040101c40e5500b019026002550f43d402880b0300158040251000031803003201121385030351410080104541c1c00d500514040c50041104c0009003800600e010f0707100d041101c0060302c0e64140344035140c00c2c514141648055074a08179012841c00400900f41c8111102643e900b07440d0768440e1b110f0402d440090718014090392203079105110a034a510041c0d0703030000300703803a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 216259550 1250 216258300 216258347
    0x120f05090d0344130201110a060501061205181b12030301090b0a06050403080a080a1b0206071119020603070504050910210f060c022103090d0203070803150619030b100306120201 78
    0x209d403101110300a900c900302090300a045000150304d14000e00d944203006582039160451507043c01512550016408030040440c0c03500a00b45944a141540e01100c4010446e526503071940c2c0c2c080000c015085510340328440000000540070f204008940990340e101d05c4050422113103c109840e8070310f000e400091560f484014040f8000301c5100362030810f283c554024003460038046409013042c130f04c602c202c0601c0c1e005614030300d44110004003240312060b07041e6840ca540741d50b8050304441071300554020700e900a1025050108551f013510031401075401a1007030740b12000c800807484920704c50300c007001802549034400b03c00124503140d10261810040d401621070101e40800700314107a50005c140003003200d00c0031050144190040001c101080c0d21400298030300101c586884507039000040009880c1a070001c868031454551500391a01c481600d40d4a102e2000c03141d0024019140c050f51050244901d4100314200070300c207018000440340a40c10f484480c85182e00110345540d134030880e03e40c01c4492070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 216260800 1250 216259550 216259553
    0x90e0601030c1406210403030501050306012111030708071a093f03070620071e05070b0306130b1507030c1a04120f05090d0344130201110a 61
    0x170700c0c0442a440040054010510300303850098219001a00618006c0c1d10280040c8042c142c680443c1c403801801d842c00281c0f45c0322502e480240d08039841200b5405000e800d200280b04c0c40e0005443c0e066444d04494109080300198003184c2a0185003c029030007022418400040104e8014100f0f580b00c100343c0709085081d140c984a040304d9010b0314140002d82c000210242801114411042801400104148550250303d80746425005480014250001241480f40400f407003c00f04442c07164048151541d0564aa5041c140c80c6c0084501d54000c9144003441c95030702d9650b2003100305905000340100c0c02080c0382040d500481c0c20401c011024450744001c058007103115021200c00354080c000c5080c1091806e0310301010300c40c8406180d102032040700b106200883e60404240c400380c80702510000050100307801c02316078507a98006039490181104000c000411004050805801d5801098000980c10444402004030701268141034040381c002c0704400641c86001c1c3c010350806640c0840300d804855 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 216262050 1250 216260800 216260827
    0x2060702070323150a0e03090904021207120f2109090b15070c0501021504081e040b0a09090516170a020903100203011a0429190801090e0601030c1406 66
    0x125074000c02c941208204100300580140120b0030341006d107030301460034000a031001c2000c00401801c002c0c86151003046564075041d00300480ca00400c0705462401e80c5000604007100d05103c00c040945039260250b010002100342c140008074022035580c0d03a80007032440c05e5402401890b24003c1717190b0040e20300100005080403000a04140c502410346603002918060002e8604010520310024030000c040810022500210907206101c040300c080d001c142c0210f00d0703102c0691059400805c81c607040402c0d0306480aa2180601050702c4a030441007005456030030162a0140300700d804a0005035001185080c403c4a00072680c0d0040f02496001d07043c0385030b03c00001d09041c8135052011005501100420407181c103a4225941c1c407040741c1040c2c1c5041c0c10b0215020070401200204001103002101040401c00010111080842d42c101ea03411411030f1100001e010003000e1180c000070303509000e4580c00090011596604032680321040b42d060754508100e0250381703606100140c0d80b0013000d04c11000310303038007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 216263300 1250 216262050 216262063
    0x9060e030d0b1e0105040b1614011a06092202040b1207030f09080901051606050112020114030f06090a0b040203010e0618090304050111030d06080a03080702060702070323 75
    0x2140c000881c100c00b54000340081c51500000e00710800c0301c2c05060801c280d80240c125001c3c1c03403000c1c1d0361582e21603100c1002215881f84020003044480100c0d55450b0035203041d44104058500f0050802c070407103c0600704085c600a4210056200c104480c40002a92840011444902c03c00b0710250130144e03640c050b043c0c590880342030301550100c001c0800841590600c503492488500c0390007044a840e0903101ca030040c0c080c49503814140080050706096034001903048986640d1700040c18065076841d040392518000702d440d4124082441102c0d4004004007220940f807054040100a240c6680c82e41c003000b48800d03014018a40a41d0748142d8031181c3c4c0c40b540003d502a00309050001c14030300b030540034040240586582d950592102800b07020328202d0103c00c5400b10703402441c0c0a0351902c1110003d509501c10f00311514007061828400003a6000041010b1390420f00036100c9800355a9501d10a030f844000c1203400200581203910280000303512003c3d69141300c0c82c280d501c011a5100503802518140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 216264550 1250 216263300 216263317
    0xb030c0a0308120c070c0302060313020d060b040c02060405060609072003031501020f06060f1306080f0c01050a08010e070309050313050a0504090203030301050d1e031806030605011209060e03 84
    0x640000d0b107040e0900c1050030903401030034045120345415440d1b22842c082e8801b6000081c400c031400030110b41040a000440701c0416001806500e9218491610000811428002c1f070701031380c00c3c0001000100c0c004a2224403903070304640a030a80303039144010001c0d4000000c0840e402d000781c0d43c1006481d20488214001c1c032040000c0210307903c0c106070302031400343c81d02210050704650145602e11801e00010441c1604228117071641080c0000120002d25100051100c041c511072900034002520b440018800744140e056005075034080c500c5000440f6030384501c1030600049441100104001d504911095a20400354038000500300001e0356072a08542c8030910502e02034071b400b1003d02552410412460041030225420800c0c1c2c90b4580c086038581c0014410f6034800c0c01800c018605008a4003560303400346180c04000c04a011079454042c0244494209032070304111500b0340810f410b4024072071300c0e0035038070705840d00603030500400c42c0320024040048044650f56228442d00098031000c002a01508 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 216265800 1250 216264550 216264563
    0x2113121718280c050907020d08060103060b070b100e04021c0302010f02040314120a1706190305070e060301020913020c07030506010b0d1427030f0d090b13150b030c0a03 74
    0x809500f8011101c1060790003c0f441000702c641070000b0340b900002c0b042c15a80e00c609200850384d0341e5500680040540754411801d905000526000308001d0200c95417043c0210565601c03800e460304c507526010b0104440081d003010482c03281c42046c6428100c4010403c2c800d20000c03c80d10180c9041d00180d80080d8000c40366414a01c03496a02c5440038000c0c2409281002440d0341095242d2400811601c0c020161800540402010900d00c0c4c4410480030201d41ca068200141142c3c0c914205070b03640720501c555080d8003000c4001c0361091806001700c41f40c040005108000022403407920344002e5000300424065413090501c00000550300348101c42c000c0244090b603507100c1c21807440070410f41e400e5010344450f45001c9002c11400c0a00180200c01c25402207043e8140a00741d100541d00d1807190101c074202a80b00442d0516104009800000c02180709104240f082e803100900303406c60443c41c0d64010602c020340c40020140c244580d21000c081e10006086540c5003040d180440c0c03407442c5540080d5840e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 216267050 1250 216265800 216265873
    0xa1b0302030d08060a14061b1e070302030604290403020d02011112010b13030602030a1a041506030f14041a060108090c062113121718 59
    0xa501d01400061400e035410300b0310444a02d003030000143c2848040c05014001005182050f0940c0c8542090780c021883d01038090050004203c4115a03c14030542002400c4c811101c070b0900003140410b400c3c00300c5e58064014140c0b610f50f5500c1d0903451a86112003030445c0344a400341c0358625051040b481c00385010750080c00490a074920000d003503825402034020340c880c00304a4078030040d030f440070a6070456240448682d11466517400b00340748998568000703807203180040140600365050b40d101c014007404441550020700415024003003514a60700c2064522014a40100000c41c0207800c108440052400c002860107050384c4107400029090f0742c02d80d809441c02203c040814034040546030050f0090801c462140b0f00000b0403aa0b40d0120342c0301c1805060042400e1403d400c0c04010103911101d020242c484a00e0501406620b0000708102542d11014410040070458029124034a10058001002d0f4442e503d0200441f42c004c000031204045105001814656600490b00c02d0280028822403204 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 216268300 1250 216267050 216267053
    0xd0905010c0c0b04080901030b0901030506090c0a0312110c1216050d0f030309031b080a1805010504030206090d060914070801112a0d03021c05010f0e090a1b03 70
    0x7110002070703542051080760403103003010420f00c84034150f10030b03405035400c2d42c1c03010980700403800380802c5010203400007119800403041140200d0114403502c0c2d644112080440b494003086404103091202800d44d0000000100740e9910403000c440c1604000c02c2240c441007100404201113041801d041703103464015801d40101005e604041c0001420200c0e849500c2c0c2003039480d0000041c0c1507a0000b070906a80300781a600701801500b14000341c0c2615914008100f00d03030708015403941c0c00510f4140010b102042280e200707601400240050741c40c103a46a80c00c007400d40d405d200d46c42d8030080c21150311600085551f00000c8150040b1000c2e1841a40720b130030080b01c3c030002c0600e045c41036000044141d042001e1407100814410a642c01030f100c02c44414940c0b4150040a4082c0010104241860145046001e0102d0301070700240001d10011a0070203858107801c42407011200207000d035454030520b002082201c8260740c4101030308001d41400361a002e00142da103681101c20403040d44400408954802c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 216269550 1250 216268300 216268303
    0x102040501030b101413150908150906130f06020a03270512030c191107050111070308130e0a14011d0105130209090f09071a040b0319020d0905 63
    0x3a494825108510065084e070406401d0300010b806040742c4030400f064038105402000c03241402800e81400d039068103003010700000c11011703039401740c4005803041600d00c4a01c0c03006210910701c5904820042d0216484000e02e48007608428601980c084488549420104401c0e1000300b820240641700003403070071b042c078189484a202040311103030508075180f100400309001103201040c0c00544c911040d901c0ea5480ce0b894028003c2406040c8000b0595200a03140d94010050503000140380c411506920741e50001102c5a50b01403611198540007801e080000030081002382107050280c0217510181c030340300c074010b44111500303c815050950726000d0080c00045420b4025024100070154811840595180201c5002d01881524062500d0446803401c07188140d0507200d01030700060040480d4108900304900e1040c007034078100e10601420344002000c400f020940351551002c0c402d0642442c0c03904c5072101241c1c20042495060602d0042c01e940240c0d2544010300c500b81c420070380015008910f09285 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 216270800 1250 216269550 216269561
    0x60509061201080706020c091504180807050610150c0f060b030a0c090c0f05070210030608010c030b040f0501060c081303020907020303100509060105090402031f08071703090d030c0320010204050103 87
    0x1203000d80305906c1401404906c01d49c3c1e814800405990229565420364044940550038210141101c10049840c00c1001004140a401451501030505080f62200d5018100f081c207401c000001c102900ca4050000303a2000031008060b019400000309680a83c012030700341000329130704855603482c0150074001500140b1800700c07030007414030309042842d00b100c0019007284943c0201078841c03a0010303d001c000ea8484d400920140582c10000c0c081c0140c007490183c00b6000c07294081e80b0490400a20b940b1000e4944140ca0484040391765102e091101919090442d500c03103140303090503601d299000300c05603c940b000c3c01c2c020111513004541c1c914003001c1050f55030180340c202901c0b46a1301700c24000641e038004c05694031214100c8005940307441d104210111829520790100f041c0f0034a5100245540020030f56a04440d00525007071040e090140c1c0040c0c60f44103030156543c0c80031340c1d02e0590020178401d4910480a510a040081103a80e041d0408440341c0d0548030700c00a144c1d0002000d01c220350781400740c1d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 216272050 1250 216270800 216270823
    0x4080301030506150a0608040203070819030306051f051b0105010b0714072603090a090905060115050403120c051606140702180c0f0c0105220c06050906120108070602 73
    0x8204c10780c1c030f0b200004601d00c007103200b180d080000b01d17400b040035962300340152801001c04d0070860391084071841c0130000500d44140b0503008a031500700000381c141810a0b181c9030b11444a00c241038544603c2c1001e0b90302c1e8112490f40501c3c1d80104454100c1200b092154170302030b011302503a0b951201464a480c80c20301c440da40346a05283c001c900100070752254003080e0550103c614544041d00341007000b600e0b14500a0391003080d40031041c80d070002030b40003059001100c0d003800340c400c0e00c401d07030389400b6586013071008a01ca1350f00103241040f041011800e600390407559500d003841c000340b5a41240d101c151802c100c0d14101000c001384500b040026581000f00c460041c02503035107041c01d0501c190001002c900200c00c80c00d02c0082000002040003410404a4000d06810001c25446128107403205009200407a07540c504189940b0310b10103208414180451042e1780801d00d1981541070040c01c90300c5412842c1c110350883c3d420f1100c480d41410841d1024003a00114008080062808800900c0c040c10480c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 216273300 1250 216272050 216272071
    0xe090304030c030f06110901020a0b060d020411030109140106080705070f0203060a0515030a1e0c0e040b0405010b0a150e03010b04020423060c071505130815090f070909080c0604080301030506 84
    0x7c8210f98021500002041e0001c440c00784643e00c04c1d012481703d660984000f0b50007490150124240150f03c1c001e54142c440c504000c00c1807051408015064000c00c0c0120b8001c6980c0300700240342544504010f00010b84100080d50320b11019038003091420400707942140318a034480041242d0b242d40914220798088049000b450b001006803203811901c00c25028a8048504044480c414000e40108110007031030300c6c001c600102d282c1414110031401d804d07039044829500b8080c59400601d0440c21440c1902c502a05061400038000b20580781c0c4851128003a402d035482c0c0c4100c0d4101d65562029100511074030400002c1c442d881d1408035100508182d8540c4200c5090001c222241c2000a8443c169550a54100703104000c440d0295014050950709000c140364820001c00c421101081100c00355100c006099120b8a0b1101020f8481d9203032070901d2200d91000c40104100348440d0840090035000d90300540c0341c002194110360404004407800d03946210000010410080e04002ea50707881040d01c071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 216274550 1250 216273300 216273307
    0x7120c050f040611070e0403080414211803030a03090204050a0c0c0209100305010c2c0312090d06090602070c060e0904020402031905150102070e100e090304030c030f0611 75
    0x10003160750041d40505410005000051495004100701c1e640c00f824845d80b0301c42452401c2d01c0e0041030104210380c00c80b2110085040640031510000307801143c01480341001e00d640c840d40031020150b40011984588410a0b011086101d440078030051070036207210341c2c001c5401c010a0040c0710544078094865000c04e441c104106044c075902406013003181d0381c104d403501215111076500c6280c04619400283c0039500e0300c5803100301c09070030000080d1080001d00e80302c0410803000244050b00d24040c40d10303a8240e000b80b01c1c100e542880c40001800920300040c407010303824015440d203204a072400c140c00c40300d55900140c420140300a80420364000c107140d20748820304c4074558001c81d50000000e08002c0c00b4540103c01301e54640c1203010401078860190341c04101030320f8001107401901001802c2c0034094041c000000c10701c03200c0030203120320443c0100d0703800081e68a8035040c0c237034802c401492140507000510000c4001403192065000450045155800080c900d0801401304d48062050303211608080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 216275800 1250 216274550 216274567
    0x20f0d02030f0301090902030a0611211308031e010b0403110603070c030e010e04050a0c030e03070b16090b0d0608010b0d050d14040f060c0b1302031510030b07120c05 73
    0xe02c00c0b641034030b4a010300840c01c144c0300d00c04a40341c200d6141004004030b052103084142c941a08015125440345401403103060701501d42c4d0501e480c04240c848440b022110301c540e00108040e5401550001c46c5052642108079024110781e0390000c00703820140411070001000c0040c06203050b21220a4881198100c4c51800c100101a10f10148200c0c02030610429042c4031038a81e0040c220060b1036540540103000c2e5252440c1110000d041d014070042c042880c210428002d14800170a5460140c0d10a5031a802e0f500c4024a421009a41c10808410032040b0761010076189080006042c5c2c10001c06408a041410000005d095901452840d03004100104070080868400a11054020260b05002c1d4021113280b0011090340300340d801200e403074640003000041d030036440079000301101e00035414004c0d0350300d4480031200d440c2e06011029500d94031000c0480d0b48801e415800942182081c0403031540a59a9510021310420480d80750010643c14400c0300c156200301e0240807603155142c0340080c81c00b2090b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 216277050 1250 216275800 216275827
    0x4080909040c0b04181a091602030f040b0c060709120b09030405060c0d0305090c090c130506040f08240f07031b0905130e100e010603050102030a0605120c0102030d020d0b090106020f0d0203 83
    0x10121a100f80c41850241c0f00b840c000c1c003c81c1d0b018bd0651244540c5c41c0c0c4c840720100e2240d44402c090112a01c900d0002503d030f6440395003210b0540741c0076100c20784401030641311040d401901078602c400ba40010030001445a4881c0c00610034405500080c0c00c1502402c0e01c05004c81d00000d00c4841e40b40c0140207011b026589103107003194851a076401c020b031242d5010300d0103044d035551a0032145d004080000c02007829070300c902c0c41d48110707006e02040b680c17100707a80340310340f4564918002d10558484407035010410541da6031201a5020400340b500044016032010325640c260b14034030715000890002001840103040c01c51002c540e40240440602010b200100425500c0150941c40f444d5946d6411401141c0e000c00e400c2407000f10b4114009640340d0802901d400c1c001d060034401e05201383c654258070400c6103801701d01d402c1407510503000742d030401c1c0c0980e1106e4081e50061000107105503481e10755011b1540d4030f61496000e00000d81c02411903105c0c5660062030542c00a601c141554010704c0703954010600c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 216278300 1250 216277050 216277069
    0x3050609071401111c0207080c4006091416090e0603030d05010e010906060f0203070308040201090302090f060907031a0d02120f06061804080909040c0b04181a 70
    0x81c0392250340141c2003144541449000440140d0041110402c245c0c456030000394a0103036080c1d00e05544444400c4401c00001c02c61184041c26450262030310000000f1074122003031080003007048840000310300c0201110440d40305421402c0300039074600c0440e0080c104055000e52014036441180d6182094481c050403206803842002c3c2142e00039400696a61004e105403094154190f2081c021561035104d00b0140c000300b40548600a403a120380024124858060401c248149402440c0b0700b400c107440c2250074510040040e41800b110603170000c016140c07860031074420041d2404c42d407068100101040f1180d100030305000201820310032800b102d42c000d181101680c240480d1054441d001d54400310702d5480b1080c1801125006000c0d000d415090045480ea118210450701a45e4494070030b82550402d0ba000e03203010b080268240110300307170340c200601200d8100740502d0110427544d54640d4a10003561080d0440c0041d180f695040d020050228019290403e00847e4002d00c00d01d5107002007041d011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 216279550 1250 216278300 216278339
    0x219031401050103112a030d0902030d05030705070303050c13060804020108010509011511190308011707030c0501030207051e010b01120912050a0c12090810050f1f1805010305060907 80
    0x1d0016a03001071b6410071407503a8088402c48060380d440b2680b8031803003802812501c000703a02902620707000d0f58080384100200c2c1d00c1416652038060030296251000c40040c40028000c071080d41c000c11000c1402c0081102d00d8004041d0fa507541001860075100043c4551811790095014455400050203400d020b64101e000d441c003586130603000b00d032070030385114600001e503c2c8952103207115040000c1455840320a25059448100c0002c50301d44804400d141d403400f46c0d1101074010076411509010039031080c0c00408090740035804803441c40f940e4900381901c000c10400341c14000da648a080007a19604612289044000359108220010507920390f602c881c41c0d16100e034001c02c40b00160045401d0b00440c0d4002001e50070210300141404454000f030108009401501107620a1a030201c0c0c03903408a004203445084e003011846066115104451039041c03500c03034226030f80c8271a0b160218080b0001080f03904101ca140c84045103031352444c200f20f0708180001d045200c050b00495420b0040310014000480c108 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 216280800 1250 216279550 216279577
    0x801050105180d08070605100b0903101d07062f0c0f060714010902130e0c15041d0a060501020703050c0f2d09061905060c01021903140105010311 64
    0x502d10040028045040314000030801072001c581c040030701106501c031034442d26600d509200c0702510b46c40c40340b182d405801e840d240e055000150408515800d60092100d080c50724031030081040e0b0390070b55542131400300d1300301f070002501c0440d600c01c02c3c0b11248074000d840e5500c0e41d01070380408403c101a603120500251560700500d96081c001040b5111002220789040d000020301d500c01c4480007410b40078180c9220141c0c452803411b40420041c503041d100e40c2a402d90724400612840305142c0621418041c03821001d01d0800051000081c2c00c1d03000d11000f514400026454a84c0d40f504106882c00c507001c03904079504661041609100080c00080d400190b840c04840c42ca40d143c40c03000024010300c0f10700040040030045180d60180704030f000410404810000ca5400030143d07200400c1c4540307404c414106040c10341a25000b046103080400c0100601250030380094a00000794040c0d40340d0b0181d508810307000a56503400200724031781c1c0d5007005014050918051142044021169000b8008c200d40b04440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 216282050 1250 216280800 216280837
    0xc0c03320c160f06031a09060904061512020a1a0f030a060b0708181504030f05010608070e011e0e0604020a030615090816060804142d0c010801050105 66
    0x252042280000c00700c0c00c0d5540142d41920740c0140c00c454200e601c03450011034100b122a0155500b0f040f40c101c11180050b050618540d0b4507000c004195001420a442d803a40c2c40440269400300191040e001e840148803030340c403908482c4144040907085503c09450b000d502000c034422502540e00301c89c00c0c585030151306c540325105d0300b0042d4010070880d40900b03854003000944804100314000070f050b02040d0700031900c4007170b081c0a0034043c08a9018214016103402040b05000085a940302d04480768010400003a1994480c5070051404486401001601665000411800d640b6214503030050350754038040710550740b500c010b40c0001d050241c2068803403600420300081942c0700b42d01c01d0008003d5441d04280000546802504070901030103048058044e0b0058218401c2c1e890407020201d584507600c0800035900c54860038410460408010344e280580029180416440c00d0b8030390048000884a000c0100c0d001002890103e03910582c0d07052101e902c0041080e6030f0040f051710f00e00810800010030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 216283300 1250 216282050 216282067
    0x8060306131709041a0111010e030d0c05040b03072001092334090516030b0a120303022503090611010b0a080a020306010b07080702040f020405040c0c0332 68
    0x14082e070f20916810904c1c00348110030400c0410813104a012084c0c84a420a4488403801800c0e906004000035441e8810054102c005000394410180900c0519009090a882e8206881e50b50320a5541c0300000d0001b9002c401040d03100c03941c04074521502e000130010f056060303541605201c603901078450000341991a020340d95000340012500003038080000d07441d8100d00b01040400151030100312020f0300110002042c040598030941d0300030305940b525103c900280c01c07003c9002c0e0030309251290300410600070028000c0390221031030000d40d2003030b100580c43d0b10031400b258004540a0002003080f259866650300484c0d0440b03454400c1c3c4401b4908407801c2c00094829a01401c010540c0310380203124441c00082140001c5000d9200c28801c405451007640d03550303801c00b49401800c401030300c0080c080203031200515090303200c0c0096011182c07000d401d1a6989001400b100d14a03a018404105640241d904155211b005194420030b4100e10058101180f1400e41405910981895a03060001017505 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 216284550 1250 216283300 216283343
    0x4050604111206040b271005040f0506101a03010e1b0c120301030606090605060a05130317090f0102010606050a0e040603050f0a030e0102010b0d0605040f0816030806030613 76
    0x84084001d800c549990800703103050303002c640c000c07521038515211b04078159031000b900301041200e099811004241181d8080c4404004140c0608101c1d214060303030700107400288081c0040c61158010800d01ca4100b072801c210712403950354284000401040400050114203140b0350020f8020444403100d881c5040f0404c42c401041c82044000c0020b40b240d4040e4881d01060f4100840c140d87c07003500e040c800603684041c02400d40b100c0c0d000d0680c2c440c1060203102c042c0b502c100f015200c420084000302e00995900d4644101e54030000d0020300540b040080c24811906014a03c604100001e00c0200a100c0c80e040c402403650041040038410000c1001550ba203e60303980d000300c0040d6400200750340c43c00e80c0e010f040c542e666900d550204c0101c2e00c600c0c40e400c010760040c4200c07114088058031001d40d1340101d80d1101c1c020f140040040700c01c1080c28a0060204201c0400303440902c00003218a148684241005050b6910080060307109510150030081c480302c00380c001511003544000c804088024800b1a40e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 216285800 1250 216284550 216284569
    0x303050d09060e2d0304080c0d0f1509050c0109080304050112060b04080d09060201060302030c04020a1b0501150f0302130207080c0a0c030c1203092303070803210405060411 76
    0x190052240c0b0079440e0030140b490315a01c51340243c0342d4100032003054810303ea64680c06140300b050b2030754100025a44036810001d0034444514800d400e2035050320b08035569851029658001d401c5c10759030340c4c40040200300c030400c5001180c41090070303c0e10040b4036100c0c1c01642c9100383c1c00b5450400c040d01c8407187c040c13501354104002420b511414a03880700d840702c800030b0342c90805802000c009000600c001400500612810301569001b81c0a840440040e005020196100c2f050510400000d9043c034600c407403101180c0090707035115a0012605200190148440500c980c0016442030005401000140e494a1041e8428034042c42c3c09611201c2c1400e0116090280d8452402c8500448440c0420803401c0710a220541c0e100f0020fa80071262110b1400305403492070302005000c200000d10030300c080207030340d001c03402500a5001820307001d241c0d8201090070b241c480c0e4031042e031580c000b2501c0700c000380035a46101600e81810001400a14003920381d29621080a0409170006081241445c1580c0b2440482d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 216287050 1250 216285800 216285821
    0x109110f03090109061104030512070f061a0405071403130305090604030b16110c0f0301110406050706050a0903021506030129120c010c0201110a1b1e0303050d0906 72
    0x3226280d241031200b09010307168119048a03160310303050500024a81c04e405460581c0c0e000310085c14000751040241001368030103002901c02050b04180b880004209001c1c14a000342095060007501c8080c6080c041610b4002e4404014407481180804008841e10b0580b0350140006804d0300b43e601e0142400d848078030400841c3d5811040003e0080203111898003003d001c2c20044103901301e1118101d90407900e801503000c0c1e040c0c181c3c1065040784014a41520f0754164001c0c000d000103400b65402000b01100d601540c041c802081d000705035a01448594404d140c0d0000300c07900300740f13790a420783e402511a000700103600001241c0c000400c45d140c0b025481403440d440180355414803c0030003032526211811801e1a20f1040e840544030b000c00d0b40010490350034007c3d042c0c46010801c1da0795030041d00e4000d0480d0004034a0b206455010010074059a004a50b1070030b4843c43c60490340c01c0ca000c14444a08024280310a0715a0500400000358008100da15009440c24001412041d03031030003034054040c2603072 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 216288300 1250 216287050 216287077
    0xc0d050702041b0f021005070503010302060d0b031902010915020715050d05070302180301090c1203050705030304030804030215190b0607051006140d1e0201050c060901050712090b010911 82
    0x400003d4a500300c41e14035401c00b903035003c4510251800f0f00203001d40f00102d40190020b0003d100400050510300d001d080c4182089070081159000031f0046032402040d00000000004e406110703100755600b08e900303c0c000d04101e00e1000c1c2c1006031444065a03079403003440754080d100c0c010034180800d00d120384190350512036520800c0c000350400010080c00b940041443d01c0680440c9000681075240511900c00c0999100b140325099500d040403521240050f40415070601208011010005074244001e62090388681c03182411400c01c3d0800915000e15504092aa240d241e410b011000c0030004403e21981300e807041c08285807034040c0c007081041c0184940185548101c0014002020300e0313410080603a401c840140001070006c600308120303000c0c030700005052001e80501d40800b1480041861400724010f05000d481d098004021914160048500b1081c036555601480100f59028541d401c08a4010405111160360b94550790210181031094400003582d5402d81066600c135042610140350700c407070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 216289550 1250 216288300 216288341
    0x1c02150408070309091a120a0501061701110a08040807021c03080108010b010905011b110a030b0603071502061515040305030903070f060c110a09020f0c0d050c0d05070204 75
    0x6031000203900481e10450200d108082c0225820714141b2881c040c4500c81d600e01041d043c2140c00740100f180c200c8000d90701c6409020070520100300309016030300c001c2c402c03d1800302203540c2c240740320b60846141c5000e85440f90020032407204030560004a1580003500b00d07070f110780d84402c03e20000b448910030403120031704100700c55036440501d90080c4415040754060002480070a026000443c1d4008803070003078902140c0490300c4203a8440b0340800001170188902c42c1002c403500d001d000104081002e0340100e82a08012003003003d00d082c20700080300107145504000c8003050b00c040010f034684000600c3e141c0e80d60b2007001c268089a40e80b001e00ba14400101044555458403405e00c19141c1c0d0051a04d0360180c41074100c00103174110098107003001c89500b5aa003961100701d0795121032004c2c49110301242c1c07103220b040b0003041d5800b051000f00502d15514034040d40d201d0385003125130309004810710100c080c060140030f01642d20b000481c00d200b10b1030803450700540d503242c20310008000306022003c0710030009450 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 216290800 1250 216289550 216289553
    0x4030c090903110c030a060e070b0304051027020603040203120c0c0a05190e09010603020a1502150402102a0f031103031b07021807050d1d1c021504 65
    0x1a4010003046020340e6034110700300c82d90f001050750303411540801c035010f41c480109140491041c1c1c1c03100700b50009100a0300c1845580c0c02c81c1d851150420340b0103131410340007640b80103601d9a0a100f0408020780404450301845042032510307000c20011003002e4011000007002070b0442d41c0c18855605840e01c0081000e85918541301c00b669500e014000ca03a004030044c00d4081140d10342520b01c0f0404003d04c207812100c05040c0002e8040118000d40000070301c0d9210704002c80145d0b1103a2000001d8906155a81000e403545403000b8504180d280304203451f814800c0a100140c1c817004402d840303000ca103080c0100440d04410141d031801e04500150106035102d2014a0300300300080c1124034045000e6a913030856002c0141c5000c1e180d1005840c1c224800f040d002c240301451401c01d0182400600061a44050400030042d5a44a10003111a0400180d00240a4051031030030301c181048010702d20141c0c00b500c400082003542d030740c0086040641d044200d07983c1c82c507224400c00840300520340707005c403280507404e05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 216292050 1250 216290800 216290819
    0x20d0f0c0503120a0e07091418160602030d241e050406090c020c060f040e04020604090c030b03010606021f1d07080303041101050702180a02040f0b18030309060f090604030c 76
    0x15100021094000d911002a4904840c000c41c142e69407049880d6070300d03440c0c09c403407201004907000b4040d585010318401190501c0d0380340325820041200750081c580c4c074042c50710508200d80f01040784007c25100030583d610300d988444441c10a030740850940201ca6038441c030b0300c90202003096002d142d2081c1007020210788200c954000d119881803680858102c42060002c001d2a4080e18060882c0c4010a100400069104461541c1c03c070340090030071403400c3c2d00c03908103034180d0f0311b00c007103030008640c480c01c80d8201400d091060300c0c010442840642510095202d104138010250342d09610000d484440034602c0c1e0b0400042004d488600008a40c0c00b1590782c1007043e01ca410880c3c065440301001c1c0f00c20783c450f5024030110303031081d5401000c0c40c20300c820f4601d0600142c0c00c003512034152980e00344000314040300c800b410440604103807038150380c41d51503c80e07600140350020721406001c1e420900c403040168a9502c2034034400b41c954031285450340d868001040983c01550300141045415000004110b00c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 216293300 1250 216292050 216292061
    0x412050703060606020a031706060904020c0610050f01140c070902070b041214042c090c03160303020c010c061503120e0f0a182406020706020d0f0c0503120a 69
    0x71910007800f0701c0359114001d03600c039020798074040c001c1503845014040580380d5400c4a0b90001000700914100400000410100c0e00460405212035100b94140840d040b0b0394940d0740d00a00b4116660148440f503140000c01e245154421001c0981004c5100304007500c0c14401400505004202107444440c6400c00e14070051041d1015500d0100380e400d0008007621940c00c540b8101e100e590031516161170100c4280d00100c1d8003100c140300e00403248000480400100c1c141d07001e4403400d00244441c028030300806081460401d1301e20030006e0800310400000e0b40118950807801000d080090b01d6448605041010702280384100040302c1c0061030200c100494036060482840440e0345900501d8550028002401c803001240c80d801050980d0030009100c400400400400b824640490746005411403211041a0f5512080000900a00500019034108042002040184000e01e50713008149030190015100d46803410401030110b01d0b24043c03120400441e1400c0008081c08862841c004000800601 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 216294550 1250 216293300 216293303
    0xa140c061812070f02010216091d06130b191b0f020307021f0e27060306160e010c120207032003030315030f0d0f0207270905030412050703 61
    0x1001d40042403400c0019404640b46120002900e001c060351030b03507100e0380c4414200300e045216280740243c0301100075010030000c050f80b140106d01e0401c40c100d5100e5003030060315145a60352040f801c000d0341c8400b00c203050700005e80244120303507280c0324451303086d090f0742d07044005000c69401d000d034100011080500b95820b00420380d403010b005100c5400226260701c2645400781d8055403802d01d125826159040b545011051405c2c59500980794402003140030740500c44548071500442e90031b5107001241c1c04495031152084001d4000c51401682845440c000403d8420070000c0c4a007600c100c90340100b00c06a980354000c0305400c2c03103c5580304025601c06040c0412030715012404018020a641d03d4081035100c030300100558290390302e400480312542120f80000364988200000080f80d0807007270100c202c04a07404c0d40c070b40038000030805004c2c0c41c0041d80d600268104d04100301d5009107080440c60700200141d103007000304042e806400d0940ca503010b181c014800302c3e40002c0c0e03401c041140002d142000c4a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 216295800 1250 216294550 216294571
    0x4090f030e01090509011212110a080910180306020c031204060b1f020304060c060b090708100e010f030f06150b0901110616050a020f03040b040e060f0f01050a140c06 73
    0x544c5840070304c40c1c1400280302e400c0d5001001c001c2180001d0016031415011a26880c4c281030202d2081003203441d000c04082d0654007110009203090311400e104040a00d0380480341004c1610940003800c0b07200c601943d100103485a6070200c0d000e140d0710421300c11151070035130440c0c00501a042a0502030b00401c02440d80d180b24103400c610542c1076a0131400780800007620358004d182050700d44541510095001760040b14030b02e594180d4100e0381c1d030f2046003c0d4001c130350954030000320f441e002c51189c0040e40301d41c001c0c1581400a9004000e5800034498a00669a100718001c0c3c52240d24603110300540311007100c000c550441c801e0041070b030403043d00240099071000d90f20f52000b918050582500c43d0001e64408141d80b9441081c00e1f042c0380500c0083c88850240d10449402c0300e01010401c0c00d5411507080718032004000541000252012700c2c1081d04180308489040c44501014005440001d0b0a81e50078103000c0085030302c16013a8000d068540c02c080c801c800b000d946000340608580c44160454009594 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 216297050 1250 216295800 216295817
    0x6090203010806091c0311040b040f081902152209020c16030f03110f0f06040303060603050709060806120f0607110d02100515040e07050a08010903050d050604090f030e01 75
    0x40c4030300003170030410031003240d02002c14039059007000310b0240c0304c01218803d14a03070800c00000d842d038000008000410300b07148444091800d003044c05013802c502d61120803007001410850005a545e06004101c481a8400a590b48541211843c1003000d0045903954105c20910400140c2e024650028003581c1001002d0b5002581240d014181604490102400f00b11721b80c8580310000340101141c41411020000311018510203c0d4400d250100c15500303031035580c000c88140003c140d0140982c1003d403070a810107010900d48160014450b006620a02042104c11004030b11076448944600030600319180c2514a25070400220968598040d02d032080000d0700803000e0010000d020503040c113000f4880c3e01400c400001e200102020b0b100c0038040300a00c4c00e64034503034220703551540b03e0030100327110003001740409034584803c01c0030015030340e40203960f1a410b000c9500d00281e0f000080b00c040c468100c3c1c0010f040e445010110f0020040d9510041006041d40740090a06420012040030b03011b0981c2c0c1c1684 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 216298300 1250 216297050 216297061
    0x105030106051212030606070b01120b06040509100c05040f060518030303090303040303090501182f0d0318030206030c07060605041b03051e010617010e040807140109020406090203010806 82
    0x3007a15141e103140f14190040704a112941c0d60b200700071a003212000340098200040780d1510580c1c0c480a030300120704403036044d00c801c0c01c10800d21805a80110300b2101007003149814021162200007658980103215968004646568007400070703a0081c0c4080000c4840c02500e4140c003401d60341c00f030340f40040c600002540c407240c40e01e8000100d230f208030740b030502460451b211603600350b0240c02c1d481c00803111952148218032101c3d50001d00e12001c540110200301e02045020b031400c1e800103000703184040068405c042021143c07650341c101400d40e5414a080100d600708110138038012001c90304001c0d0300000010034402e0a031f0041010700042800b43e241000595568810041102d0340c00c41d1030146040e00d1071200d1001800b95100360340c0304900b17480782c900f1802e000002c030860180036001417002c1041800c003601803000304080640503240300b079280c070118102504d4001583c000d4040c010308015500802c0421041d00b074114200701c5602600c140150b9490712100000b031342090040e00320342d2164600058 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 216299550 1250 216298300 216298309
    0x108010f030f0201230f04060e0d0c150201020708130510050310030215070b011503060801140609181b1002010902011e1b0609030e01090815070c1a010503010605 71
    0x14100c1e940892000704082c681e50055410540020680303d1000464101a040c0381d002070081c80801082141c55039600c0c00c0140141056844601850051003500904d100007400c0a4418090360b1005031a851200f405500c200d0280c4034941000301100c3c0b0100e58500042c284400c1c4400703481040702c46090030303440b11000312005c0c001280e1201500300690b40c10400350610107030f03080d84d0a200c1128540750090a849c0c405644100781d002d44c01c0c0d211408103051360b180d49881802e018240c14002405150301900c00400460b102074505480760840602103036a034150030300000c105002d148140c88070016140f00011040b00f90703281441c081c40d01d040c60100500e10600c20018003581c141c461700311f00c8120346010a50800004010800e20040701c00c0d1050000800004414840c80b460020480490314580180345c900c054076040d050208185061051660100f8a25255011b480b40483c0076a1201c2c811244407244050241c803211000c007a262080004400709030688905900910a4a51703c50502 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 216300800 1250 216299550 216299579
    0x3040906030c06140d0519090308100f06200102120708250c1101050c1207051b010c1220010c030c14090906130e06070e040207020a0905040203160f05010801 69
    0x3d126100b4208003801403171010364001c941090208500c907200008803001c1001720742c400c65098001c14030010811040b03a07950b01000f400782079500200c070319840c5000d00c058030304010310000200c41f50b500c01c200f0b401309000354103542c518061203920001d2400e20a4000d010040242d6503100f01e00c40001c500080d10100418200382041555103400b46010161541a0544a40002241003020030007a08600749010420509040880044281d4411030751421500c0d004005460380c0c1a80d4042d00302e0900c90303803c0001d074460140c004019180c842101c030011035614003076409048458010512030220070314158091101440382c0d860070401100015002e4607240102d00202c480c0034400c000448450a0030500f07181c20a002070000c0c062451101060001d2702c0b40503101000a0f4046020440f07005d0340000300003c80ca10a0b075003140f40c01150340100d07a442840340a40e500c40d0361144081411910104160f050704440c246240c0c40281d1605054030300e0b03031401d104260000d001c42001044188104505 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 216302050 1250 216300800 216300827
    0x231311040203220606170304140307030503030402120705060729010f060f0908010e010c1214060d02060c0d0f0f0206090616021e030a14091005160503040906030c06 72
    0x14030502c410309a400219143c0050b411a0b000b5280c0f00009503e1486180d107840c0c82c183c1030003840e261810011082180481e80c21443d00c030358001e0408001042c008403c60341c00580580300c0d040e0740c0f141c07076210070301d02942d65100c03503000300300010203009121701601c80000b1401e200d03422034400c1c1d030b008914916800080c0a45c1c51224907400040016600030150a141c1c0840da0038803e0040307903035105481c21900f03541075280059441b0030459080c660701c030003160282035007010b080060500034151001150802171a0034004c0000d003001303205564462040e100c1180910b402c460250a00304070042540c502003543d2404584200d0b400d0303841e180081585481911714400901050399400382443d2654401017840c1700b50301540e04244800c0740d00900703000c8500c0c8403400446d6940c3e00c03400e005280a00310b11208051527000e1000041da65112084410784d4805440d00a07211714040e00d0485030402a080001d2051000040000e02401d481d00080110fa01810f00c03212000d41d0f4901c1504c003d00003184 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 216303300 1250 216302050 216302071
    0x6040b03100e1501030b040c17031903020708070f0c060e1f030902030f0a050712020f010c0804120b1e04030801060f0c020603041401050106050c070306231311040203 73
    0x210000354021941c4101442c6082c482100c51418003d0190120b0020a800507501140c07860f080009010282240340000d1410740d8001d800505800c03001c13500e0340680300e03082d5030034802c02c1030280400b8482d8042e2004031390409807141e0b031a1000d15110181900c000411030fa00210039000251b21809104040403040300900139038100d028500340900081c44080554040c160340f80350031409a00c0801c0b540c000d048011005104000ca54141a4a042d6056004421411002003440c0041c0c541828401d000d03a400c3c204950404c91914080342e85000e160030000b42d42202030140e2080c4080c0440450040044100c840d490010507900c8480c9003a00f2a409000300d01880010031006204265841000c20f4500d4040103001959001a88580c8155015500c41c00c282c03001c11000ca030280315090050140303080c1180f90800003007031180c4461700b52002400caa0303905d580e040700048800485260141d0400c44100441c41c00c1a05030200700e0303a00d50143d4680c0d49a1165244908007031080300e0199041d0f0340e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 216304550 1250 216303300 216303313
    0x20a11010e0706051b0a03260402010e0d11151c020403020a0b07140a0b040209090c01021e01090210030c080a02040f150e0d06050610090e07200706050702040506040b03 74
    0x1030f0a641a0b4001e220102d20320041e801c0840d404901400054100c6e0b01c01d036078900d15440c400300120544040108010030025040c8140030050703070001c10303140500c071080d1820010150941468070902c8007015810360030480c906500d8900046100080001c8031104600340c0c1d0100300811480f00301d0045010003904002103070b0b41480554688409802c40600c202501070f01c0e4031415441c0d50a284e85c6c25401c81d424240d502c144400c41ca403003540694007400840007082009200d40000f560751402d90009800e000150102c2d02c20f602c17082d0440144e694028104a04089010100500904151803140000388144c1d0215144400900880d402c03100c940c4036461b0820306103984002c52072140100082448601101300c039682c0c03260350761400a42c0c00b40300700041c0c3d40b90000912024240010f4044108504110309000c005039504d800c80d0018080e01d06454a108039122103400c03611104e81889161049440004d50700da444070081250a00c00e94042c00705880e0780d004c0c80140d4800000d074a134140c0108 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 216305800 1250 216304550 216304559
    0xa02120f030114061603030213050108060906060c072105010c090308070209060105210a05010b070203060112050a020a080304180b03100c030f0212160c021804020d080d020a11010e07 80
    0x110f6800e10724480091001d440c0821088a48588480840045000c65004501100d12280341104032000300000e00b026004c615110000691010000341241e2203094089907064121104001c010081e1840060a82d20710400294081c1c911a5062044680e90309046591000d24454810b92007260707448014141404203a50801121900091000e07040002c144000b45400301c2e20844200e00391413401d2000514202400e080b01606d50580001104031006c00c406001a1000103429044840307500403035401c9051031902074107101001001a4ac440b281e408081030001001c0018811035030003040b00b1075050503041017002501c80d10446542d040c2c10008a00b08000101d030003070f41451100b40740c002600684d80c0c4190f41203070400c00f03854542e95022020803030462600081d0200380d0105061078029224a07078002100110203c50030a40050260040b03421501e0b1019444201548051280e460b8011089404001d4001114400026100da9811903038180c040c03080c254550001e901401407076052 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 216307050 1250 216305800 216305819
    0x40303110c0a0311040506030c0d0204050615130801050108070b070b0712020a02030705160806131b030f120c08090415091a120309031c03200a02120f0301 68
    0x32103004441405401811040303561880080380185110305040054101d4a0043c441141c00c001e0202d40260300c4400b4410142c5e031503018000f201d07581103402080c641d6030300c2d01082c0042c5180290850543c00424885032100c0e0311400c4205032100d00d0000c1200d40e0b0b9030902c882c0d940d5154411015070103401c00071580860483c1460a40c00103c9080030301003055403400902c1280d00c103044101c010313080400ea00c02000b0080c40050b014101c10002001c11604204290b911050040c100c0b86014030043e02c01d90402104440c0310301070001d00031840112590b28100300348503100c40705045070001100d04840c40450b00596410102c40e40201550b070070300b0a22024800185514201d82c0041c0d5070308800000c4211150003001d507241c2100d01140005048101409141d00c610b40801c3d8050b0002d0211a2031620300082003907074180c011014101c805003d510070b17001130041002e01c07030740740c010480110740c4001440000d212450069003142d0003480552924030b140d01030a4581240040d0400041004004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 216308300 1250 216307050 216307067
    0xb18030f25050a0302010c030f050912090a030b04060c0e01170a0b030304030c03110328021908010f06060206130c0b0705030f04062706050901030504150e03030426040303 75
    0x61240780d03070340888082d02e415143c0a00365038202c006039100e00c03821041aa01d8050b0185903041c075035081c416401c03c810150b481e6009580d1070b4442a40100b4501101d503100c100800065030012105011400e085c28036501070142c0d20046404600d050483c28030303a51150301122900c660303000d103446250700c0c4c0400201c05012130030a510350600c0b0a00c00807010420854a0f40001d501c00d4080d40e500800705030600d404c00420703032a03450018003c0043d880038080f800642d0b00303c45070b040700d1110b10801c130840091060922500106802c0d86401200d40d03050f20b1a41c040b000340c6000b902204c3c1c8541d51202c4d0501007840c0070100030200e0114100030450801010301a00c8160701c6207080d00d0400c0c0c00e200300c041094000da48407000044019035000a0078800142c0e4650054240742c0702d1840e035050100c050035900c108010b1030304069484000074148034013800c40312030100c0f084206005682c041d003020390b6260410395080d201c0d0b107030400c034200c20440c082c038801803201c1054071203e041914546080d01c5c0c0c1c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 216309550 1250 216308300 216308347
    0xe0d140106051005070209010e07020303010e0c1b0c01030b0603011a070f120216050102011a240f0702130207050706050a020f010c0903032c190801090b18030f 70
    0x64850308042200d90f107602a18114000c6592000d4481c80640100510441e040c0c5c02503102081400a10505030b601004680c191440d02d440c0b51a0b0741c4404d869481729101d50603068135074a145a103001c11160021a1140004200342ea06200000843c420405503100071302c070391102c03082201c1c00361000c4100d0102614405024410010030700303e0310b80b2260703d0764800c4104900140c00940805135129404150071000e44000e1008020901007210002e003000c80f0080518400d00b480d2446400d20200c82c18a60070214202a40c01c3d1901545008401c458001d02d408074403e1b40b00e8450114104214400d5900c0b4940003001003010b946451415900d541c81418444114040c905074280090000d0094900e81846940d4481c401480d60900400360940c40c014101070200e604454130750783e14404000040c6070402c540a8419010104000101e00350340d5010010035400d080001e0180b080c41c444c51485888060303802c4141c8145614000d48900c200c95820340c07001420b021103035145120400301c42140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 216310800 1250 216309550 216309553
    0xc0405010c0507051e130c02191b0311030c0102030708030718030c0e2403070b090102010f15081c12020f0706050f04050d0f0c0f031b0809010f0e0d14 66
    0x1d07840d100405e00f0142800007190a584c12190140b80a05014000714428003000700200001446070000a4640c01d4540200520030b031000702079014042c42e0300c07204001715190341c131020201d07135285003580040b4505046a07220b8080c080804c2001d50001c03040303504a50344000d00038a940d607005010784494009140071905400600e20110014140302c4c0c400000d40403843c078484041c41d040ca481c081045003140103091030f01c00e121100d201a1000550001540c0d802d120303282d1204903a2004074010010724016440050a1140c0c0410004103039101c21306561000c400d03030f0b0f1600c116103401c407100700035403c821000030400300310b80002c0503080d400b5010428100881d14034040d6161100703402d8800c02e40c3c0b86080c4030304040c00d03c0100107080200010450140c200f1280891030035a02411180001002030b00f82146807600f00304051041888116040000350701401e401d03c68104100e60341c104003001c5012030712000754185542d000316402e400030600144141c40790010740c1e850000c49503030010800c105 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 216312050 1250 216310800 216310813
    0x2090115030b1306050306060d120c030e100e030c0303120a0203040602120a0b010e03160b0304060f1b030e030346020717030906131a0a050a0509060c0405010c05 71
    0x2140d40d050b0b9407036a03e1050030004a45182080c041604000001c6d0440d4815644030070040001413090404c611040b40b1420854009006400c060328008140700d00141e11042d480f500807809a00107095880c006000e82c120384071701d00c0c13503030a040d5284110f0030000040682a8001512003490360000e6600510508015040030480440d920000c01c042d101da2518644904441c01c01d56400407034522149000c80040c601c4207468060281a1085409070042074400040090306120507600180c60301981d03014200a520183c0c40a4921070002060400029003810480b0f010b8500c0001524003840040402c0001c40504000c20307001c2ca00f0a066120803a0201d602000181d1907800c000d52014000c2800941c0e04d0700c0d40c0c030706510300045503881d21080500034414080741e00300000c0d00320b5018580d5403030140e18100505240f166900c0c4d02c2041e400800303e0000700210207a49802030360080c00c50b00d4003406944c50300c0703d080342c40d054229a000301910341800708011640c072034009500840d0140013034405 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 216313300 1250 216312050 216312071
    0x70b09030712050a020d2d0905031c02060c030402010801050d15050109061d090303010603051008010219030609140412031104090603020f090c030604090201110d02070618030209011503 81
    0x4a00c03046241080468404150000c07030307075014000c10581441b540340c48804450642210381c145003400d0250440071692038403205455004001c140d000d03040043c01c41e45150181a8440d409200410300c80006018003000b14501e22080001da81c0100e40c16114541c1e560300740820b00c120300000190070b03102904010002e4075561620b1195038042c0c50502c01c04204142400a0441d00340c11500b04541084128000c004005001200703880c1501c5842c6008541901c030518642c0006100f0780044459501c001100c0601d100042c0c102c1c00e0064044d02c081c0300f0726503904007001c1100d006040d0340d810101a20005000184200c41d12807007800b0905000031040403500c140d40a98005810165440ba43c034801481985400c000090071440100d8041c54a4602014012407500001d408c080c001c9458032195400c683c042c517540c6600c5c0048400b11a41e40014090007503507520180300f0314003c50748212000b822290a510010309a0b074010300b040ca0580d20700a0700d03c20b4210040c0c0880e040565600c600309 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 216314550 1250 216313300 216313313
    0x506070c170316021603030e0f010203190207090f050c070605061f08040b09010b0607030c02030304030803040b1005010f0507111503010e010f060206150405040222090c14010203070b090307 83
    0x140203580c0c044004420440a0001070f10b0480170b8120280000003022080000030b0740860004601601a13881c04014400c40006038038500807001c0c0350501044540140912590000b13008040742c106190a00c80d900280f80383c81e044403000c0d1124103c094040102e0000308072a0307081140c202c0e03030160041c110400300c2100b105e8038540400d1020700041c0c0d001c0910003480300090742145c01a40a50003000707104180d00000e00c503071240384402411300c00104210750030f56505005880c010340d0082895a5a49003516112425000854581900c40148103012541d9449045540a5248141c940a142c164551121802c5014103200141d000121501410410040d140594004c11070000d46640c69410070f603c00c045da40300c82e00040110741c002010000000c0c0040450494104180d9001940e0340311800880d00d250852041401100f0300d0070582500e44040c0d900c0482c80d5400307001c0c081901c50b01d41c1c81003060801c0d250143c6005030f1051200e0804900c0d507027002c17604803c0f02d9080300e203400b00ba40c4d150b5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 216315800 1250 216314550 216314557
    0x190e011e110f16031202010225030f020105090c0d050c0301060306091515060309080919090606050f040302060a170a20032403010f06081b0901030506070c17 69
    0x2140000e03164203403444442800c000b0740780e81c60906800342c02683d04809081d1041080c91202070980d0b00c003070709480c00840c000c0d411074008140c0b030007901001068000d10020180108072003100000c50074408000520710620915024060354405052201704440412182400c10003054415002c1c001400322655800d10464000310310072174000c9440406400c0c05442c08001e8181c403001541084a41d03811002d00103d244152007980c20002041103007420001018001d46e880c19402192100d40000040302c600c3d03982040f210355900501c44181c0b1803000320345a010344141c032440c0f014103000a100610b016800750200c2e0b290f91034035003454200300030907005442d02030319420b082a030744294400f440901200300c0034100d842400c040d4510f040400301b1804d0f141d003c0c40081041c40c92884005a140d42c203410034120b0512504007400f00c29200c240312038451002102020300e1b408070780c60035051410100791541c100e81c0c10601404040e600d8410580b04100080d0049800002c00140c20f0402c10905014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 216317050 1250 216315800 216315857
    0x180a0f06080a11090c070c051507051b03060114060708160b07030203040605010504061404090201090f0b0d0c08220f0807050606040c1b11030708030c03190302190e01 73
    0x3c0c4000808560a0001c4503002902da46141d03081006030318080341c04c5401d402c08813181510f00003c10040e02d007400b00d00307001d41140241540274011804000540466074000d4001c4120f050b00c202d42d0f0795512130041c40d5803100105070004400e01004000c81d1000010f0f140d131401d6884c80ca0041901e694035520000000c480400109178044103000500c452845418098031050f074041240078103001050300c011000981562041d83c54800039401c59104141d8000100240e808503a05552142240241358006c3c03011941c02c103103014610b43c9064402e00002d8020140d004400a41c20510340311fa03101400d074030030141d90baa5410603003040000d050000400e1440c3c040e10140201d818814100300944200004810810580341c000c82c920512903007a0504035580600c1c821103401c50003001c1380c10000c603640302c1203042c080418000320281020000388200c0a880684500e2415200015012402103d0050020000768004c0000c5140281c45074003800784141403540400303000d1130741034500c1c0425090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 216318300 1250 216317050 216317063
    0x903080907152601080307050f192303030112060f06050603010b0c01110403121b03080a0b0a17032101080607111009060606020115050607080f0d090c03020f180a0f06080a 75
    0xd00000323000091203000d8600102034081e03c0003c4404180c1c51014040d04000b8050034040f80002c400300f0100f9120700d00c0400b411080d01d4907580e440d52450244000510b064a18508140090f807088a0500c03550742034880c024010760440c2d007014282d64498104903000c3e2029943d807419000d40e90b0303110024100561080c000d44203400e401e5080101902d0307264004510300032403010030740d000030341010f60140d00c854180f2000440c840040000b519000f426488a01e0840d4508405000180007100800c0100c00a0411004843c481c60010102d8102481035400d581c01c003801080105104120061100080c030f4111150580251101402c8413a10304003255410343c2d6080401c0120780a0080c409446003610300030320040e2522000c02e0180c843c40c0001401007000042c000d44142d81e440903117030480740c2c8120402203152207242c0723201e8810071400240d00c90703e42c0c1200348000d881c1104c42c41d41c103ca0318860358149915140f00240141a610328600c90780740c0c0f10f0a021400d901c0070440040541c0c0100d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 216319550 1250 216318300 216318307
    0x307051c050f010f0902090a18200712080c07030e040b03060f0412050c190303020f0408030903060a021c0b0a08030c010b0a080a021008070e090a09030809071526010803 74
    0x49140c14182966014001c40b034014401d007481988c030488031604444028410804081c0113041600c01402c0e00325017004070078907080d000424943d1110103085840c0c81000300c000e501c0036482060780d200720100c5200c2d90800c000c1240c03100180c410740e04c4c07002c1e0030b40182000c0381c1008580000b0381403400880300829590061000c000500020f401c0b47c510303007561424138516003212000b9141e1130b0004280742c4022406000101e804040c4207070f04545004e00150b0240343c9640d1a141c00c562254072803d5820301c83e100b080007140728902c191085416031207400c40f1242114202401d088054442d680180c0d5114184020010b084002400103100284040000040340c8104408000f0701000030b4000b445168040000c403801030303d811494003030840f42070411820300e96840d601101c803200707040c0541d60440111f800340003801040ea00721035039007446510f5200352a6140c2810b41d64440c01da20841e001d1a08400c0c1218103039000b884102510880c90580900f4551070002c1e58455240071b0384009a01d51001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 216320800 1250 216319550 216319559
    0x31303020706030b060a050f040b04060203070506060a051e01091502071703030c03042003070b0706241a090a0e010609090204260309040908030601090b0702060307051c050f01 77
    0x140101c0c0003404080c2000c0010741c1e01500456150f00404d0540310901ca400035010494410840c01d450080440d882e107556610780303440c0c0c001e460f03800401d0300b01c81500c2004046001c80c0b6062012200390b0750040c04040281a04100505800325007440711f5043c8507001c503002c00d9607a0b019403c2d19580c00550010300c412464001d52101420502002e0740043d041801070080c03400750202140c1e0441e070841c084030070181098507081030b0000b00100c4140c0c140305107038000800d00c03035070070207070041501030002089000c0152002d6801004a06810329500300c03d80d0701801103640c8a1316009411001900250030010004081400700078550000140034103038400400c004da622180010140105d56415800d042ca460403148400e11480b4125801008410071100030b51420030039190280001071041c80341d00c3d082d007040c03a21a4401e07503000f070025441d80c2d0040fa07004540e00407a003d041c1d000e0091483c44e0b50b66002101e19800c0001065000c44402070703411412069401034030b0181200030b50444465142 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 216322050 1250 216320800 216320803
    0x216020915121c08180a05010c1106070e0616170301092d20071104150e0a0510080a030e01021005090c0f04020d0606031b0207081b03100203130302 65
    0x84200040b0380c0808060700e2800b400c914000f0000003a0304007090309460f0580004c1d40400408101112841000700d080b051007070540040c004101e00303840e0b00700c0b0011007010617902c0b51011030b401070100307110018001e0942000f0340100320303114140e240c451402e0035580d6070002040c404046e69840000102c014000d0340414410b150514000541180c194985051a1401241002002d6030500c1d44d4549001e502005107000d00d407201d081100f19541c0392694501844091001c0340e40e54050391505441c2c062103645141e00000740c4922003d031007850780d6100000030152100034515a020310140400089014040044086a41c802c0e01e0761100012140300092038102e10300420701d0342505010074000500310110b00a012a1029241c0402c1100c8540c0070901070320500000b00480c82c0340c0040003c07003a60640c0603041d4000101203015014050100882e5a00801d010303074140c2e5081803d445024a8480d410b621201c0d01c0542980c41c2040208030202c121303001100c2d50540806030301403040c02c143c0d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 216323300 1250 216322050 216322069
    0x415050d0b0307210f0602030906150a06050403140a140a0308060a030807260a030c0e240c0a060c0e090603010c081506041e050a0b0306130216020915 66
    0x10941c014400b2514105115229500450460141c041a031001c0014845e003e03d0b5070703008039007041c015580c9050100c0007d0341e844080717070808115040d00c038241450703260030030382c400898040740d8641e42046e09540b22000800c0c0c403030104490500c14201100b001446031007071b07580b120000c403002c1c03c2d0041c0300382000307811260004c0c040351040088640c28800179450f070080d2200507802c1205030603980010301503c01c10100e440145141d44001150000d0036990640001b00c80d140180c1d0303440c0e022400201031001040e11100100180200b0840b84a4a00b0b81c0002400922110600720b0304240841e03200e02c0c007201c1c590080e0300b00181d4a8200140d5a050030090550070030030960003045401341c1000c0c010140d14020f8191910b8801c405000d41c1950f0307441d0207031805050068140c00e0400c0720300c01d100a21301040d03c0b500d80521028040001c0410114064078401c1c20041e00490241c401540303084001d50109502c0340244041c243da401c00768445840305845500c080086c1a030262a00301009840d60 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 216324550 1250 216323300 216323321
    0xd0209270106150f0201021201030507060e01030e060a090317010803030a1d0a17040509102d0509100905070c0c091802040f0b0d06050601260711030415050d 69
    0xc0c103010040101804003828502460743d40e107068095420003020032070192282418005004911500110034000080b03001c0c800c440140c1c41d8550303607107010001901542c614001451241e0441c2c400914207420982101c0100b510038039154034901d0b40e0410509103400c0a820500083d40b010080184c9041f862059a0301007030704041898144100380b05180c0d0700c1c2c80360b4000400203c0a440c014403485401400d0720082c00d80100340d0500c07881c000c19900e501030658840d02a800c07468038220305103581504d040b400d07000420000001a18100720070300c40b0119000e4080010b00303207605000540804140b2906008106a554048902e95036083c08030750118544c0101d200189003104100d013000c10f21070b1031754420303a040e80c0100d100c4d2001010310b0014500b907640c464000100c41c401c1c500300a00f5900440c4504802d80750308480c0ca2540c0c1d4009229042400c00d070b90b0070020080402c8485001e100b07125481c0c81e10b902100e1800d038407403000d02d03a030203016950080803900204444056540c18000e1a1005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 216325800 1250 216324550 216324553
    0xc030c0c0f03030c0212040306200903030406080712020a1706101209061407081b040315180c080705090c0c0c060a09030c0b07050d020105010303080c090d020927 71
    0x49201c0d11141c44100e500c010080030706650340c1c0030814a90080c003101003501d241c00022a202d550f00d0500601809c032070001101c1d0f001da182c600c2c003480c01642080d9184800c020700190700b4281003074810341f50300d10081c182d030003844101c6507503c0000802e8002090781d0080da40c1c8100c0d502d4100010f00385071600c003801c402d105440f00d203250b0241c90f9000c4c61885480c0020b41d000b00b0b0304c0030642400c000030300e004440f880759421540108488a90007609950040c56862280303010b2040d01c2c6184440da00450000400306000d018580a8081450b00b000c0120140c607a64450b0075011070760b03040c070155010350040845401440040040d0300e000c01070b207035001000340700341840d10507103000298440380c00440c07a52043c08049a07286d1034501c11440900990343c40081140040d44801005034a0b402001c01100c281c40b807250359024191040c01041e048940c9516440042e031200c0607600c08a40000d08e145030002c41160125002d40d0320030f078009002d081e07040076005045190700000440448202c400d441c15 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 216327050 1250 216325800 216325817
    0x20712260406121407031107050703030e03070b09100e011107240c0b06011b1b03110103021812030903150609060108190c0905030a060c020f070b04090914100c030c 72
    0x1312030100004030b500624920700090b066840001c6400c0f540142003001d0107038442c0c41400b20416810150700c0c04003210840880c0c20299803101740340c890344600c041c030680040049003a904440d020750048c0074002814107103c2d49105907041c115141410a1388900c50301205100d0600c3c0000b44610a400c03020a54940303010340e0070507070b1142002c104c4003400e4141000701090b4034031101725442c2d101f201e000e40e1144041e200c000d82c00601034107060301808142c0d0381803400e01e41016198020700c215441c446000c81c0d220340c40100d02c030405c0b100c80300c00e60342058103000812001c9102c0e981440b5000703603030041c419512003500b440814844c201000400a5062010840901654910905022040c1c071081500480c92440801d0202c0d03000c10030382c0c061038143c8103000d2441c00300b00035500440050056a0f0894240840340104581d4440d0b00780700b2a18140380c00c10080c40804419000324100c0c90148201a04645c400c188035440d00441c0d02e00c0c0300e42140c0e50780300d601c10194580a518501e00340d42c60f28000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 216328300 1250 216327050 216327071
    0x30b120304120215030a0c02100615030b01051b0115050409080d020c071205100515060405130603020628030501051503090109050f01020d11070302071226040612 71
    0x54a2045000303074082d0310341030011082159a44c4620301c00d00d441005800b0340381d0512010500c0506070280c14040507001d600c0c100b034104c1e9010b01c40c100c200d5403512485541d4004004d0117400a01d00f02e202c0a04000080014031481c116034925000d02428000001074604600d1403034072003203104c0b81c10044c03041d42000b0741e18010030b9500040e98280300341c0540040c5d64144044d041490040240c0c4a941d090b070340011140103100e030100714104011a118018030083e45c480101c15a07031103442e909158440b0007400148051f0a0040c1032400c0300b960604001a03ca840b82c000aa940d0004981c0200c031400c036101e061000e03101c080f00d4442040c1c190070180b2542d414140062002c5020012202d030400d004000609124000d4111042c52078200c015180343c40105e2a100d030203940718010481d40c0b82d0030403101050b107400d5041101c00803905a809401800c1c10310400a40002e081c10040d28591402d04240740c00040b040b03c01c0aa48811000503a52649064005000d0700340e180041d140c8145001045003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 216329550 1250 216328300 216328303
    0x90b0108070516021009181b142104031806050f180a03060209210c010309170a050901081614160f06090201080105030a050a1b0909060903030b12 64
    0x103801c07018508105884000490310b203034012080c8203019501100c05628481c01e0754008800e1000d032196aa1110301d0070700c8181100e0143c0c2e09001101c4000d804584102d0380452041150030110704015803010b10384010451110900703d0810191442c0c4620070045c030003051340104503a01c0b5901181c1e803444001c2c1c40d01c10040c0040c0150300b004210810002850342d9513407402190403c0d0740d034008085132a029200e0801100035041115050f02540065240302902c1c01d60418220100c0007800040c8043d82001004602030650703d102120030809600d45c2030903100c2e0f139001a00141400d540c500d502d0300c4c03440c030004010500103418103403030460b542c02103800c817644844020000550500070700c1da6800200f0381e4428128110102400110000c400101082020341007030103443e000360781e50401c50b42c0b6501015143e08040c50000e069a014019440008000f05100701e00b40c2c40032600005070640d624401d00a40c0c103003c0d4201c9290b59a00c001204068041c820f80e60702c100f00f03881e2244107808100040703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 216330800 1250 216329550 216329567
    0x2070b0316030e030d15091e0e0a02100e09070f1d0a09061d0a0605060712030b0a0611010c0206100501110102040306110c0d0203031009090f050105010618090b01 71
    0x30504510300440c540c4981c1e0003500900c0100301e46108a0b81c0d01c5280d101100010094801c25410110812200040d0101d49024007080941500340c45005c041503101900020304180c2c40d104d0341030240c0b0034400c0143e640c02c141090899a161100c01864040b00c0070403103083c000034455814400d078002036000d81c80e03001e540d01c0c0c02100718181e0052820a40c0340000c4980c0203580c01509014280038020411115000d01e60548050f9140c0ba8140d039160150a00301f65910303801003a410000c180704010102c1d407030301c55000602e5424100080c069082c940030401c4120150440404550403148009405109109200c80a4207034806003541c0d0420000030f0010701403500c0b61604010003040c02481c003170310a5040343e00569100504200c00400340c070008185800084014440d401140c1d80c40e48014000b1040307c0c0b0801d03000702d0b00d42501b82000c09071030082194200a4481c00b01e00e4403400c0003c0d8013482180e010304030a465038102c2422114800a001a660708001d030598107050748491540d0f00480b04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 216332050 1250 216330800 216330811
    0x5060406080403021002122e0b09040f020703021207110a090b01020c0f0901170f16030b0708040807020607050a050f01020c0c01091211120307150c1b080a0c05061e010602070b03 78
    0xa0410710340115001114234026412240d668a511000020211341041c0104200242035074180301c040521001d4800301d001d80d050240140e0443c605d001101d8440d98020030000e40329038041030789401541d000c90060310683d0041031505a507140d80b0500f070368042081d40b50040f01150302000781d51902010650040c810b00c41c5210f4494221103440498109101c41c0041d8001c15089503095800b41c4010404801584000d80d19241c80402043d4054420f0403031a1050350070080301441c10303059909100c0e80e43d0101c0802d0380c00b4000c014441f80014403e2103145039110b205030005d40c9800f1101c01c1c55050400424500f8184860424100030b40403107420700d14295500000605488004076000c01ca81c5044541111114000002c415007044105001c4170b83c121110001007222581d021010b9070007941d010343c0030303034900e00c010003ca00052900004001a440360700d45824008000e98515203051000c1d40c0503400e0001804e00312805540030880c107401041c1600c01002c4840c58222701d0b14203888040c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 216333300 1250 216332050 216332071
    0x1f06030c0c05010e0a02100908190204060302061b0105060f0f04020c0c030307030507060510080a1106090402040806060405340215070201050709051005120a060506040608040302100212 81
    0xc031158468040c0541c101d800d5007280082c011445101c1010307480742e0b42202c0403446282000c40e185011841341d54490280c6258a008040d60074480c0145200300258240c1284d100d900c480002c00145c8401d405003000e40082040324003c0705102000c2401c1d59001468240a4500b5481143c5a80c2ea10040c1310005d200c265001a5a40c044c2883c0c18101200d42c810700f41c262000184003030405501c032006014139400380c80108640e0700c82c80a402e040c0d282c03911903c13105a20004901000c0f90204148480b91640207041c0c40c584043c20010800360303045940007050940200e401c01c00f03e400c00d0702840741d20560f43c40c00c0c07042c5048101c5141040c00b081851031f94042100308140c080684c002c0103500004a00700d140c1402919000700000d002e00804c4510f5800035400c6500010a810030742200158403400d921400d0800c0c986600111915000401c004003c680396440098141c40da800100b01030130940c0c0d616802d51900f4240a441c188010000103091481000030905a03202650402d40084160b603 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 216334550 1250 216333300 216333311
    0x3140721030c0318111c05060a0b010f080f0a0e070b07020f271b120402040c0f080a02090604051203072015070f0b0708010824011214010f02030f1f0603 67
    0x2c040303190011650b050811229008180320f0600c0000031323035180715034030114090285e00060030044500391580d034a02004a000d150104940d20080b42030703c0c0c3d2007429010000340868a0b41c1c5041d00d401c070154041106c2a0000440e2030640c14850780c4450508404d40382004078880100c0480141540c9044265800e6106404580780b2050710403840800b2680740e9038103071a41c080280b00c0b200b181d810340c1c040388110324006036102e0440c021503000008900d02d0325082070390b96442060a0195010b5101d40781e00840c104004a0181d42ea094040c103c48044802035484181910b801100058038090301c00445200c440280311503604c02c0f03c0340440550699019868400d40e140401c1c1d4014048001031980c05980108400c4907403000744c603070407198444100c0b4200008403100e03041c00780b102402c1860807003600c00140a0b00a4075140200c0d40c6224440da0360800d608003c0b428211080c4200e5030f9102a00002400803c05501c241035420002c141610b00c0945002c51480150304c0e81445464103141e10b03003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 216335800 1250 216334550 216334583
    0x150e070c020105040f030b1602010c14210903070506060a1202130216050a02010e0f0607020405090a0b0108010c0f09080a150b030f0a020301050c070f03140721030c0318 74
    0x44083e40c0040024214600180d5100d1a00442c00901100d0b1360080c042c51001c0b11042360700c14022400c221885031210000d080c5001c007400c1c540e0380850341e086105601c0e5000503400421909655100e0080a4050740d260751151030700d0382c00c2000107842e49211f00b82054061002d18442c41d20545d403594116011444071000700b070080060300825205d40c5410103580e03031610621034081114002a80700340d842d000c00d141c0100c10030404114040104ea0000414414040141171075482903422401c1682104d0403229150b58003000c52600340c00c00b40c49651150146581b050304460030b480b0705580750130001d08107410400300c199114408440542540d1200440d07000251982c0e20076440c064024068603143d2503001e404036550800d56030204e00a62900340028000c7e0788440035070b01e103641c2c0107505403030152458500721207080340c0c04a050780300e000c2000395030009200c04c1c03043e1080780160701c0700400d40ca04903480601101c1541c00346006140c200182207014502c0d1141c4c56400c554002c030b0360700c0100c074039 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 216337050 1250 216335800 216335807
    0x50d0606080103150f110d0f0506031605040504082a060f16200706030e12030903040302010c0303020909011d090a08190e030102030901060f080a0b01170a021801060201150e070c0201 80
    0x54000000c1550400100316183c1001c5408c01d40c480180d58105101c29142c180c10f00d50388000c2c4605502c40640240424402890190071041d0420b000d10312250420000580c4602c01920307050b4050100414403004010100d401d2005a610050400d0088001e00d40705044480c9000000d100908000c2e172151102030503c01c194501c07480d542032500f01c03103c480d00d6440c041c00400c0903d14840d201d21601c0c016881c195140c400300d80c4180400ca0196082a103903500544807180d80c140708a040c19002e120103202ca888586401d4001e08408810b01d04c14018040324030483c00014000060036040504140c2c007054400003110002c610361142c0881c1148181000c654038134818501300d41c0355000000f4400100c4054126500341c038002c900b00c001031070396840c0035079651104080081041200c01c3c0108540c082c0841c0e8221401050700c181d1380e041040740e000802d458441d0f20003089010048005001060b03091140c00b00c03034612840c0c8880382d1800c103100700c1250312000307101c0b104001b00c1080354804c5912 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 216338300 1250 216337050 216337061
    0x2090612060106050408070b070206040b0c1009060c080f0601020604021908031b071d22021804050c01050a0804080304020a0e0c09011419030e011b050d0606080103150f 74
    0x1420401d45400d5611008002d00c6980175101d060000c1c81446408500348400744102c8844580c01841d5528040c506400214282c002030305080d414020b01003c9c0c650312402d40208081c891288100084000210038081d000320006400603040c044d2240c10011183d07000901160495012255400b044103007c4425841c802103400081a600020400459134204001c00551a0418500343c0341c4880d25602d101d041e03002c403180200100c15540003c140320990407801c00041171624400c0c0058925290007040c10303074801e142e68650340003d04041200740b007010300114040410900c2c1151030088698401045001d0142c8083e01d41c81d40003001c2011036982210240090244080741c0c41d0a00c0c01201002c880c0c0c00c090b800502040c40740108840e902d2004044031402e2161105000800b170a20f0b00440c003c01c44001c04903029903039803040100f071402c14844000105003c0c6d807115501e401c4030b0b107800c042c1d0700305a122406125003880103000182e0740c0f0b4000040904044000a045106001ca00010b4007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 216339550 1250 216338300 216338329
    0x507020a0b0a0e310b0a05091311030a0210020c010810141c0204050103051f094407061107120f17070e09100e0610021609060503120c0a020906 63
    0x2c4034020120078040554001590f80d06040b0f41c1c000341b01c0e41d1030003070142128044540e448500381e080c2c5501d00040c41d01d00303016416078025044508603034443e4042000410410042c2c00940d0240100800030b40e8030400c610741c08600458502e0115107002d0544080c81652000c488c41117002c5452410f0114100000008030350b002803051040f540d5130300b4080d454501e00d07800441e00d0a4007007440c41da5045140110000c0560000760b803958091509090f003940054206110852254107060000c90740404820000c0070030340d1001c007a50389000389000740803911040d03001174000009010039404030300b480c0045001c036202c41c10a0382c074444400e4811280f041910300c1c04280700e1810707818040c07107550000e284484120284c03000e05142e02d507806143ca0380c01c0c05219a20082c41d05000084281c200f04800c0040c03101540100c45454180e54420035948640e900540710301907545408224516003002032848251001d01520714043c0c91000c03d5440c0d50007500043e0140010700d000c03072070035182c04001c2900d80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 216340800 1250 216339550 216339619
    0x5190f06020d021c02120112030c15020901090f050a05040b0105190203040504050a290103021308010b0102011d03030109051b270102070b0405090a1b0507020a0b0a0e 73
    0x15500381480341d00940200103042c900e6020b000315600c0c0703c1e0b03203842203070520720a1b030140d4910b5a203001c02440300c0c1c40140d5021820004143d6480002550405c81d01801d070002490141c0c031000410001802110168000900101c9141003007066440300c1492006480064402003405400d840059030a032090001d20002c90742421000c42100382d02102410a1702e40480c5d0910541c0c65a0f01500140c0c0e030580002804246840c44881c00182403510300d1509040605026041403088420580040485e0303100482d01d0f511900400fa0542c0d0a1107240c95100364009000841c20001c408590b03203000500813a090940c0c0c0b44046280d6031506074002688140c000b50383c0b41d841030125209604511004c41c00d4610340c1048290750036035800410020180c1c0c80000c0300d0f03070409281100300074512001410414809940700d40301d01c1022201c42d001c0e00c0c840015200c460707407200c641c4180b1000800962102c0c01060050000daa5044c3d401003e120159000b02c96102c83c230a0350440c508400e0307030000b60b1585c91 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 216342050 1250 216340800 216340807
    0x15030a2918061f0905030111040e07080411060a0801080609030403210c02040603050309010e040e030706180b070801030510060608010b0714010c0e091303020303130c051801180905190f0602 83
    0x141c44d8090020700603940164000c0c84620803840000f41c1c2e50269004840d103003445400010320141c800c0b410076500c5405a030211264040e82400700d8040d501c400d4090b80000c0d0800b0043c070110408102c2141c00102c040300035884c00b403840c1c850283c0b01d50b038076142d14070122400340da101903a03226a45ca049045d800800400c00e503585d0b0720340030340d40b0b034803902041d07002c03c0400720340403030390310300351061641960441d005140b07006541d59441c00208035910f07488260280f5210785001080149405510030180c0c7d4071f40054550550810b40d16246d000d01c0244440780c20440d00740f001c16401260360f411141e4500b08140c8a000c1860b040a41202001c1d41842030742c603244a108400380d2003004010841d005a488680c9a00c0708002c82a21302c10215018015a0040000c50801c0c20000d003200e418034062450302c03032240e032641c001640804144006d901141d02a1005000309103880c58031990054903580300300000d6074296600d03500d0715812011a05103a4510a00c04140020040d541c0c240070780c000c200715134 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 216343300 1250 216342050 216342109
    0xc03060c22081b030606030a120c14150f13030c030503090f120904180c1e1503020a080708070c0206031009050103060f06211115030a291806 62
    0x364502641c0349544a807140e00007040c0b041c10003150510540d604200c0e27500c52124035460940e40303103513141710454000c000b805110712445424000c41703002069412500145003405100c0f103142a2029007940e819003101c4d0a14000280c000e82c6004406034141002d41d169a0740350321140c06c1610381465060f19004d1844a134084991000c000c0454000850f410000020b0740003c129210003117007402024892790100910040848048070b400101b03140f084c6100203521070301d100e641c46801500c004003080e004030711600b11700d812030485540700d0120715010f14a8a051749000b4004d00c201c40010380a41c1001000c1000c5504c0180d00301c018003d03691061000b07503500d103000c2004090a07469014101d203060b102181002040c03444d444007022890615100c0e26141c1c6038021581c07194400d46a0101160003010102c4015902440c45000d14440004d0445070030781031505003240c0b1616100c45400e500e07040320856520844089221201c400c0c020440d80d41c1d040201c0c040c000d41f14107114000030066005c66 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 216344550 1250 216343300 216343333
    0x16141006030c0801021c0f1112010e060603061008040606120b0406050106020102090d1b051507050706020c03031b2409010b030109020d020103050402030106050411040302030c03060c2208 82
    0x2411603100b4000904503681d1100814200c0c02a0307950880d4202000081a0035040c05804c01c0701c0da1442880c0005081200e442d00c0c6500d83d101c0d012141000140340e00422407070400702d2120303a01400503211580b9501e0010700181c50b4507280c480c01400c1c02011404102404410b40c8444050030428140d020a105a03042034885071400719000c680c07007805d200003ca035041c03044c0203541c810440601480d802e00c240f0f69460f00313130b0803407140718507041c1302c2040300050780d56600824000b469407101d03c115a42c0000b4203119003000059007094055500c0701b02c02450382d031000070441305000343d018040d0340e4086079000074908101001012407039421401c403118608d00412080c642c003c0c0d103408000c0000101d04070038103090b64450035010f54070008a241d83d00155009810040d8440c2c40100000780c5140c0725000101242c008807d11051002c02140510442c00c0411030416540000c800078559460640d040d4510751090700304182c03109250303422600030407403003041e16005020314600380c400401a10150f10b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 216345800 1250 216344550 216344561
    0x4080102040e0618010e07050f0307052805030a020c0f0d02151501021c031d100612020f04110408030d0522020a150909060b030114060c03161410 64
    0x40c0d165481c41010840c24540882c0006503800d2442107032503540e02c1d10030710700c1621b4002081d100a00800b0869001c0d01c1c4c62715030042d44914440c0c7c03641d5032920361601c10174000000318009611069075820302c00c09555008410360b5032110a07403101503528031416108905180482007515000d1042846119105402080708407200c04081020012a0307074100d4403d502c409441c2919025800403502101c500055286071041450300d801d0202d1089864642c07003290a84042c0c2507070305900074140349003104006000f018010b02da040d240c124801e6072500041c0c0c010000d4031805119030707501c02c0482600c908034070030b41c0e00403c0306106803500d41500a031513901030442101c100c2540700c0c0c40501554207082d400c21811300c003500034042c2c44010741032008034904600c2201d030381c0c003e0000680c4c0c00683d05070180030300c0009c0c0c8098810301e03490f945000340f1810030b51007000703036107115000501140c00a581c0c0002528000702500d04401013440e141e003402c0c41610400c0e007000d6514050889030016088d4a034014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 216347050 1250 216345800 216345809
    0x91a1c0204090e070f1208040819020109061706121501060305010302090a05010b0306040c0216060c060b03070605180f040e03211905060f09010e0a0c02030702060403060518030408010204 82
    0xe203c0002494440b070785075000b50082c40d0981107806020f100350310001e9130541259102d2140603140c0b503150011145444c150410034a000a0f941d8a19021541e00425800083c40e00d400d011460102c0030000d0082c196000f060795006a44c01000d40b600300004000340041034120000038000c2d542c407500001c01621003400241d002c1d14003103002c03401084541c41028102d81c2c00d1043d607806d5494100070440680060710071082184550003420b920b0200c40f001080c005c1003e40c541d040d80c09102d1404034282d0384d8040900e1b20903004110b0400ca10364000c0116035103c050300d0780d41c03501c81c4004000281402d05841c80240c00610b040c807402c0110a001005054036000503048500391042d040124284c2541160300c80848201600c000707102e40c01039001030b50030840040028180c0380201d00400d03d00c090036400505c0c58141c82c03017400300b00f22452164902d180c0285c400785152103095004203065118902c002800d40380d4600004181d42c3c00c207803814841d101e00806480d0394550f00e00103c1e010350024040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 216348300 1250 216347050 216347069
    0x2030a0201061505070308060f130207020a080d020604020d0311031912060506090f030a0b090319050304020a03080309100f02090a090618020304020d05030304050a150c091a1c0204 79
    0x8001c10302903404a10381c00d01d000f00741d0341c4515142940d6402c851001d002340040b60802095510b0b85a00c0d0794207090a602d20100030401600c0b44402c1c010030a407104681c1c440d010036042004003d0b211607000c41d9103a80701e50180c9400d5800c0c41c5924086410354404500726030b16000c045002d0038401d130312000f2a1160140d640d10f220010b122001418107d80141c440d0070346c010b408110351003060401c8681084600c1d4000e01f61402155291212141c1e0b40c4100c503980e00640000500c0205001e0004a251000c03c8926015017545070550224500400724000600031050100029003100d104011680d00e0042c0c91006105140960003900040c0d0000380d0020720400c400300d000b2400c2c031007901c10350303040724a10003420100103400c000c240001e5001510680c0c00028000000c1d0103d03108000031801940310b68010300903954a0305203030070000038543c10880c0d203509041c9170400c0c0725449003010050f01e402003140c0341044080b040303416061041d03810b03001c5900da03504500500f60017507601801c1100c00c601d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 216349550 1250 216348300 216348311
    0x30b0f04030f1d360105031903080703050a110a020f12070c0e09120c030d1a0d1410090b190e0a061808041811030603071205010f02040602030a0201 65
    0x104140e400d80003850018980102c0c041d24010f6030301d4003a03400022002100070f1400f003042e181640800c0706620b081d000d801d0802d9000100080d003800c00060314180559124092a01100e40c1c0041c2104806801d101c201038843d004540416055801401d21030201c481c0c0760b80d1179800000c065210002900c1f820000e014a21800b00f50300744110071540080e5100d01550030306c40c1040e0741c09005d604064a198204e100d0b0b8040040004010002400c8258070b9400842d00c80c9000d0303556000b541c0c200c400402050001241001c0c403516a080e10b4140c0d203900c4104014560403200e4690720300030f640c1502c4601ca40c1018109810710150208841c0590802c0705c00200224040c0500001ea40c40d0075510041a80094642c00110307140c1e0b4822070341180d54150340d10b14004a03895540c070030b80040e0402150600700340c030b000840d00035600c9040000caa1583c001400c1d4a807800c0041c0d1188141e200d42540380395000c41c404104442075020780d00000c9010811901c0d02d07100c1c0402513407900000c1000740550301e0720 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 216350800 1250 216349550 216349577
    0x506010e090a080d0b150408010608070b07110f06030a0603031404060816052101180b0f01050901020c0402070c0510020a0b06100c1703070e0a030203030a18030b0f0403 74
    0xd0440c0391040301c1e8030000709502002d954451440707030b0107502210b4505940f120ba880c1c4030780d11101250054074002c4801078469082c031440f00d00311402030780f00e40010350201b4800c102d8503203110191005660030000202d02c4c4407098010030044d4041c100c503154444800410081207138001d510080c00d9234007035510301e07444c0a60b140328400144203500484011a41c4140002c0c8400d403000c17419a0488039514066051009950050b000c00e08035081c1c3c0954403082d04018000e400e1030408000c0d404010900c01c0c08070005510108481a0203540303035034104040000d002c82264001c10044084900c0a0400c56880c446414042100811402541d1103108032a0020f650140b00081d10950650450700130146519524104201d5078004001c0200b400810301401010a62620025641000e400822031ba280713000d05008201c8104c0c9030748a80b117090b9110050001da2800000d0368812902c506000340014559451000c1e0010aa84010810700d414020422540124481140128460b07202c1c05110001e2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 216352050 1250 216350800 216350819
    0x607021504110f032b020a0b1305070b0720030307020f06090109121a01060c0c06030c11101e0e060109110c0f0309030115150804060f0608010213050a080601030803090c060301030609050601 83
    0x381d5010701551180c82c0409c070740303000e041c901d0043da610803030031500019075805d81404140c21040043c0c60f41d1009040c3c400000c0482c0c043d2106101d01180694076000082d40043c001e140100a070f9070241070701140880b1164003c3c60400d01402054442c1080540c15241c0b850032032a10291195821400070000284607004817181980e240d888065280440d0821504070000c2c00c0805094081100d04014030b18001c4c1d0031b0010100d005005940440c0620001c07900b440c2421790303400404400d629010002c16566004552941520300114010803c6022510300c40c0c814020380c240e40010303008410b455030705688004021328403810258006d1019420402c2c81040e220654441c0d2041d401051000500c418490b0b40b080764030501ca00701c0003450075006051002180c1d42740e00081c49a03035001801400c207203000c5a40304024141200c11001150034603800e40c0e00d0394818032008100aa01102007000080180070100150b400071707000a032613680d0383c180840548030400e4103946a001d0303140081003c508 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 216353300 1250 216352050 216352063
    0x40f0e0c040b0d0807060f02190206010b040f03081b0304060522031505060d0606061706120d0807050c0616031a033406020f0607021504110f032b02 65
    0xb0020441c40500701c15031038003561980405804c58450340d80720160740112000703101908214444400c900720f10880e80344003a01d09070b01070b08421001c00050204210b8bd400f0529008140c0e640301c0302003a150302d0b401803030164510216401030000c0c0408500480c0c41c680c0400501100c01d40404180b210083c80100c3d292604214080a85695040401e141d5109115003142d43c01c050b014091020b801403e854102c02c90307800750000000210b1004500103403c009094694001004854070681070030859050340d80c0309180d107021000e0003005000501554011415101551105020b6545500d8030314106a0054044201e01001c03e14040b4804003005001d0f4000d812844060008c0000302c40c10a0449802105e04560341f8100164401c002902034031104c0020050070250020681d010307051944608003c401400c24003150b0000d40740b1000d40000c5030319144c00503045400b52004881c00707000f240b5a00d144c8152150188210b9941c400c503540840640141c6043c9440243c81d84101e4000413170b201d03130 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 216354550 1250 216353300 216353321
    0xa0506010e06010f0522030606080111190c0309030f030503100602030a210b04091211031e071a09070f1a042105070305010b01020c010809060a05070e040f0e0c04 71
    0x221000121003100380280020186c800b441d80b4400e5045240103901001c00489800486405440c3d40d030401ca1000240076910401c00d018101904001c0c1a0441440c08030800c0082e0b82000380c0381d090501414000c1034204080c580009140c40c0c0f10105040207083c40d4001c0d1041d00300b02d014120005501440441920042c640d60f68030803a0a404407840a1440300510f143d080209070b0303c4c01807601a030388510a4400403849107440e00528403104d00701920038001d0442903031440d0010037000d942c450700300d5189200c40706400e21040d01c440983c00c059156040c00303040b51100c00501c4091104500c00062410111a902c04441c09129159841410412615500110146024007041c0040c0b24081a0b507001c44403041d042c0014016540c48003031500d40190700595032030759101960002564180111b40b6aa402800c248201d800c00b0642185d940b0801070102c1c002a9640c5c02140446104459101491030300170010710100c50f080c502c800080c40c003111103181c0c0780304110b00001e40f802c0a004003040c04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 216355800 1250 216354550 216354557
    0x90309060906120b041506021b0105040b030c0705100203150307060207061209050a0b2403010b0f01030f0906060605040609090b01052505240901050402060f09210a0506010e0601 78
    0x98084144000140200540c0700368086d4503103d500c5454981811080024462980182030401ea81112203600d4000320302414104a0304101c1400901004c034101ca8115560f0f60169541c0c1c092424818104402c07801242c00c5140008103002c540003451a03d4a5140d070308809032030020380ea90341e041c0e0f5203240612804000c6080000c2c031141d00d003016400300101394050003e0b2030041490744c4c1e401c01c400c44c007140c803800f4404083d009c0680f401a4421107000400b4182c008212103d4084005100210b481300e2031410151034003016600941c4d542c205c410219030103001441460340302d807005070154006016071400101682000141c1c1e20b41e43c020701900b00410b071601c41c1f808900c0441c0880350680d078001c030550000442c402c0030001e04100605002a201d407143d0300c0c1840c41106000400900180000c50243c2c104003c0c0700c090790302e88003250500c103c41c018030b42d0380c3e18141c130109010740606080c4480010400360348010042010400300c0076207200d1006c0d01c1c183c0e03072201da42d400144016140386002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 216357050 1250 216355800 216355817
    0x70b1501032f0403020d030503071101060315051306330e010303110703200109140a0603022a0c100f0906031a03030a110f010b010c020f040603050f01090309060906 72
    0x100800200820000c0b02007080c4540743c81e450703801054010341c0d001011000a00c0002c03c0104071507216900310403d5141070003c0c000c3e9403468039078503c080590482d8120055440e000b103a0038284c3c0328241c82d2203076032026080c0200e0300c001c50b40c50b8820100d02c00a20f803480c1c580d075843c00c1002000780c41c0c1082d0f915810b409a1203034210780302145c40350007140910819201c2d00c0004030109040564204080062010105107450608001818041d07a6440000750105111030142990f03607012101c03080d201607190043c0c440d1654050b00001110700c05d09200d070400c551081c0b9500e4074000c2005c418450044c0da01c424039020144c2c003100c20071034840600c030014084d81c3c2c050224510a402c48010a64090250a12501c001e00000d0540e841a40a10081444102e06590300071050100141018a400080140e494900c00103002d8007681200244501c110000981c03095540d43d0048001e1500181158034a00c0400301d040d0082489040941c041000f44000286681c410315100b01504c1c0c0a03940c0000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 216358300 1250 216357050 216357101
    0x20d090920030912031312080106020d032a0e090606090901090504081e030a05010e06030a02040f0204080712141b1311030c0a080a090f080a050d02070b150103 70
    0x14580010708011034070701807604c0c4500281c05003806035020f0000002c50b0100c19803140751450050110000030030030b200180f00108a215000704036070b280903080c1c0c01d02040c01103006014002c1d41003000040300704441d84031078000c24a6032110800410150941c1c40788010340300d1004200302030040c0c0d5441030b440141c60b0010300158440b40c004607045032140c01030381e00f450800254a22001200400c4400070036010040105013411030040ca80144a1178044d164503041c0000881e485610300d01001e800340352035401c403604242241d411a401085040180c591694881e00f203258440c8005000703545c40c2558020702c00300c0c40c1c008103182024640c03d03450703070a11440070000e002180c1000451a6140c4e556443d14284030100c480c020340c0b0504080845540e2907050318400303448480058403841d0503500c0c0104440010740c2c4141500c1070140c00500b40c0c2c2d140c001c000710031a102c0c4a074841c0c00010f03500100d00c1c0020084034800140c06100c0c41c803034681245000400440446a42852641c0300c1150300c0c5000c138 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 216359550 1250 216358300 216358361
    0x6140607021009030b0c0712030905190c0b0c030a020f010c050301090e03161217191113030c03060608010203150f01020c030114010806070906021b0f10020d0909 71
    0x50800c0d0741070406035143d5540b40c43d540b01d00501100d0750142d8a00014082d020042814201034000609090800c9005070035220365a6440c1600c0c03c03035404001d04081442400240d0443c540200340142486580303400340004140c494014940000c094881e00407c54070000c4180110703480c0684640e00c10b41141c0c40c10070600c024003101000340456010030041d00d640e2455a90080c3c1c81140120a90110713601c80140c010901c038807001c40100003020920920008000c0484640b00d02c000407d000320704141d410204c10201d1045000503698024260400030400204044582c01c0745d0080340d04100803039494055074242c0c0700c00c4890408007008481c1e8680d072403911000748407420720180304541081c02210046401c4550601c04285198056001000382140030042c9592000151034100069464039101a51b10744104001c00c10300040c0a40c00b06441d00c1c1c840d170480f90b44000902c0c1d06404440c051020351100040a1042c00060190307501103201d405a004a4111000748008240418003040155 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 216360800 1250 216359550 216359569
    0xd090e0f070e0d020315040c0503070b031602030909040b0109140903070f0501180b01030c09140c0d15030b100f0506040e15040e1006120809120a0501110a030614060702 74
    0x1980c3c4905810140000f5842c100b0100b105280f038011040c0c0542082d051030010b100090340202d10030f41c0401418000d200140741507903046910050149068003180720705905500172040703800d4005c1900c04c2040306005a40c194641201c0200f80200b0100d00303407800701d841c1c15104940c3c0c0003066008000e00c03000554200d201300400c6004000000c0e0850030380a1041002410b45410741c0e24422103401801481000307103180d0010724402c1010011001d151084ae5040040206607a100e03100102d04081b10b07210603000199211010000c01e8a425207910740a2481c1c101912461046da502070000301d807441046e030191091320710081445040030301c0c000c20300ca036514000b000c407611030520300d01d084d815031100e0041d0f801d03079039a01003c0e2100010410b907a0084801c02e0b48400c003d01400c10700d278804182c0300c0003140c9003801d0070354150030300443e0142050320781101d042c4000d00c0d84d07183c22120480000000003070855809290780500c0420b83d611424454a85040c1556912207020042c1c00014601820704 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 216362050 1250 216360800 216360827
    0xb06040216140a080d09020111071203080901110316110606060f0d0b100e1003050c030c03041406100503010b06070c09051902190f05070b01050906040b030a050d090e0f07 75
    0x1203c215010a640d20f0246410403074480d00080e840d840302c20110760b0011105c01884240c00d00400300c9a152802a840b00d4000f40b5015050291a1010900410007074109105448100d00690782d00d09000b03032189036000506001c4000200075418101400b1008905180583c400508081c00c0030040740303500d21582d010f410084a1245c3d02c00701100d9a4442c610f03e018100b61649600d10784045403806d000c0d201031800d07144003c051405c410403289000b04000c0e42d4200c074104104940340c2c1d4070703441c25050769042407074081214403801c0c0400c802e00010002030300a580e010b800a100c0e01c9841400c6c42a00d0240c2180189051000703030050010103034035448998410810941101c40325500c617002c10403a40030881207294540d24407444000d503a003211128114050924205107848201c0e02c03860b4400c14103010b2644600280000705e100ca59803504400311076030006095440b08655441c1a0740d58901c094501800308017903600025606101e049400e224440c4954860180d0355070040c112800300c072818a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 216363300 1250 216362050 216362053
    0x603070b1803010501031202010608030309060123030109060506120f030319060312030c020c0a0b0909090111040e06090112080a180906090518070f061223040b0604021614 75
    0x7051101c0d9902401340342d0007507005400810000145900c02800c0d1402d90b00051015071003001880a039400016000341120751008403003011002c02c03c0d4519820401c6138007280e15600b44000c041c01e01405901803802040115801007520041440a50700d440320942e4040194005100041e20708000307103000f8800174400c04002941d01c1c0c907583d8224070702c0c800ca10108006980e0340f40005e2900d0301088194007811040302d100302003e2030000d00107528454800094020b01c00d8001040201d0001d41101c00651000240301c2d403500c0d00e9490b03260f440541120698801c86821000292040c3c80003482036003a0380060005103000f41e80c0c0e81c03d4071030180800b0b4118074640c6907035000030103950a118140280005c5d040102c1c140c10201d601e43c1c100d024001419039141c2100030200003036080b05e03412104032125420213030342d1003008000310f4001380a5440f00300c1951405d22181e410454468200a01ca280304071021070031a107905083c00124080d50740e070540d01212a040c40c10204102ea101c40650036203210 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 216364550 1250 216363300 216363337
    0xc0815270402190833040201110106080304060509010e1008010b071a1503150f0123130506090c13090f2c07050414060105090109030605011d0f0603070b 67
    0x1c80040ea007100f076070080c899904071000e101c1354507000030b03e204aa0482001d030041d0000e41c0805a42c03c0c0c00020744000d040c415204e2443d0503510081d08500006c01042e01903d44440e07554101030281c2c3d00c115030841c001021070811800b5450481d542851508580e40c802e80527038204100a1210360056900f40c4d100340401a01006084049007000d116115242070ba01e00c2d40d83c0e60092501d00f1004599540038000640108406a46030703d400c1411152140e40c0036108030000f00316056200e07020303039100e030308100c8000110500200e01d800c091b008a0003038031a5001d913500c10403140c05900a0102904c41c0c148402c01c08c12150383d9035003090a0450381150005010580c0c48100e4624141405001d40c2c01440c9001c480c044900903c800750040101342c1d41448520f0412500c000380001c010600f44c10f204010402a49036440340d0864800785a01c250704000950b111541411001c209941340803556903280d000500c40400d1041507402940042c004000c003604002000c01c0a810088004d4012a40304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 216365800 1250 216364550 216364579
    0x40902040f0906060507020f0907030b0d05010c270303030902011b0c09060b131703070b040b06030d2a15021c0f0209030d0804050106090c0815270402 66
    0x620081008084241111010625003a0202d081c3d62aa5002d6028050240030080c00b58890800d45c0350460000c0f50043d50750395501e10180c00501d415040075801c004807105580030090150300c6070180d508207482d1900d010f0301140c107110744020440c4601c442440740040400009020b03402c032600580c41414160a060a2060f0310b039413a1a1000003a03400102d1503e08102d8240350344100006480040c8105c1e1400c1c079100440d1000c4240e622030400440168056401c00000c1413094428407070f48100d02920500b06800c02265080094820324468060040300030000d5000d4580c481641e03032131803e16146000703040640688200149800e8495922901d52048980c160b40b0041c010701c1c0c0c000d80083c00e1018401401000c0310380c4c866241701078504c1008042c0c0b4654000440e51035011251030888040d42e12450540d02408855101304165070920002c05003964000091031321a5a070f010324043c1c0280d12038100901c0382c062074240c10340480f4010201c480c40b0312003002968424000b41c54003c013154030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 216366906 1106 216365800 216365819
    0x150b030c0f070804120c08010515090115020c030f1018050a020603070c0605070f0e091501050f0c0607090515040305031b1006030b1602070b07060207030504 69
    0x2090a40c01c2000b19002c84014020220310b0380380400c17807846c041b912132000303002c1d4042550902d4001900035004089507400c1c0d100040040d081c030f03407030518400201e5070f2014480c0118001e41078240d0b04c0d610104454a030009c0f08c0302c02048070b0701c03400600c402100d007240060f8a440304101101c6001c214006020070056804a403002c2d902d44600c403091350406104180205498208000c2107116604024007003528106c075101c1c05044180e10b030410940d90811aa004a40f0a04e8210700c5415441080542015440202d00c0c0e407030b11030085880c07850600b00700e410100007190301c2024416402d008040c140c1082c600f0b9034050505d0b045554a5440c1d000d0075040300c02c954504008440300e41c00402c440c00111a40c0e0501300201501e03030505060f030213021107407601c000c1c14035421060003620004a134801c40b081d50300c1040c01e0444540da4003000c0d40c0482c0040e07003007140602020500118 = true := by decide +kernel

theorem cover : BRFrame.Cov 216187050 216366906 := by
  have h0 := BRFrame.cov_init 216187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 216187050 ≤ n) (h2 : n < 216366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
