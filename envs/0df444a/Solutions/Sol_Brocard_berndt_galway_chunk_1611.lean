-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1611
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:51:32.384722+00:00
-- url     : https://prove2.me/submissions/d6f9429c-379b-4d1c-8483-153a2f1884dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 289568345 ≤ n < 289748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 289569595 1250 289568345 289568437
    0x70e0a06060509010e1c050a080c0d020703050c091801021b0d02031c02070f0f08040e10082508071202090c0304020a09090f020a09090b0a27050c06 65
    0x2043c400a0064500440490b000e02c1095100c0d001c801e0480c2482c004407508903060b60301c00750740e9092007070180d80186d00c040380c584586007d0600c1d06200140e0f40d021070340c109014088281520b010403070050000b03400070913507000040d10354020010070310060002100302c0100320000d281c031107a010300b010104c0341c400d01590401e200b035100c10704000a10340ba006100c00401a5140514a0410b091640d030300e502901d000b580e01182401c116181c00200151400780c81c8601165070b600400c0e00c0e00a100b401240764580108a096000140801d6a114842100410038003101c0d00c8907001460300a090303115032103013042100c900d0154242900320940054960398068039528003500401c003a6151f034403400c941e0503541e0030201c052100000c84071031001d9008007180942a5504003002c050a0a030b8400ea071030229083c04a04940018814489080a6001400209240c00b006000e040038142d00540e894084c0c4184444141c0e40e22006200c14400843c0ca80394280104455104440c02c025824000741e403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 289570845 1250 289569595 289569607
    0x307090203070516140a0c080105010806190b0d0519140105010f06050706020f030f0708070c20031608010606020d090608060d020f1005030a140103021c14070e0a060605 74
    0x26000013101d9411151698841802940e49000040c68014915082c1d403406640381c02400c01405500810848002d036009002c96600e41d00e040303845420640e401c101012100c0f0804080c242da9410001107044014075080b4049220f0302c1c0c103410580c0078500201c162440e01404030400600040034008101444020052581004002200000d180c020001803240100b045000c1180c5501180d180c202d510b1030030340d03c9080c02d10030180503036003d40d00754010440220004010307a11450745440f500e6084400d4200380c80398148400004403c1e050299058000c81142e08900b98200380b20f4401440290000144249440c2000f800d181024094204000007444100040c0b94440c00c0d168015000700c1e0400038143c01480000c1002480b0341719540c019886644c40c03904142c1000c040d61240d00c2c050418403c05502c2c4004210035071090100035880111412003000c0d180303080e400d504850b48285034561074840c00c00081c520345036182d84031800b454007810030070201c201140030f01781c000d04039800e1160810f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 289572095 1250 289570845 289570847
    0x1a100801051003030809100903020c0a05040519050c0f070f02040605101d06091207090606030905070b03040f08040f0609060809031902072c090c0306180a0b15030709020307 76
    0x2d04910002e030800c42003802040700c021050116241c4102405800c1150310514940a9200c0000750f0314181b013003242c500c0004050419000b914400c10b00d1190f00310703203001076801c040001d080203805500051720a01217410b401e24204c00070320030700307000f11744442304072642d07104000540d075413034000b0390155011a0f003552207150810242c076225411480701e80f281e00040e0000c01c1490140014441d48441a000b4664035040c01107a18401e0300c05120061117038030344801065050781c00c01032008206a100d440308120090099000c0d640083c8200c4101c5460090f80e260300c00e00b07400ca50480404050880b004004103030300300303001200400c641c3c00c012145181101c0c4440d04c0c1d018a4080b6100c00720100f214255492080c020000a00101c5d92102c0200c40c03440d40301d05000a18103c60309a0f20300020100f003041c10002a01e9043c0c1c0d5000f0000c04096440e008016115200e5802c0c1c0f01d01032080d00000c10020b1045402c041c8030315086e03603507600c410100c0400c16151060390b90240a0580c81001404005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 289573345 1250 289572095 289572121
    0x40b010c06050a152402010203160c0510060e1e0708011511030d06060e0f03120d02040b071416051c0212010203010801060f0603290301091a10080105 66
    0x45030004000a0141e4400401501409106200080c044100503005c00c401080c44002c250510048004000c11480400c0036400c0703200603503134070b129040c001c0e888583c07640c4510881001c1d00d02c65000ea03898503c03501007000660b41a508038549980a4104020354094038541042c08540402070004090500c050040c024140600418080070000c0e00710000803030041020301600c400b00801c9a61b03806040d504a4028500c038040d80c000200030300d840944d01e1410340c50201100c00000c0181c80e050401c101c046115a0001e0307132440c82d15800340710003c0c058a0b0b0201800100e4003401402202028000800c3d080c000700c000300c0696070b11219800c2c070551310b886000495000f41030305a400c410034140006000c0104d60940121290b000100120745c7d44010b401002c100c0358941007a2203540e49641040c0c1c113550050044502d4125100e54410901c890030315086030b01e04010b00005180315a5840345a014405000d039140c0413580760080c01050082220200014074040d0002c00160800d40180703020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 289574595 1250 289573345 289573367
    0xf0303060a0b0f09090f0114180106181806090605010804050c010503060d0209040f03020c010512070507170c150a090c0b0a02070e25030c08060409030e0d1b05040b01 73
    0x2148004203944039040f68038411103180388001030104003036161050140d0843c2409000f1321001d1420101e418299082c68260b4581243c2d41c240702d250140c0c00c0840c01c0796507284844401c054240c0d058800a18102c03641321781004100c0c101c0011a00a00701144c030806d4440e40c0c2d0100e07041040c50350400c00806e0f4003181404c094103007483c019560b034588600080d248105103c02a50145007407003400101700c0035503c84420184240c01396010728038003a00655042c0250ac00e003a41c0361032001c0020702c00c00d2182c40101706441c807800bd0004640700d1980d40b1105900000c0a1560f5544555110030020191141d120381c1b009007004240482d600a541d1048060300350720600d00d000001042c1501090300030f010b00400f41c154503000034075074941380b0032006403102500c646100b08100d51501444d020710030b00070780700e19101030f442d204101d0300d6402c1480003d14600c0401d600b0003003030020188059440131034441903180107490015002180c10100c1d51001c056a1110784524034203802c0d0308807660001123000c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 289575845 1250 289574595 289574609
    0x1a07082205100608030c0f060601120c05070602030405010b091b0717190203070b060f0a18110324030118030c050114070c0302100903020712111002010e0f0303060a 72
    0x40c048405142840c0b0300a24680c00000740e509011000c1009000000a00001401c9404032140100d000b40d4a0391500015660540050080c600d11070512600d80c01c151510045403030b0103031500b010740d1112004ca800554007200e283e51951801100c034a0807040c1140c0092203020140b0355401009201440e91050130030090000172414044400f03428980103564100000d540c0c0751201d41000c8a00940340c2d4003401707044510034000c101103041424580c0e82003c26200103040d050701d146c2031003111020040e01241615205840300358501190310300101460091176603008413481c2c08010000404800d21000082d4040da2405520500201201410071110782c1c040c10640080c04150078820302400743d10004110040c02c1100784403000394000c0c01d210007a806039007980c00c042102e17001c1e80d050b01c0720707a4000340040c0c0c40301400384031020a00101c0c0c20080d200380c50030b054505091021900b807a44008118015035507542c00e01440300014030540707080c01000340c0510f2a614108000172114483e600400c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 289577095 1250 289575845 289575901
    0x70b16090609060f020708030a03020426030a030902061c0606020d03150608060109031a101401140a0306051503010330123c0207020d02090702191a0708 67
    0xf04d0550007400a007020704690010b4940d01d401d0000c0c094007a40c0a8400c28441c0c5142601c0c840c0402000e030042030710450385101641c5000940c0d00120040c2c42c40c40403c1e64000700401c207445629205940c0403004517650800810190302d0711601a09150403010b5260605045c544800d08250a004c914403e0310030908189400751601030048660018a0f04000c1c1003090f806180715a141940c40464400c240c0610741e50f0713a0588408400c000344441c0041d16000c51841948070b0f00c4080d4000113490071405610b4005031081d03440e8009501000c038000615102c0c580000140240195a810181100a2200c07001e9103e18810380c100162500440307041d04000d09000c110525003000e400000a03400d050b03a6a03200500403031007010980c01d0070505010001c1c0d0303164400ba4071000307500a85641903001829515040540d4080c80b06034800184060214060203c0c1c10070000c40e0398003680500b40c02840c84104c0c2a8112810300b400c400054440003d0168140800100840510007810101801002c0d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 289578345 1250 289577095 289577117
    0x120a050403021e300d060e01060e01081902090303040b09030c0604061710090f0b210a020f06040e04141009020f0d060609060612050c071110090308070b1609060906 72
    0x2139900714207400c8440c50405000030b02421500e003150809016919901c801490b540d03602e000c00d0b120032000810850201d4050b40c002805c2d4a50240308012030120b0600c003500d0540e800c4006800c507070064101100340300c008074540d441c0d82800c10a041601134151142c0e4034042c01c1400203030481c02001e01c0d41117895013942c00203a0200c61039142400401105d0824410b130182103031618080c1001d0160580034203100c00403459186c80040c040194030403110f01a0442c180c0d15000e20040d0403075060b1090304507000b00b000141d0040c4071500184a68040d107180307100c0000f200c04e180d0a04103110300017154030b401d000c0f801c40540c3e10410007501500f01220040c03040746052400d44081c05099000b41c484a00d030040009070039802400c90510649100420811036940060345076803070158080152610381c6948040c4120b0400045505880080c1d00349980e450341d480c2d40e014095070100c0c05c12207e01c107410381805216100c42180d903400d0380b400d00300040c50905042004040c56024415001000403075816 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 289579595 1250 289578345 289578403
    0x1202031509090a0f0605070f0207060e0607030504030206040b0304141212060d0b250201050c0904230106051207030c081609030f0c0e07050f040303030203060105120a050403021e 78
    0x3c4411850303404103554200050f103051030002000204c9054022410400c00350700440d201064100955010b612a110810004410b0201075000443d0403018031000300000320150356140003501c0204400c100c0d540d92031078640b4007881020100302c42e04850b0b80c01805030b240c7c6c86405d102a10030305410f040e0915140e644500014907403070342c15a0080c1444007240107200ca42c14148a00c0c00110105c416452000070030354008a080b03850440744480c110006108c40001e82c83d140c2c0003540704540000100d0368001d03a0300b890311a44002a488040807078400100305484002000c034481e80096641000c010842482d80040c0941400900c04820702d0303654000c40361420300402d15880990307001810764061451518202c040c044480c0a090071a40140000606091183c411291401c3d0780b140b501d03040620315901503000e5040542400c0c14040144400d0210520114040e407180040b260302045906207810082e041650f0100c880e400402c81101c08400090000b415104103209920300c40300e00810740071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 289580845 1250 289579595 289579603
    0x605031f15030902030c0d02030714150c0f0709020408060f04020a0902120a060801061d04050c0d03120507050f0421120c030906020c130e100e03040303120203150909 73
    0x70418004030005000510030754540c0c4003070380d0f9038425021901d001281c18100840c100091000961550020038240108510324040642e0080e0140c40c10700c0c800d0b4071010200c00d035002006240e055510038424104024070410109004001800e001c5107032900b80310341c07103480c3c0800a1411803d207070000b020901319140d107120300000b0203002c2800c40d160303a1301720300b090306594094032184000e5041500200d2084011f100e058115a0030041c03600d40e42ca20701c1050300a0803c000c00940c2d0320b0003031000b060341135190050031001413442581ea0f010f9400741031404000301d6402400040800c0030611280144182c142c0451f03041c3d404c142244a15040c032071308004400814910014024880880760079040354103d5400f203072061094580c00c0c04662208806caa55440c40f41074160b0001c18490140b02d283c0c0280c1c480e403001240c2a00380c8450b05c1c102c14580042d03514a45002d106688001400c0003030581c402010051012501c00c1503140d0b007480104d01a0700c50b500d4407110b100b17280e0200490f4464070104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 289582095 1250 289580845 289580849
    0x4080a08040c05130f060503010b01092c0411010f0e01081515040b0304050601090c08041203090c1e05090108100506010219080a0f0206040209041b09050f1f0605031f 73
    0x305182c42d010303040c000f090b01402d50f03410b03681445403d0100c01f0520b460180036071070002a040c0d40300c82c44a49072810581c01e40d070291000c02d440e0400312002d40c422500c2012043c0c4a140203144118402100340001130092102688640411a074601541d95603a48107120a8000d5403810318540c000d500b0340c0000d4010000b0001c1b070030f101c4c4400030f4005225881f40b40035500c560702440c26121340da0b070384401582c19151082070200006d03082100140014544a8a2002002441c90002610030240e5900d41001001d038202c1080700d00400310081006901031802c001420043e40c5d20b140c1545002c80c4135560340c0312420110803087d03c1d440001c43c181d200b0051040c0c41c0d1694007103289801c50720305100110741d000900500014007803001c172214840c00024154007030369024008600c03554407a194090070780903001000160f000018000120042c59014140c010074400d03140c2c5010b4103003803000c503e460360040300c0c2405c0d850109800708115900281a00d921448118212200c0148910389684a01c419 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 289583345 1250 289582095 289582099
    0xc0111011d0a05010e030c0a02090a060b030f040b071103030415021c1401050109030f140705040c08060a0509160f03110c010c1202160303090819021501060804080a08040c05 76
    0xd018410714800000d8103048141c0140000c001c0d00f06211592500e030712a11030320031718035807001000c603005040190509900645c1c400c40024004d8a502c049106a0300640d00030740103a80e0340c3d050006000007400c9081c4c00c40c074141400c504180040480235107078000100003078482e0103190114803079544507030100d0780245201d08a4140b80080d44c005038006041e81d880c20039a003540300c0008121940145007100a9a420040301f07601150380c4e9550300c44c80250410700d440e0901440c040051691200c0c0290904481e00d520380400501c0c0401c14007800d01c8140d813015228103203581c18858154925032070024840b40c10300c5c141c0300000700c101094001d010060030b80840c240d00003034405c90090041d230107800c000186988404000302c0292a00c003c0c0d0141030002c00040440c2c014400c0001c1c0070768450700403103125140301401c22001005a00c80c070b04600400d0000341c1c200d5013501309400e19804586002d050f072070824003154146620760995900860b03101809100966001c681480b0120050000420b40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 289584595 1250 289583345 289583381
    0x507020a0818040c020601030302060a060e0a0209041401140f0f150304051c080a0f11090d0c03060603050f060f0f15190605180102030421021302030c03010311010e030c011101 77
    0x4c800f40007175441750240b0054005008000109040d10306034080d41d41118051518040d4544484031030100a40c0f000810710b91259941c102c19540c034001d018200e000707115500c5851258503034242805000791500d410542f20340450303c4070400030b40e2129502203001025112481e160355991030141e14181c800c940d650100311669000c000c407550302070305203449101c000500b8802e4100e140500001e1301c000760680545200b060100750300c03030304010141340c441502540310080c0070350340d0303031541400c6480300e42007585e0070f400540e200403004104000054101d8400507008003d031a200c080072041031405051070036045c13000c0c41c980c8801d03505c1203051044002c0f01e0300c144e818a41d5070304003c0d00582c02415281c0f610300303041c500d40310a5070012081e2403c44515101c40b0402848a01c1d003d01c0258084108903440880c01041124000103880514400d40c80301c844142d91b54114107111509400d03802a081c1040366019800f4401d807804a14500048800e08060340500140c0c8142c0780540017000140c515034003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 289585845 1250 289584595 289584611
    0x7050f0619140f0604050709260c030703030504050d030e032406010c05070911071a1b030103020d1113090b010e0903190c0203100c0206190507020a081804 68
    0x55000e040307499000d40e0346080140c440d1031541c240300c00314100d80800008441d0b0000614604158201540c070800c945400d00d440c644030a45c1d0751203001d007075101103d8040e8000f00c110400c801048a00c00d0308204400910040c2e28541c0c0c010518400c9010380c0d402051509801e60170140140000322220350001c064465000ca13254098840300b4103208284069400c160102d6100d501604205032016004000741034842e00b00900500038246e0050140300c2c1900410a90b40803814501032410340c50001121041d05090110315801c42d0303061940f20b6074684408000420040ea1802807000b486980500d042403a055080c1c0015030209002c44881c1c4400d0600c020081004400c82c820390607566503800400003600d40610b0180d884c05809841003144c00017032a00078540c0e0203000ca14150a2000341128141e90000d9546015219804050000b40c0e00c1a814021400b084441c00c95035031216640400c100e15003080000d595840000f00035110032000500954070348905100032003a128090f105201e244 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 289587095 1250 289585845 289585861
    0x90a081513111003022218330603060e130b06010e0402030a02120a02032703040b12090f0d05091c05030a0c030f05040503150c0d050c1306030b130207050f06 69
    0x35000e4601d600c1414010101c0c41e80c1a1b001425240959841100c0201661700b5184410010302a41400100303040c031400c400324a10b442c0400c014505800c14160312241c62034104064140c9900f03800c0300b01d01c1400c0808202030304401d5440301f41c81c82c0d007041d4508103e071186070050740e141c1c007040021a0000d0000041000300d01e86500101480c24246942c42001e540b254080c00c100e00040d2030300c41d448558118048205080c0303031107140c8101e0a84040d1303480c0559441d41c5040a910004010311520307034001c00c2204051040c8510038000c0ba240c8090045000c01041c010240d00c1141c4002d482078042166102c84a4071150341483c8007603022040300e60712065414080e0554100d91412000070f40c01c210310141d9288118180e504580c4007034020008900380c650700c0380040000404030b500d03a0340140802060b441c5107000d2207015410b1aa0090755135a02011594644c1403d600103000780750821110a0312a01e500d16144c2c0c2e00f008140700180c6481691812314145100008028034908c41da2040c40151 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 289588345 1250 289587095 289587097
    0x609080c0a06021803011a0405042108060f01020a0b072003070b0f06150405010c02040207050105040c0e1308030a0c0c0503030703060905010e070e012d05090a08151311100302 77
    0x101260b16000c500074400b04d00709400d13217100508410003940f00340502c0310a0309050304515000307807080920320b541207034940e2644401c5140c400b01780300081d1014103002441c1044800011411030070b102410031100140c64840002c2c0018200c1b8080001400c46201e00e840b6071032008411032000800c4e81d580d84030b0b504002c000798500360b8051603240590408070700d042c40c6c0b00b68030100e290b05641c44181803601c0d200c01500c100400038401d9070440e80130007029000540a2040340d2013580700c1c01d0303507000860400081040c00140102131010744060160120089484841501c0d8051408031020402000110f0100c03002d0913840001080c500c8080103200c407261305a000790003a180300c400f0401080c7e0740c0352100030040b8420f407540c801007000c004040302554842c1a11049080d984a4000d4402c1407002654070450141c4110600080002c00d4015607450a108100b00a0a9440041c419409400e83c1001080000b07882601410701d11400c001c10010030b14450380b1500ca0090030038060098241018010b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 289589595 1250 289588345 289588357
    0x9080307030c0b01090b0102101505121e1902040e070506030412030b010309080d0213080d1106060d0c0611010e010c08091014130c052116030b040609080c0a0602 71
    0x61208250004c83c0f220035a00c201102c1b8a0140e0081038040c500007208002405a801000d411443c0880c0221352611418206580f4810000080c8000902c0080868520301982e002c0c0415400c0600301600000e4500c6403181200c0d012a0005402d4041a040520300306c5a503010f0303900b0080200c00c002c24480c0b44003d25416550070b450034800650894011008c40f4039201c401001c0e02000e010300640124176a000e0030303e003084810160704440d25140034524014030711004800044104990396040b5038244241508101c01740c43e012100d004a96070f041c000842c1c0c0c0507035002c20070b8000a20010b207909421078a01c22526400070030004064a200805e84941141d12410a01c520034851440490701d1140c458034135a6607440901d2900d9110107407580110441c01912030001c2c400c0046200e5880f00e03120200200800d641400c05d6064041d494100326001030140301c9250b81c0c1e00300300003190607446020b40c03041c3d2101c40011400600e1a26080c240216600850301c0c2c85411040b00800040d5801812 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 289590845 1250 289589595 289589603
    0x51b0306101b08310b030a02090a080705030d1e032412021c030f0e06070503031003030e12061501052809090c05040909020d02091504110306030c0f0109080307030c 72
    0x81c0c181c0401c506018213070344c09604028556401804000c12420080030b190444030880c40581381c0742a1500140e521800f13a002102c1c0750b004410200f10500e820881a91a540d481c24490050050000c50707500ca80344211425041c581ca4942007240c0c4050542050030340c15071210300081250302e92640b00030003100d8800490260825038041c0c0252008828042c03001545036440980d203500109049401407010141250807d2080c040b10002603c10310295200e2040c42d00d0100035145035060061580200e0784c0c1090040c01c0112300607090b0390000c25030580c000141c1074190171400c2c046004070f81c0e0b441a01d800048140c3d14803400c000054903950815019400303a56001c00c02a1204001c0e070031100f4010061000c101c0c00c0201b0401c0f60500d8100641043c0001d10401d0b404005801040110078122001d02022003440e59840300341c40d146c070a03219003002100865096151140109640d20400e0040b61700c6170b40e61410000c02a0300c55418003025001c528147c9454801c5480c020300f041d01102e030125 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 289592095 1250 289590845 289590877
    0x5040b0c030421050c1c121209060203060310020a020a03030209060d05070f030e0106050f1302370309030f050c0a0507060302120f090303010e0a0f02040605040801051b0306101b08 79
    0x400c0c1c3c038103a08003890348164406484424400ca58861522240310101d07c000d00620360740122002d440d81c4940078046006000148c0d407890140200342c140104004803002c5944107000030704840ba80020440c031203035030608005030b0365040d00340029214000c4032001000c2d00d0400303041003a40d0764048900703040ea0030a9281402aa9000a412800d07980c0a0060580102e801413420145180208003d401030a00900040c9002d5003107200e0004001c3c10f41803c194401c0c454162007c1554048020001c1c5c150341c5010060081c4980c0c0040880d07403200100401c00001003420389001109104146500d41d102d022159460340c1c0d004050007a412800a6542c849801c40c00529802d5503000324501c01c00d034030406140707941c0c01c0040c114079100001d0210304140d66111001244641c0310300c0100040c00e1140c480315115890040d00500350303480108844114001d11040c108a8a100300aaa80241045a80121008117500e04035000c80c0d8401032200e00b00d0607a4070b203000b80f002c0c0c4401009040407402c285 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 289593345 1250 289592095 289592113
    0x903071b051e090c160605130506010e1b030c09090910060e06060406030c09090c050301180c0c03031d060c0301030606081f0b010c14070801050907030305040b0c03042105 75
    0x1080c02000c0780030480e40c208607844001014132580f03100400501c00e03c00c541918400098a031182100c50480e405c1600d141400c9850050040c02c0002d00d006110f50400d103640c40c1340888903075240500c01d0107000b90518020010441024550003942c0311700d0b40c050700343d1310341e483e06015840d640c11001e014004603074548040030801c82903020000b803055030050b010380d280a19000e4100d00500340e0004040c1005075807071000c0b90f90075441c0070720941d03c10300e48c1e03d154695051000359098614801c1100042d94a001e0581c000d154104070380249991b014140001c0068070604d5852094180640b102568002c40c410072400c40e4070b120185041e0b0380241010000962034109281e510320400f08008602c90780d442d02c201e110038144d00861008881071515054040e138560303407003249416440c101800742e0003243d400e21505a00744155580914580014034083e465520041c0c1a441240190280341c000000c03e20f00d0464204202c8004101c00141480490420441041c90104010084400307020700094 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 289594595 1250 289593345 289593379
    0xa05010603150521030307030507020105070e0102061512010c0804060b010e090c070512030403110c01090b070f1a0c070b0703020a20070b0c03210408070b0903071b05 73
    0x140b50780c01c001d01c2c2c2c4000d60701d81800100100d955416109801078494046401e6050000384040d5020304038030f0714081003074104843c010b800d51307030003c003100100100d864580896131f90018410742c11560641c004044041c0c11070101e1511042c10010307450541c204007004501c10340c02a000d91003140100710400c407020301c0d10011a80078100405503603004102d400440d0086d001d9100038100d00c4d2050040741c2440074804458a01341c0c004941c15400b00340c19001000d03030f8003814800e22086a41c01d1270710038201400d05409160f0350041e8480500a0718201c0c40803020840600007481600c413001c80c1c0002c040c54142c07400359030b980c00381030225000700c0280f01003400c441c000e0003603407801695929044149000d014560b07101882d4092004490b1041c00e4001442c403040c44024400c1d810220050743d80c80e082c5030b4280d000e40311403486a00440b4580020480410300202c15622001d5210324000c07065180ca4800c3c030300d18010442c3c09030034004181d81c030b5103501c40c2e1a074084040b0307102514060180ea400c040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 289595845 1250 289594595 289594601
    0x201090b04030c050114040306060f180606050a1d0409050601031a010b030613140c09041805030d020c16080303040c05010f020a110105040e130506010b030403090e0408040503030c01050a05010603 86
    0x210040ca20714a212042c42650300036494108024503d0007021308295580e1507140540700c071684080e03c84030600f43c6c1072007000433142c000310460807400c01c1440030610344940100b9078403d5510083c10000044840c0c1080207503902c14070640760380280280b01c095001c0c00c095488950a00c011180746031040c003040000e003900300c4158100c0780c0740d05042d42560b442d1000d002003801d41c0305a481860796140d071080502824464030a0140c0503005200ea1a01d5420090208540604c0f10721071f00e95003081b01000001e200042150131a403142c080241c3c4460b1080c040d01c1c40d01d81c2e041c0d09800c01a201040100d04180e002020b50b104500402da125299940e6000540d441d00a0307103c1040143c21041840001c5002d0140c500160903042c507040b4501551001380c8140c0e15001c1c1d442440300303000c1c900704000380b110800a441c05407002811a920714145941c2c040d200e500107200d100310000d20a0001000d014002058400a010143c00d0301e568201204640b8000e00c0d0840720991598174000010a106200744 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 289597095 1250 289595845 289595849
    0x20f0403080d2a020d081819110d0f1506081f1406030303070c03050405060a170c0307170613110306011d0105040e0a0605030f0a060501141c020316120201090b04 71
    0x14020342038182d4030141c2110307011002440007091001060b05e14403902810080b41940d054203014061508c025450030294241948140604c00c0011201c040c1c003146401c01c0b405120795101c80c0034042d00003001c5811024000e2030340410308031f0048000c0e11480d1407994038240740d006c0d003581d0300b040142038202c0c440803c2e0317106490450f0107600034070000310311034000d0b00d4000c9264002c4c1041420299a00b0008109501417451a00015190000e641102180000480d0040c00c842e41c030302c1c2580380522008105417001040a0f101c58a28408104944c40c0d8501149003420845000d0045445501054019a106680c80c0c0c0c0025507821042e612050300b088100b1a5080503590585090324040a11030000d0000d030062a415660300b40018056508005862403803407084090074006005040517000c4400591061891464a041c03440b600c0c0e0380c000c10344681c0b00040d1900540c88000f4000300c0d15001e003948455080c182c1c80b140100c3c00010302040c988005200f40e88103c2d1080d1a5000c60f29103000d24 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 289598345 1250 289597095 289597097
    0x305040302010c06090b2a041406450109060806061308060a090c0f05010906080406021201030b010906080a05030313030c0501150504060522020f0403080d2a 69
    0x6000a100561107503502000c12070081201281c0072a40b52035010720100140c03078020000c50308814800c5019008545c101000444503005420a40340224034640006080c0000d8070582c00090080980c0d8900421020800492914a0500c401e4000070702052150b40741048928600400320040c6588030300d141c80f0941c0c000303503200403507034481a06010440e004000c08540441d01c08902180031101003107490b00c500024500460680740d18205905207181540100d80c440707020180501c00c6d40d0b00801c400c01100c4481c50110042ea4990514000a0103150281c460550003100008244504c81c19924144c0b0382c0030004028180d91400003070703928030075070304010004e4209100051000e0300082c07011030a10f010b800c00d42d20000c1c0b690380c2c0c13a00315a4a4480700c2d14101c0e81981c1440b01d800c181c400c140c054a000d444c5017110800c0e00b03c6c12400c04100001c04c1030426000614081204091815039000b580c2c8088060703114035000e802100507055a03511100802804034141c49850000402c070030f0030740c44c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 289599595 1250 289598345 289598347
    0x503060709090b130515190b09010807030b0d03020a0519110405101a03040302010b1002060a050a02090402040810180803070516120c12090605040b09040e0a0b0f0c070305 75
    0xd0002c80c000a0700e000802581e0040b400001480d80403114012140b1541c5012518030a080d100d104010710040c22403482002003007419821f100d031010160845559660074289003101e695110b001b10040c2c100407200b150010250b003500c404050300011408505407180b0241c0354001c090911940001104200142042110307400380011030800f90b004540200b05202403d403e81d8650307502110040740e02075911a01c007000000c00c010716078203108030744179294200d074860044141d40b00300079603800c2c018010f403c045a41e0341c00311304d008003a41d04580c110600075000390744943c1c0c0c40b12029214908034481203106402d140c800318035544611003124145078005103180c20b6844883c0210b4042d04a46d02c160440079404050304c0104081000107110140b80382ea03a40804a4240340c00103003445000642000d000340e03403034180b00d1242c01401b0380c0d040d5001070603541d4498848500040150040d10144250f500400c12094240b1604088a900c508400400c1c124a515961308002c12480382c90009000104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 289600845 1250 289599595 289599599
    0x506041a1513060b0325030513030305070e030d0314090304030812040303241401020c09420306011d010302010f0309020405070305061009080a080715020301120c0503060709 76
    0x2414040a015041c2d440e20000b810380d07200d0f200750219510030f43e15110300820b0103203511109540b04000c810307495454035060144d0308041850721880080c043c0000c06054484001646242c420012070f1010030008007100c1e2080684540070380103014270401041d940c681d2a0014200400c00070440e0200d80e400511149449903828001c501ca180c00b03801141091340b9940b00050402030b140401098005503848045098030709620001b480b0700e00d046841c159001640151025921014401c0e440240c6801040c100780341203502c901424604031029a21260010040440240c58410800c0074941034040710b0003641c0712552090101400140c40c00002041070044c0010751240ca50f0203a503454078140800c04003055400141602c808481d00e40009584a0810600b89410000c038040f003452414031110032800c0a80a0752207040400300030300890800034405d01000300744c6081d0a01c10450072030071512541c4904103200c03708071040701690f007164040c1d400b0545240207d2240c1c0500c030191201c0303030014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 289602095 1250 289600845 289600849
    0x70e0606031303090906090b10030506010e1e090906060103050133030f1d0c0d1709010509120f0c04060617040501020c0102040e01030605090109020603150604030c030506041a15 78
    0x41c0070300c0c2c0b0803000c101c1c40d070700f000882812a000702c80185c07600c0500410300111800c10b209004100002100805051405200707090341c00400114036540c094440c0b07802141c3c0aa1010350420407000141e03003201540d01080b1100401155450240009980500a5980e1508048422621000c0e00420103510000b40a15545c6141c2c0f86d00d030b800110705000c554820014014402c48200c4001031160390000c04000b0b5036000c0c20721524105d00d0003200c0010031025647c1b588200381c140050303200d0704403100181e4440b20340e00030400c1c1d5014110003030140e4803600102215940303072030900858140c140b28031590442907281900810b401d135201687c0f201c44200700d40902e0010284003410540703640d5400c101d0640034040c280018400740086540030901c030351452600c80c0c00c4a03002401c3c0b0009925181d618801656a07a0440b5040815a45200d04004080d0000f6205204603840144101c1560740000200f08010941034032a42c00350059180c40002041e0003c01d0720800c440c20500d000d00c10a0301540c84c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 289603345 1250 289602095 289602121
    0x509010c050f130e0405030c070b2b02090402041203030b0d1208072d12060b030c0f040f0f05100809120c010204031401050105130b01050a050c011506030e070e060603 73
    0x454030f0410503140c050b50301c04800c1c09490f002d907002d651541000540041504040040d01e000302012043e5900d08a0171800301c1900c0b112035181001c508801c3c2e01400300420094064400b00040240115541c55481d0380d1542640109082100400d003800901d560a00e04409140e100e5074000114240361505808100c406610090400741481182c0c044526010341e0b82ca240004104c04c9410740100920484015080c8001e0b111001e01030350078440103000d000c01da0001d694010340201ea000da02d50044901041d0140540c0e0071076010b2080000000400c0030017000c00e0350480d0340c190f0740441481c450a0040b105050304440d01403035580300e40c401d42001122400242962400c6a0006040c96202c2c0e0301c1c0c00c50306000d0030400546039103d40c010300440c034164018042d184480c02040050100c41400139105002d01c114800034494041034000004200b9040b000c00c00a829152051260b2100d0002d030081c4540d048904491180210101c0c8207100e0240d0300b401a0310041841d401c50791505000411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 289604595 1250 289603345 289603357
    0x20906060a110f0106170a0c060513031e0b1503060f13060e0109020108071806080a09050d0c0b0a0e0709090f0b0405070510050306090403140f13090509010c050f 71
    0x10000505454100c090b0b007808031003e068111400815007a241440c240020f403c1ca501120440d004904a680015450705071306d030481e42c45080c0b036a02c1d1000d050040c0020200da40c005005922404a84925071030071107071a81881d440f41280080701c1d180d540007175030781c6c0100c13040c5241c241d44010b0100794030484050300c40798044441c00c0d900c00328040507a121419136650048113151613442c2c0c020207045603003013010260b120109143c00881612010582c076a0300c18030348640f0081c00480800729903030300c1864200855860700318017201c80e10340310000f0050501c244620b0690f01400e4150128003814014001c00c00c201c030403c0001d0007a1410700b60014001c0244401c1112881c0f0b181190030b00146030395084510460040c0003920800d85860f0034800300d510110801001c1003410010003e680d178848101d550003035014074080d1150000c80e44480c42520420041298001c40895030000700075a008560064a15550060080d5118000d509082c3c0b48004810b102003041440144030800f000006032403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 289605845 1250 289604595 289604597
    0xe19060b07030e210a120c150c0212030108100b150d2705060a0e07031a060a1a09012601230a0b0a02190305030c07050106050603100302130504020906060a 68
    0x24020803400c40138104000b8036840f6600d50030034039004c0140071058030941c00c01e80f09070501c2da213a4840c41e614050b0340a41c55000d0001d090340d98440c1e41156200300110840282c0640d1515a2035840e01c1540d50f4a1401c00041502241000e441429500b01505500d0a80c00c04511040c24094001451000741078480b8101032042410210314400124422100007140d009001514560524001b50825504508030400c0b107944801c070100001030440c5003401d001c2d400514400c65648032480010406225580b1403c4807070540d8201003403199018004100102090b00ca07007020849001c0e03918004c1e80d01c140d054800010800c0104002e0048079200003101480c0010f9030400110070300010700b0345400d5088070850304008a5031820b0a43c042201281d80b00ba204034000241e4005c2d507005003a0b1100030141040000301003545002c026094000002500e0700511803616440d0000743e4400f90240c41c8010380c824504401100409046031098a02a5402412407c80c903a03c0b43c00b80001c0742d02119002c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 289607095 1250 289605845 289605859
    0x603010611010b0a0f0e1308070204020706141501020f1507050714010603060207062702010f02010f1a0411040b0403080a0c061401140a12060905070f0e19060b07030e 73
    0x50360360100501d0141610005c0d00d4621806c04072010382d40440181601d01e421100d8404002080c0100107540e01c00341d04480243c0d4556691a01030050500056032404980016041c00390703103081c41e0078000707135164283d084820a02d04228000c2c4d903068006041d90a1068400120b0350780d1307100700c0c014500e1034000c03488040081d40c010003550854149a000b0303600e059001c40c0d1002084124028560f90030704810380418168544007000c00511401c103002410300405224007525203000390008000a94900c80400840246c64035000f20340480d00c60203442a454083d02c07403000454070040c1c2c3c0c10b0354a000011801c0c1800c5543e0402c81d07604c104103100500c81c0440c1d040000070000e00501403001194040507540d9490110001c824511071800c035441007180844c14031007101034030024910311ba00300201080c0d4800700d00f0481c2c104416904985140401c440c4081441c03400248524000c003404058082080c0c2c89c2d500020841e1103e00401000840400003400480d2249141d4103148000038015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 289608345 1250 289607095 289607111
    0x15060d080c07140a050f09072a060506040509011803050904021201240306080c19170d0207140d02091e0109090c05040525020a050a03030e0606010c02060301061101 72
    0xe40d1800b4100d40c4000c0c076150102d812001a070a20455000080000340d43d082d00345800b007030001c0c5070010300900c1e8404001d201c1040d801c42d03190000e44030080b00e10074400c40742c0302c444c203050200140c802210403c0c000c90520000c51210f206c1441400020b00c1050541180445903640c12200380d40260004d0ba0703ca0303001c1c44072200381007804403010f00908141000c0061880e5024810b1080707040c21030004e06061030b2010070130041030003003011642094100c401180d00f8420481010815049070400c2d480302102422001690000051f18030620609400301c0d00e9a580d24810301c00740c89086072190f5000881e603150030005040c0100510340101240241030100035181c0e00e0044051000d0780540350340c907150181c0d101070120007441c89000c3c2c117007694144143d2030301c40c43c4030250b03040f0448a504850041000700c1e0b10540f00f8091715844690010580da45283c05043c010044c081e04649040680114008125198001c60210706a42c0c2d002d080c5508582c03902e1002e42d00c0d0700240040f001607540319020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 289609595 1250 289608345 289608367
    0x1503111c08030115080603010e030d0c03020d0606030606080a15090c030902191a0c0a1211060a0b120c0102060c090102070e091b01050a0c020402030c09121c0215060d08 74
    0x42d502815801c0514046111080f50040481d80043d01680c001c0e45007202401d440305004c02143c20f00080c081c0c002c02d403030004080c210700a00c21401d01c4000315251030030224049a258021004860150351400b07503507160640883e04580d550365040c201619400e5040000c00443d4001c1c92360300020f810002204042c54020072801500c40380003441c1204069401d0084091046175450b0403078681840c142011840c070200d0380c1d9051020b0010308816442c000b0b00b69803511a405440c1da40111005442c1c0030b0602501c90800b4040c5521854481d0000040020608100007240d030000d0105a004201035211101c4500969001c03820280c114003403c0d50120315007a01842d5140a14810340042150120408400c00e040101058942c1040000c1002040080e0704c500320780c0855404031801641ca4903603080d65030300340c480c04c8002600a2101131030b803007039141c0105080c6500b03c0080c1500040361a640741c120b85801443c00d800072032109050205000382030030380f00100074601c503009851900500d155 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 289610845 1250 289609595 289609597
    0x1a04090b0a06050322081303120f0219080c0706080a0c0309112e1e0c120f0e0916030b1507060b0d05010e101113140a1703070302011503111c08 63
    0x3c58121f400394400104100040c15031030695001039450500000e00329140001d44940030590800c040001000300681807140354811503644444800480e508642e4030b142c040c00c0c1104c1140c88840da5407502d007070081c0301ca000e0f00504820a03409095580b00e604154104403040841e03009502c1142000600405815041c02d480d102c0035016407104030304100c8491481030030b84034000347e180407c40c43c4402140001e540d034516a42054907400d1040703610100c0c03038040785c0f88448010101d60000c503000c2400a0501c80802d002c600261650341405160500014050072240006030340740c01c0e46040007007101046299000d00300cc1c2c1c2c4000c100c42c03039145598031103d081d50700340c0040700082c4e0841c09006226982c6403064400030003200b0040d6080022074003041030784a04a1044c0300891808a0b0f6085440daa41440700015040c030b007c204500002c01c104080e500d4120303031000c030007640c42d140558810348444100001241d0b846405020084420010721035410101100300002030696500f6000081c1c00340 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 289612095 1250 289610845 289610857
    0x10f17040c052d040c050a050d021e0c1e10020c2a09010815041101030902090109290a1208040b030f10091e11041a04090b0a0605032208 60
    0xf116400d0481d20389442d12058003200b0030300d1007589424103166209402c0b2040d581819120f050003511820311001c518040d200f92030030b01404c2202042c3c2c404282d641c800c00341c501f4900041c211520301403080e000d680c1d6404078610700e550136404480050440e01054005000340c12030341c2c2c25a100f0401080f503100c031b060428556150f00ca407211035141e941d400c00e401010300522200005002000c1000000800600060b00291280131803000d5128564065001116004e40c0070345071800560b5a403494000a111003d00c9a11103000c00b4a03c080076046081d02c08040f000003000310003458a41807620b01184558070045880c18424040002d1803d00c5c400614031401040414201c01d1404560100040540c1d41103082094605500604903005024400e01580c45131a0300281001702c8501e650158021a4043c0c4008101c82c0e010381078038414000540700711070109800740b00b848034050030012051100e00510700003d80600020302589414201c07404e1b228102810000519019210120383d03038814 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 289613345 1250 289612095 289612129
    0x80f01050a0c0c03080109050c09060316090801151715150123031603020d020708090f010e0d030503190c05190e060702060705010b041407020705010f17040c05 70
    0x204100a6688030501600807a014145801c140348200c3ea41d02400b1410107024180c0c100307a407900052a0f40b071980b4100d03441c1e0b510080c110764a0f4900700454034440803040c01c0520000d0401d40000a44c1041409600041d401710340d49892010304180103008905e41d18500c010b2540b0564001d50300034500030049c2400364040290708540c440d03ca0b8000b41401034900d25010102040c080303400c42400c8903009a03600001110b900100c4000d9581d411006030050984540910b4170000300340c410041d240300200f40b045819030f0070b1840d1800c010015030317100c00380011050304016807440400000e0321410045622803401c80c00c2180d209000304641007290003114052020680000e83e244401d50014102c1c02c00700c0d42440d08003c81c128040100b100d5002c5c2040090040101154034420030400390024840b415014100704503c02c19446c44104174203050311441b01501038007002160320b51045500c030f201c116154860141110500209a0440b80010300c2a031b0036213003040010456030f5500c0c000c00052400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 289614595 1250 289613345 289613351
    0x6050d050f0706052a250509060d02010c15090503070606140d0507140307051905010f0f08010509040f0510020d0b040204030f08091c0c0e071b0813080f01 68
    0x40310181c034039241030b64201e4000d10105000718824907045480e040b2100820700c042c070440d20b0a84540d2460411040e003000c004200c15151802040c140c5008441211021034940c1e121303807200001e000c00707203040700d90290014949519420200700243c15002880b000358000090452444d03c0e20b40c01c41d0026001100d0681d2511420040314410018241d0028030842c3c42c00c600c0001c55580b240d80f0881d81c0f0504e10036007852030011200c0e643c188429402054040c100002e8008038900c2034141185c580503490102d061018000c650600ca030545619141a58031880d00b181d0a040801940d05001081151041c00d03003610b03800010000d00601c180081e803008c02603185c0400500c450f007513916100110b4041c501c10302c030070000310303c0080000742102d0f0021001581d030403150b40403e00542c04444443c0c41005552086010000002d03070141c22205002ca1000c0c42d84c03552001104c0c000c8140c01004040d4029030741809c0801c1091000742070040c1a841c0c0d20700010b541e14035031418804869940c2200d659 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 289615845 1250 289614595 289614613
    0x120403050109020109090b012c03060a060302010201060f060509040513200a0b0a08190e0a1101080609060d060e0309030106090e191a0717090d03290904050106050d05 73
    0x6003045c0c5000140c000d0301410300404280d4000200013091f007200728003c80a04d0799181110420807801c1c1c40102c2000b90a07100d236480d201c0c0700900601603a01c000c9005601c0c0000010354100000000d10070356207030750760f41843d251400782040050280508440246802c02ca9082c001030801031280300c040c0c2c03a00c01c0950008103160204600440c041e0700c003d410384010480d80456030f5101801c254801c5003205020071541c170034a0610020003d10355600d03020303c640951103041c407074072900034080758000341d952804568a030014005492015604990003603400c6444100249158000c1c44000f04400200c900700202800000c0c25280310340e1104038065903420703c0324014481400054401041a41484030043d941d40d102c056207003115086910042565012524040c1715003104440c100002082941d681815400c0f592a11001000703034001c6854600300707945d900d01c4011a0b82114130080301807020801c2100c01e000b840d80d030081c0116103075540d66071701040980c1c48240b00d041580c021002410441 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 289617095 1250 289615845 289615847
    0x721080c0111070b0610050a17040521041403010908180f06030a0603060501050409020603011e0b0711030609120409020a030209030105090c1003090c060c0201121109100507020d020f031204030501090201 89
    0x1b00b501c0f04060030804200280030549811082c81c400c2081d84840484031660b403070a2079820402c100810904142c0c40d04c500010b0f00203079402820a03114481680440346000100309405c03140d46140c0103010500511620880c0b00401000d403200c20030103800c1c440c42903d070320006585a8401c07034125500c1c0d683d86c5418402c7c00703010303c075540c09040246c40c00c02c0a082c15400094140c0014400c12416101c07044548400c0260011948000d001c0c031805162a9001480c100f500c60400703000340b9000748100c100062901e1400680031031007500840d0701c980b50904000e8480c01030351009081400341502000020155282449080c0c0715407401c034090a4105104020000e00e1041e400340b02c030401d801c01003c0d10104800001c0300e801c950b5a800c1c0100c65850510050710040b00070008c622540c1c1c5040c8d00907004c45686001040c00d010111980710a0307500e1440180c07014041c0c0280a90080b03807030302404c80181000300700a007c090b001812148003c0c504030780d40340c455000307800481d0720340d4451503800115 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 289618345 1250 289617095 289617109
    0x1e060f042c0706020f0601030c050d05102f0307080703050a0905190606270c030b0603040309060806040c02030f07050f1b0108010b04120b04060b0a0807080721080c0111070b06 77
    0x5c169000082c120035459500c0380344201c441030182c01c0c03192a0288090040000030400b4400d480c18542c400d0100c0540c10044501503518411a40242070340c0c03001c0d4a220903090341c1141d00c69011900c9003913031070701d961104400074100203041c1d03a07000fa80c40c0c8445c1d02045042042c2040e00e09210f80e41810600c1301d10345141a50f074035511410441560b10454144070b05d2000c004950424a54030000c1c1c1c01d03165107000c8004c0c10251103000d401c12400800c1c0005d0543c44840c02040d103906440c4c0150544030344040c07100f1600c15441c0d64005810038083c0c400c01955000080c440503005100310361290100034017031410003544918000c803415102d0070f001869608a100d0900401c80d00000340e003010315159040706500d40c0c0c0500140840c2c00100000c0070001c2c0c50340100440e0502600441e0743c940c40c0c0c0c0c1c03c140d0394002c900400c000b52082050005414501084001604c16455004101c1da0030683c0d40302400d4008540d001d410f55243c00c558081d1071600f402030415240504218815030921a0901104d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 289619595 1250 289618345 289618363
    0xe0115092009010f0e221d060705070f11030d0914030312070c0c09020313050105090118020603040305040b030c1903050103110607080c07060203031e060f042c070602 73
    0xa00d000078041401c2e6a07030000c150b00d0120010b800c1450300c4e552030000042660b1808038044002e2032007070f02d040d400ea0240303620210f0700c503403001e0018121068070060107545130b03003c0b0f034003a000510401079180043c44080d1418034043c450b0084500590016001071f080c800450340401c000340c5810001c204280c078581d0303c8860341c10190040e505c0c00000103090305801c0c2d4028916000c1c8030540e084901080446540c00b0000d1010080464807401c00f0240f80901c01420041501c0381d600309008511010700c1849a80d680c00e08802c0e84e441d1075a240d034280700031a00010b100f9801d12400340b20021354a107020008512a0360f42c0030003207940302107131800400005254540001058509001400000c0805081404035042280e906407a800c241c68500d420784604010039060f802046000501d00f034001020318041d83c009043c10040c1c50424440d8405140101c9045901c03a8856440c50302da418640c0c4150040440300134050000c03244484d90004281d840c004c80f046641c0140d1042000550500c10148 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 289620845 1250 289619595 289619651
    0xf030c0a03080f06150c1c0f09061706010e19030506070816020d030e01090204090b040326070f0c06140627061c0b010e0f07030207150e011509 63
    0x3c1181815008121015658242040d01c94000607004a02c1d03c4204903610100514100d00c000305c1c4407c9000511440500c0384d0800845c1c0908004070360b86e800307510007480c1e40e09140340300b480a541d84001100c5460003040da0a4014064000d4800661490b103423000185024000400b05410305540040090305c0080000b080c840410b104020410381c00324440c180044145804205000e41d00030081c0101542030000307500501c0c0010b0141000300d0b040c0305034400d43c066115034141004280726041000a0b00d0f00c404500309451000030f22030303409200c6180f24600d40385070060741a40325030794090403241c0c1c828280004903e14410407103c1c0c0fa110707001d90352486080760410708040f81d032246c0f00f46001014241601c1142c00c2c404206015614450002c0880d4200c0c809600f42c1d40c6d00c01c26a0403240741500d00045000d25040003030043c500134002c445550b54420300d520049001200707080c00900740000c1c0003886540f01c8405070002036201d8030f2000600000341c00051003000054054030302440d2844001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 289622095 1250 289620845 289620871
    0x13060c021c050309060c1c0512040605070e0d0311060c0405010c140102070507060903030f0206071205041b0603020a1106061503040606050d0f050606010c0b010b0901020f030c0a0308 80
    0x40010380356420348004040328141510012402498058254000c030840d245e003107440030600740e88840001540313030046004035030845186520504c0c00c84062152101c0750081240c0710b0f010074001107250b4445c56010109140225800d034050700001c0551100d203c0640004000418103208030340d080c022107812022549009207810300d40400039020a0401a0181820042d20805442104290112101158080b080d140096110700d40174062004d14081600060000040b140d00c0c103000250b040d0065542c0d4481c1003042c0e9035540c0940186c14020000c54050180056901c008a03800d03085101500c182d49015031180c3e02040004c00c03d034103101c1070190325440302080c0045500d803451101c0c00b0742601a52a55603a4460070481c010340095485650007604c5110340364140214071000702e220078424070590b0f66907201c2d5001100d0b40d83c0c0e8427402909951889004110344d061000003030000c804103005440c0b00b1202240c03460700719000031039441c200341c12081e020310400d03501102450307011041080e60 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 289623345 1250 289622095 289622117
    0x301060339060f0c0813060908030301031709220203060f031908031f06020a03030c0201021305120a0206070c031407031101050a140d140a09030e0f0d171306 69
    0x4025940802d21484081c41154030391150502d02c42c0e21102080b5401030324203a980c42c0c260f5000085040944509000180b05080100d41501c1c040201c0b4101ca0b0812010a1300030708011040030690b01c01c8020a034807d5000448405480100700c01500c4102c031030600584034640441030224050fa40e040c00e034400e80249800c140f0b920061003e55039490703000102240c40369036103018450425000194a200001c102c074002508540c00070b010440c05110350341c140007041e250842a0700f0307405a84804081d03041034007428842400c00310540b0071990b85403422540a9071154020403444e60008070142c0d00e00c0204103080c01801813041300004a4001c1303200511a2600c0d44d100c0d121941c1150400a0411100088203e4210f100301c081980c4d800c05517180980d00c030482c00c40700340100002e16070100d44501040006500e0700c7d4610480e40900e8040d1074894032800c1c004100b1001c2c0f0f0680f030f03502e50b004000700440804034103a01403640e1076102050140c0e56808000307200c0440d0908690004080103000890 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 289624595 1250 289623345 289623443
    0xd050d091403071203030b03060906040515010e13020406091404050106050d0c0e0408041a07060f0606050d0221012306070804051306080f03071a0709180b03010603 72
    0x30800c0f41c041d100304c50003e401c14542140500740000031198503214840900003040c2c001f18200d40150702c241d04460000b525035482940ca41424030031b0340790a841c2130b000207119500840c40c109910348001c01c0040c0c041d848580d030b401200d40589115102c6910442000208542446a40042e000c202c80f1001c84046540d10310031024214000c21001880d40b001241c1000a06426940548003600d010351070300040c400450720a03001000d007645c0c3c00341400380700f514401841c0b1a102c103564460b55400e241642c1c411501010703520803019415800d0700104003660030b16280406a01800080e0164107125100c04404001078131b4003002070348607440c1044800002041c00088030100c80d02510035404445082d81d9000060102d5808100940501da02c294100500132001344a054401d681d01103d05070744242c406024941210040007281075002d050022902c040615028035a1710200030448480e403001107070035501286c2c412941d0b0b016042c2e0840341c8080702e803420011a0300104000c0721420070406 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 289625845 1250 289624595 289624603
    0xc160e10060f0c15050403230306011407060c020d0f030605060313030e1e100801150c0f0804030b04140118110102070e011412030a0f030b0f0d050d091403 68
    0x82a8014407511651449106010380c401c49800758100c04100416403c4c0016103001d00003c41d0100d000440d0500107402503100c4882c0c021407a100e124400e0705594401006440303004004160100c03041040c0000e00004a044c000c441c00c590955016020072944007001600500d034001c0701030181810410140020b13140c180681794006c05600307400b50480c10034141521220040b0f440c3c2d90300b180520070301c450103004c0b122529443c04000c0e07412180e0619000742c102c80c01903082c0251280c40104c8035012000c2e51080200341400b81c0100a400b001c001555950f101c994010341c01100d004c0706840401c4140101c20108064010307a4400078485004500a01c1541c1d1950f0603004109080d40d07a04090164420400040907004000c0c02c480c0b03558551840740c0348040100f08041c4201031035445034400d4000801a0384e180d05107a00ca03031024440b104030a41c040c10402d6031140d0410807002c5940025070383c915100100354020700107080985104580200603440c2c64100403c0c1806030304404209450000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 289627095 1250 289625845 289625849
    0x90f060402010f140307020c0a061d0f0303130801050906014e06140108030901050712050d1b0e030303060310050c0f19020127080702010e04020c160e10 67
    0x101c1c00c0030303c44001c85001d07a45090445581c0364100d03808030402c243c8a030001202e03443c4039021110000980d0307460408803581b0f040c2d403503030240391410f0004c1c0744080c1c14042d100c542d44160080c00d0b60f04154aa05081c41005400e9000c0307001613450324140024800c060062a014000030000800c1c10191244c150602d448140844144074064048d03006100d0320031542c0b01901a02c02205800d145e40c21f0804202810060001c4111060650000107401800008442c804501a1030b81410690b4580311400c142c2680c035030361030901404000513450400188550072185d0f0070710030610140002840d00170040d4411901c0300d4003c0c1d1040060000c47d030740c00107000703001081ea1100807076030340e03156990441c00e030003040804c400e80d10b030229000801c041d5038850384415162a50080000c040002e14803010088424042020468500444408281a0402888064010b041c0310410f1120503000c036040780d00107024602d8036040801c890460345900d60302d082c002c0c4030030040017000d810100161070000c82c0398 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 289628345 1250 289627095 289627097
    0x150b090105070201090e01140102120c0c120102090d0b090c030a02090a09020d020a0605190201090309030609081216020c22050915010305060703050901090515130821090f06040201 79
    0x302e010b030704680c89000d041002c0c0c8030328180d2803032a59507000c50300720882c0c610003501d0244c0103a08240c081c501d602010303200c107186200028120040c142042c00f07003400d0424500043d954080000ca500c070380f01d600710f014a16209010010592038802c01040c00c0c5205112414071a8010f4451940036076079140c11107400c01c464540000b0142c0c050705c0000c20707411948038000d41005000100040c1c5940001c0170f050304458140564469030a5a04c2c200d0803262025001404140300078000e01c0841c000703500194540744203980803443d004800e0b50f01c042401085481c980e9000d02c201750010026418004068003480642d140c6a07910351402c051030180400d01318840b0a640c1d00c01c00039012020403c030f00314801a04840050055840703051044c2c80d150101d038454086402c2c0008509400014403550107003239080409000d410001b203111400300d04016110b400c0301d803442410400402c81e0b500051198280901c0b201e2411101072410860140d4010103d00c2180c11001c4d20002c2c40c840400c4e219402982 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 289629595 1250 289628345 289628347
    0x903140709060902090d06150e09031317060c0711030f07060f020a0b06040b030a02090a0504032d0806030f030d0e070506040e0115021e0c010207090510050402070606030501020703080703150b090105 87
    0x1508070700c9003d881d0b80c0d0040c04279015a4060042e5040c010000301203005205122044880d115804002804002e400d00002c40c2d010304009005006030401030034916104a051f41000d40034540068a0310400b01a03004a80e0004582000701640011301444541034500240c04981c54607151100318460081c00070b8029615060322402c0d6035402e11050402d15401000301400d0b040c8030760040c0080c4170840c3c0407804180581400d0940801c0e2031004540c1104000c03811810190314641101e4070840a04450741611801c103003400a108103201070408001a90030004200c01321030002071403d0090350105000f42010041030085800204245041d903a102001208141b80e0304012894903000680700d107580b031440300e64540c2c80b030008a4149000c00c0300340d084a20680e2543d410804844068920202c02d42c2e80a0040100c2d09140c2c01034928640a0140011241c0d0769803119401d980c461142100059800301c208001d65400d882821010380c40c0f03440900400b410001d8a20951007040c2c006414088 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 289630845 1250 289629595 289629611
    0x905060a030f0f020a0c050c04050c1b0106051c17160206031b0304060608150c180f090702030c06070212040e1909141218100903140709060902090d06 66
    0x36140c01280d030f04070b40c4400c02c41d5504a0782d040180200013415084445000c0e500740b04416152500505000da81c01121141c0741001003180b400c510002619000519502c4400008041d44c07810300150850071280703007110707070030318946444004622040e08043c07844000f405100200c7c51080c0c0e000c04034580c103480c0305a4035201c900040300e4100e080f44042c861918000b040004100c0d02d50411303000c403223030401204c02050300080304101188044516003030001e400e00809664113145034401d20b0b640d00c06003010045c04080b101181030284111105400f507400000c0d141a9480200016503000c4494409480121003501e880d500d148100d1160f0300982d190349010a0150485000d0720043c4040301e103040040324290718001c451350890419110305406120307007200002446500300c412a190900c00c444001241d4401c014000503003140c64010008140d5001c00000c09125901c400141000b00600e40301c1d2034400500151541074015012a42c0103001940507070b207903c1e11300b03240c0310fa101f140460700c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 289632095 1250 289630845 289630871
    0x30604020f0c07030f031725050405030f0c0f120d05030a0216050708070b16020d080c070e010e0a09030e010327080301030209150a0e0a0b100809010c0905060a03 71
    0x2c0103000015003180a0346000104100c5144014901c40344280c6514483c14182c10401c158220100d406001c0c100c4c2c80151104800584a01c880a82400f41045420aa2581c010a1414060a130000c80b668490100c50a00d49481c91019911200171244483d2a10862030f40a48510b00d1800d1034086c0310001c008608001c00c46d405030303041c25030350440802c401c0401d0306085aa45a8902c0343d10341e64000da030008034a984405044484070052644940c440341c80303075070034444818032002e801d0f00e00c00c405001031041036106000c454010000e0507850b2070154104180c0c0c0c60981000340040e2480c510b80304518002035001803103000d0705403007400c00042003480344c4103804c00d041c8003403030b0380700010f15003600081040203c05c00365050340d00a440004040c0d4800707070740c8000c3c09416200180c1c0301d01c0f00b810030050f2021984019601c440c941d140071801030101e1000c07940d050481c2480d0720100f4800420031602c500248102c216501191803d1362070146410701190840c0304241e2100f08258403110000003017 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 289633345 1250 289632095 289632097
    0x50f07032a03021215060307140105030912040b030711060f0103061e0e030408070b0703051e0409050c07062a0513030b0c04030c1403100e010b0a140f010c08030604020f 74
    0x443e00071300700380152810000101e0311807102c81260420300301c450003c43c1c1507040000e00141a1011400b141c480f501000f00191082e03007000300ba80e103042c800d121800071b4181e24540600018050000362603103d017401c0e000a4002e03580300c00b810b0500c1d0b001108014006011100081c1120341024001540d084c2001e02e81d18134840c8500c01e99240d0b410801c0d1294004000801841140e1014003074401c03494841a491645100c0e0b5032002d0009a0288550099024155902d00070b0300082d9a90518080d5681e00c0305c02911402c80300c489000b500480c0d40030074000c8501685980d00c40035241c820141d508642c8030b0032101484210941040400300d4174003200240544600080c6410071091055440c0c1080341100f40d510601046a115032176540008410408290488a1034001806407404101c8103241a000703040c00e00c950ba841d9902e4040b0300c0341e1511402c07449000f030f100c0c100400f141a640e00e01805440d40552000ca41080009003981b0041803048080d2900504101c07405aa1070310090b1020403d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 289634595 1250 289633345 289633349
    0x29040b0309010207060c0206090f120a0302090a090e0c0108070e03060f15030304090504171e090a03081c060f051503040203070806070c060c09080606150c01090807050f07032a 77
    0xc5d10b20700001c200e142600080c40c01e100324400000c8a000c40c0c002c1502640340c100c0c040983c4540c040602c4400c01d101e001ba0058580380f0303005411000c07000e5480701c020064860719a0302c420740d600400745011095034000308080d401881ca091203192126124042a40ca4400412405444510102040012041030300103601ca26004040300e45030394482c07803560b0060005480460b58a401645480f0b8540d5040060702c40c11585602400c201110103a02101581d00416809500c151007820101c00541450040c0852001801e110301000e007030035250104480454004065040b4002e40820803a50380e020452400d01c00c214150307440b0303100d900c0807900d0b001c4c0c2504480110701441040180d1964010200e41074507008500c2171000e07110101c81600c0e07441541c080d4a038aa042840041c0c91414070307070001d61784845030025a40c506210301400364215441008101d40b40180044c4140504c001084050841c05030300004d001d4551031699903241030022000340b00502c41103407100b011507003440c81c003000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 289635845 1250 289634595 289634603
    0x90618050606030c0306040804030609110d0809030601050307050307090902040e0304080312060907171b1306030f0b090f13150c1e0509120304051929040b0309010207 73
    0x1484a900345400c41d1540001c55800380244511050903880d40340c005081e074003403500900014600f50642c4c4500028160116043c3c4681d0300b1008080129140d10190100c05d500904000b41c03909072800400d4104001a80302030b200703030300444050142d5a0301041030b10450300c8503080002c11180a101060140103282107840e141e010104001541d41404030081210f000c441c4c01a500070358400c02001002c0d102034480800094004080001e00d051882106800110050346400c48100030048800070f640407819107080301181100400c60540c16002d1424039008541c001d001c41e11424001c500030300c2c1e000f04010b07043e10503c40401c4010410f4040c0d18200b030f0704145220f50f10034a0035181d00107442818080c80005035609010031540540c54131080e4424a0b5036076582c83d040d4903100300100b0200e51a0035080300d00040000041680d5810f0b2440002d4941078001c031406803419500d00060075040780d500d001364038406000e0601d101514210f40c00c1d5103006001c0c3e901da840d1070451600900410034020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 289637095 1250 289635845 289635881
    0x30603010e3408100501060f031512151d07090501210212120405120c01080403030c1808070f080d0e040906020903102403020f040b0102011518060501030501180906 72
    0x130b02c2100182c001c503050700d11700d844402240d0403c107000c0b07080314401c0c480705514161000c0180079010140c2c00d5100b506000c1c20b43c5682003c0d21010385070880380c1001080040c0c50545030310050641080c0024802003820032020802503151410b0141140351001001c51004800c0c5400c0d0b04540d0b40070202d4641070401001c540c4048003596903078103160700c14082c262245c3c0c6582e4031441c8003140028603400c044010781d5461140d0b2200d581c182d02501000044509019400101842c1c01102d1102c180003030110600400002c0e01e07040800c0c074114550b030080080c079002450a89600c071340044a03880780d850155000074007501030b41007480080c0969001030380d25000b6210b043e04007502d1500041c0d40c09540c02031140d10505404480300042c0c909100094106c030340005421000e107802c1d40900c400c4d500c180004901c3c0c6c11030201c04144070549810001c12140d4039000d450928019114081c098582800c040040e9414203a8204100703d07805202003c950712060341a007048001e800c1040d003100094036007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 289638345 1250 289637095 289637113
    0x50f041802120a1211010f02092d0409050109060c0905010206010b0f19031d010c020d080406060308031e01090605090f18010c17130b0408070501180602030603010e3408 74
    0x42405c0345008800c40258248410031015a0682c800c45805150040004e82444586951508003140100d2521150880c1c180407500a407242d010301c192940c820000040c00c148140341c4401140c0340c1c2a42207081200c2c102d828086640c002402c1c40c10346040c05000c589607003030440f03c862640304020485951421041d4001440c941540005409215004641c460103d450781214201c4805e80740d5200164004207030401d91600640140d50007034098040401da513a102d0b00c1744106d075070040e0751040c4191030946444070b144c0902980c05014111040040c08860f182c1800660301190141c4641020714000010a5610a0021281440292010083c01142c00f010f60162410120200c0d000400342c050000030411b0000743e4000d802c680e4030103075200c1c954499031601030180e00488001c485542d80c1c2c0c5051070130315008226440ca00b0740705000150350303440d2903001e050079904500700144c07982d840209854901c208060401150354075150300094443d207a02a119240c0c40780303034000030142c0201c03404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 289639595 1250 289638345 289638347
    0xa020c01020712080601020f07090f1803210b01020a0803070203130b03070306080f072c0c040510080f0a0b01200102030702011118190b0d0501050f041802120a12 71
    0xf456603240c85600c0e48036159813804010398440406030f42101564100e001c05021a1415510003c4c885601000001f0f40c3e0392a09441340c058002c20307006030040b17a079034031902d000d0a403110508442801300000502c00041c400002035922801210010852080840082c10b910300c200283d42d41c0c001103412070000705554214421940c0d006440c10000a428a076000c80c0008001803240040810308000700f68040c6030880c84440302101100320300524100e46140208050b4012903103025000c0400d0346580c0750b152200300010004049010000d01c000c1c070040041102050421a0f8040300c0b01c03001003000c18245004844080102104550030400b4400c0b081000d003055002d103100d440d084d0002c004111404520030820b000710341c43c180880514500a030714608040340680000c5195180da0450b04e505c422003010160880d0f0031005049580b03d00401092411103410500414183d07000c01a8804d6000c1c00f070700781004050007038001d14074000c40740c0490204000d00e504003504090050740e60802504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 289640845 1250 289639595 289639613
    0x306011202181507240e03121501031b080a060b0a080901050711120a02210703120606120b06040e1303170601120b010c050d0504031703010b0306090a020c010207 71
    0x34030b14000c211900c12405600301c0c002c02c5030f600302d401c0b22040c10300c0c04ca600c80c5c0310300785e0280c0c0d1302c107800641c4c4480001d01000020006050825095a424000c610700298a00320148948800c50704060502d8551110054000c0181d400f49019240030120340d0740350080000a005d882c0c1c8020241240050200c269a41c0404070a0265210f10000d100030703111408200c84140d03034003000b2042c83d049034007a400d81c1c804c0c0000070107681e84ed60058076030350451054000132503c04c0304048480204001444002c143d800705120360019000c40041118900342034004200c80041851822215030f5100c120000d6619013054070010000b070610300b6094906041d11031070390040034a0890200d820300f541034841c1c4a282030201c0c41a04103030364003136208005034040c4003e07010100649040c0041070a86d2004104244542c20064400ba00c5081c3e036203155280c08100031105540c40030f02c024050005215038400e0000300c98001d002140e5400a40d100c19006000038810344202c4d085561001030360b0004c000305c0c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 289642095 1250 289640845 289640887
    0x40302011b230406090e0717010b071407140402160221070906030510020d0e0d020d110705060f030601051c0f0c080405060402010f020a02040f0b0301110a02070303050306011202 78
    0x2505910007002c4400c102d510380981e006040120b02184403c1c02003904900da41c540c004138500d84a101915500c003070310312042c030a802900d085400040c0c09418051140c0b028449660803100511509150449001015a044103554400e503000a0000600307007943c00480350f050340003014903c2c0c5500303000080d40d48406082c200c2055000761240001c508001b403149000312a04803018203801a21008200025404920401403503983c41d50b007114243c40400030b080300d0302a02c0d0000c140c0c03d02d44580c054005410250380b40d406a02a00b8288400d840d0b81d03054544008078000c185850b502c0d041c00607140350080071006540c40c928807500b072025071200e8108034100300b1041c0d001c000d0300a88400c00c88010104176800b5001e5407122000c00d0055100780d0b03942c60710604510681d01007003900d50003d82601e40180309413043c546c4400c0900701c649001c0c8115a4031066685507240b41404440c80607407030741c0c035134440903050002c0400000d0960740540395201071000d19040c2196156004284504091018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 289643345 1250 289642095 289642127
    0x51603110a0510020d11070f0f0606080307060b030601050f030a0f03050f0a0f0e0906010c021002070b0f07021c03020a0b070203040f0303180b0412060515030303160e1503010509040302011b 83
    0x42c0346c40e04400390100450300001d401c10181c0401c0503040d1940e01d5140701011003101e1056a6240c00112030708240090840688901008900307940768801301841c0c5038040c1c02c110700c40c02c80ca540d88800d658000075080d036180d81c80060036130484c1c0709040540e51401a098604400c0c00c1c00119400d5070f075481041d1030f07a0000546c070f90006403a49071701801541c01045481da804030706040c441c040540b07001c050b081c0a0503003074412071703051548429221095400003034100700e018030302003405011442d01320146440703d01c6d24000700c402e038030494600941c0c507140200040c000e1040c03480400e001510030310446028101c0880d1a807031080c0ea91034020311145016005da20741104401d0080b609141890840703041700c45440d203d0688040503201c1c407000340b00207003110f1b0798800c801c9009091070710203201444c0700b07640550b400c03045074450400103049645c85000441c49030704900070b54004618498141c9064600070349070030500b9942c500d4103030700400c895184490020441581c00300440e0f0700c40e40b418121052 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 289644595 1250 289643345 289643351
    0x11030a06060203090d1b0503030a170109050f130f0b040c0303021009020f100c06050c0912010903050315060c12030106090f031227060203040312051603110a0510020d 73
    0x601c600490303ca02030290110b92088200d8090004260303180c540c1c86200b000c00000f100c901e580c80000914540c40700c1c94100100f60550714841200d03515441540c010107996906211500d0f000c0c14152845400800d1131020142c511a000240300070a4242480309074064611030341c0d404d290408201880da1131000701c00500c17960304103000024041c000c0150540c0d016085201c3d0290780b2040002640781d484628041052154405012451601611b4001d5010482103513a030341d400800d00040c030914610040c0c840c0c0c1030000e500c0c00242e1020440c1d80c400341100b8081c56050240000400b0303486841144080e6106070513800840d4038007440254100e4015480f880030240e6200052403859850348405410314442c0d8041c890034501a0046001c2d0500320f030021401d004408050441c0c0312100d4210000690000c902401000400305040e44002510700b405420100414620141c10f1140c1d4001002c100b114440d20072181c90400c1031036045035109050f205d1280900003110029040441c42c0b02003141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 289645845 1250 289644595 289644599
    0x50a0b091e0d08060105180d080703030c05041a0304150c020c01030518062e0801020a080c0403020d060b06131202090604150e06031e0307020414151201020c0111030a06 74
    0x4009503002c1ca4070800c1e1981c180c42e680307180040d078850300014610b80c4110000500c4050325076070903641400c080d2107104142d40300c8100d820014122014000d000341448000c01c41170150317000340f41e404c01c003e40d1a021540d42d60780e60752a00303075090f00300e8400d250901c1d41050308600300d403074000c20002c1c410f0b01d0a0781e082103181e83d40600b20b82000350854020a0b65044100070580c0703903da40f0907006050303080303c0810001c64140041c9440755079840d4400c450070703540170403074001480d44040b9064210005680036410a03045800040e2308600301d013401002c0300d585001104281d00d1b100f058807051400b42c0c00200704590303242a0000c41c11840c80040344203844450000d87e040c506442015002d86000201d00c1d0014184030415800003009402650b0511401002601d01c1b00ca81840c1c4031204078140265488481074410302085d100c0402e20f40c4075461070002007000742c040b10040360038001d404840160650303840724403540c02441140d01c001055400c0a410248200380c0500460044d84441000c03c17102e9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 289647095 1250 289645845 289645903
    0x40e0f0603060112030809071502060108071413020d0603140c01020f0d02060f070203090a031406090f100f0603062a1e08092b0306050102060919050a0b09 68
    0x2202409216039400701e0180c070b1300100788a083d005a100d00c041c000c44070b80302e48500210240c403211481110040c0c1c071031303c0144540c1d402405131b840104001c80c4440420000c00000868161211034140720303035075010440250412554000000554002c440340c8840007010034899124040703404400d0251207001c03d15503c031000002c0e0144503070240e6000c2c027a181c5030103d54900c40000607201e06d04505c428003092441e5582e140c11000118400e00746001c00800f000c40c118101480100410304ad40c02c5001c84410380c880101d01d948509150baa400160181c04083c028014802a00040c00c820b1138482c035400c0d11680135052083c02c5040c0785c5500610928528112541c585c40c0c030314400140c07010801c103081c0a001d2000e084c1c2010041c4251a202007804070804039030200343c00040403000650b0450081d075a01445544003a02003031010b0111480e00b030641030740e03501c3c140000e80000001039200c0000d014060051004181e804050701074a828041241e43e03941c600d0340080802007865084240c1c42d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 289648345 1250 289647095 289647103
    0x50301060609031109190e010b040c0c17031812070b010e0c04090b060702060a030902130204030b010e090a080703090501030f061203080a020903010e03031603050f190b06040e0f0603 80
    0x3c0e9031040a06142180f01014041100b101902c0603c4030511100c100007101041d0141e10314050a81000040c2264960100829105540e2004040c0f103407400e00c6c240407800c0704c141e004007460001c0600e9540d4440307907020180c810f801519a8000d000743c002040005500030010725102d4020312100c240c903604e645a414030341c04150f4500c1442c240403c401c000f9020150401d007000d810003059141481c40303c0e004681c1690042400c1000039903a0010841140741a00120040101400e01103080c02c2c01c5503111005503006000d003002c4068401e002815102c1d0400c43c00a02070f42c45000c0d1501c038111031401402d5811a400703158046410540384002c890380910aa1044409540310004240d641ea2020341b0004000391040b101daa4003041b5454880d08c1c24010042a9400d000c01559a45013440e8400c04da2082c00e80c10030101800d04050048143e11040300c581c1212400f415201c0c544c42c1e220311280100601c0440c03907000301020900055040c01c01c902c0700d1196400c1942c00119a40c0d0b00205621 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 289649595 1250 289648345 289648349
    0x60e0106091203081b040311010215060604050405060f0409030906080109020a0e010c0f0c0f03060b0307060807051c0c0c02030c0a0b031b0c01060b07050d1815030b090907050301060609 81
    0x200380c0c105070358000864414140245c008a40800b042114040305004800561280c0c20503981d82081460081c42d0356410484c00304281504401c01f0b0085c10001c00080a0748118802c4c10710031034641c008076505139120600d4194100d8010010070403104c2c1c0345405400c030446031054402082e02840005903000c01c81c000c0307810070003084d40c03600c3c04080c007d001529070110005041d02c146042802a00c0001d801245160240155659400c02d1f03d10303600c1c2c101c0c01d1b50a03909141c1d019801429040011540249901d41c0201c054101161510070f1684504122003215078517600300c5042c00340303082c1040d4102d1200202603000360700380c83c1990301c120306001010416111701580f0010400001e003812225415001c120b09031605801c0c40d040f0858051b50030b4a403281c0080a80b0030002407500c080010400400503000c40324140b00c01042402d00159002c41c0c00f51140e000740c040742514065129200c4e40c03000c81c008000829050150504850b400e68038819070250b58060b6103480d0021480c14024031040701 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 289650845 1250 289649595 289649609
    0x2100e0a020a1a0f0a02010b040609021e040f05093117071101030209120102131d0108120a0905190602060106051204060b0d0507030b15010504060c020d03020f0d03060e010609 77
    0x4a80201302e10700c040c40e54441c40101c0b085540c0c5520681c116a03550080100800500e0b5003d80c0300e0308040301c8885514103807000d0131a03204003004200318540805000d42d0032104100c94a40f11503980000000c1c1d420780100302007d10034003911094111181c46503400c02d41c0707406060180091040034140c100d640c400c1c084080c21170035044827804410340c0300f90020b0482c4100544912a03d05180c41481e0980c0c00000d8142c2d1500c100d140b0a2140001c241428800c003090301d040380f40740c0d502d0400100c0d150350300c0c406044601e1800043c101c0d0034074095050034006040141035000904180d800700c0c0e85180d001d000380b50050113048000504284101305441c0e47c100901c07106079103501c440d0744150081c0640c6504640007584014000302052003032000e80019402500007080502c8c0c502200d11226070020003907810b04c43c040c081803202560050300100c41d16410f60300000b000c480390505902c0c241c03e00e80801d000384603034030020b041c19505821003011148103c20f414245d0b6210901902c85110b2402016 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 289652095 1250 289650845 289650847
    0x1060e0f090630160501050a08060a0513020c0f010203060f0d020a0f080f16030309030605040f1e1b030302250e01150806041a0f0102100e0a020a1a 65
    0x603601e48180c5964002c0d10080c20300c03180740d0704080b007580c1d503002444920f88094200c0911460003c0c090041808180450703040d00314003424000064020b00500c1d1307403402040f41034800541580c444207124006400c00804400607072180d01c24000c01307540300064044641c0900504e0712841d010500a50b40030b00c0000f0210201c16249005208900240c040240c1c1c0c042d02600f00010301e0180e28134071070050a00c0c0d00250101c0c69901d0741c01490718840d0400b00a10701011181000820b85c80440c078800e5a611200108080d210380c00c180d40000d403506c10161042800d18050040081000d00d0031500a200d00264140310440f603003a07003103e1240d44000b03009a0041c554030203403402c01c010812241d501c200510252152513034148020038109811041030948544c01c1c00f150290000a2554450002c960a02c9801c00c1811011040901106054004d0003c0356604446038028801d800c01042310440401c50030b998014100c0c4e499802020590064032094804150b0340034918280340d0034901d0140365 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 289653345 1250 289652095 289652119
    0x81f1802030709020702150c0c0102060709061b030203130902090a0f0e0c0f04030c0e04061d0703020105130e0c0306120307050604030503040c0e0406050906090a0f08210c1201060e 79
    0x20004e9806030781c1c104c2c4c1c4039100311951140c0d000c1c000054400303000380d14000e01c1592a07140001e032801102601003801d00004c00d0040017019442407070041e03000c6018070314244448203441c1c140e2842c0520007203062000c15178140440e043c8103d50260403411411181080620f50340e10074149072a0303090141903880000c0e080091340140c601030081c08503130402c050042c5000c0c0c1d41d40b20361460200a03007000e03015080803000c1c0801d100c03003805480f10040703245040c48802c05208090b00e41d28036561000a040c4503001c03580401c2c0c22183c0340500d0080c00100004603080c0380413428048243d10031120385108801c0b50854001d0544000103440703c8a51100c02004242c485440c03e580b00d4100030802c03a24503100e0040403c80a11070707035105004500c80d01011070f4900b42659414108a130041c00900d182d803020b0500380100d81410301c010721064110880c4d690341d55595a9294100c0c0401c440395800400c81d0092100c0400c40000034107612440422003051030340c0740c160868825114139411a0b000c2e07180300103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 289654595 1250 289653345 289653359
    0xa02060310031a010e151011030d0f060305160e150d0218150102060921090301020f0a0e0303211302030f100605060a020601030b10081f18020307 64
    0x295088000a1081c4903502d03660b940750300e1a4001d0964010031000c001004200107592039880e542c024a090710703540c11550300000810021421010040b040188906000c858a40148102c9080c0f07455840140004040300c440c8078007070700d402d20007103034244103294010034410f05e04440355043d10101030780e00101e038a46140c28003d2440d641320590744150803002c41401070792000e0701d281148a0407408241185480c040c21209804203503607a0f419500718400b0020035901c0030800d130304403c500b41c955256000c2030340b650503001d008001a05406601c0081c0340001401040e0203021a843c03a0ba0750250302c40804c0382030640328080d8003c203942401002c19502d460206c0007038031341c0d0310111241400b507200102d0740000c4d2401540001074101600248610025000c050240d100a004281c90061404052040c02540c6250511014007041144004211a00281600c1100138400882200c111800d0100004022040038550440c614030700000c0f410082d8059000b43c00940d0020040c0c20028a4901 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 289655845 1250 289654595 289654597
    0x319080a1404090c0c020f0301050106080106031508010608071a04060e101115011802030606030402010c2117060d050a1104091401020304020a051f1b0b0702060a0606030e0a0206 78
    0x81100203030381080c4070125200342035118918a044c00c954035050390020a0051211480030a0f003010300a034100401809402e03006400c090450398103280000381500e401e9000308455000781c010030003950030300000180d030a40c00103018041d1568000c4540030000707030701407000340740c442e5201c1d42c00451601c102d8030300c1c24507110401c920561400d0400446030007400f40c005051074500c0c0d100b02450344500c0014014000825a2020218410039045145003801380001c5d10034080240003d0420004e10310071006c000b40b528141d8864000d611201412000d03082000e4400f5000e4010759800d1410380e00012a1464444034101a2a40000c05015084001c3c1c0750346c0d41c201c40e00d14200780c00c541c985403980005108100005880540440016140e040034410801c184d071180e07004920424180c00055100e9600d103100d4540080c4908080c0000210080c0a03030b02c03848030312409400d01205404101d4083e40216046224091006041004030303102e6909a04850381c402450762585d0200601c903006040080c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 289657095 1250 289655845 289655867
    0xe18060f06061309050f100602010e030f0c03091f020c0a03230316050a1104050705031f0b07080a02011104060507080315190303030f0b0f061602040507020a020319080a 74
    0x40c440f46070b2191207581c04020b98405544000c18603102504101c80ca540203109000a040c884c402400000c03800c9591319524051003240428074000090f0203208820100308035901c5141c00782c074500d0801c0000080c00d0702080c06101c0725000d40218102d044031490403400800649600c000c1c2c2c400f03201c11288160f001c4070021400404a8401000a0048005070b0611007401a202d44020a40c1c0409441c003ca44503202d0482280a82c1c01c100030302003540e8220040c5ca034400c0e01100c0318100c80400102c00080c4560036030003030707110030b80025801e42480640c4005040b20302c4a03030003e00002800440b45042c0344175501c660000140700748559000102d07460010754000b00030440302101c0000c0000000c54000784040d00705d85080099204004140e09409291180e10000108225540d419000319070343c0a0442025032140b400011500c1803200c03103084246046030040d0080009140400c00070795902d000b560306910901c2001c1100d101c0c0719003040851300244d4080b003018104800d05030192407a01100d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 289658345 1250 289657095 289657117
    0x1b0810050319050114060f060a05070c120b07140901031a0a08070305151306050604180b0a0f050c04031704080d050406110102161e020a0e18060f0606 66
    0x40200010240e4040056407425015440a01a03200c001d290030f908450600442c0b002c00d064102c20440644d0300d040001e03d4401c401e8890703075540c03a07001c08102c0f00d5202e001c03001041000f80c02408200c4043d00301184403001e10940035810623440d40c20041d80c2000400d0440e0b0000d440800c80c081c001d501c80d1300f002d22500585103a1403120044080010580b00468100345455403041100b0018000c0801c400c415044011140001c00d0400e024813900411f850032000e00001d4541307020400540726036104882c075080540400110060b1440e148081c01420b48540c03c2c0e00e41071a41c01c6621821610802e800380d01c084500f41d06c0c01d40f440e81d400150204802e60114105410300c00061201024040c00d02c5410880d60380d20387d2241403150141801d085000c210006038414049901d00803818008015035a80004126080780c50f1134039101c000c10030014000790800310256000800000d5105183e001d002103004c04034000c2e030b5041a096581504441c0355a4007a030600200710603061501c02061590308d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 289659595 1250 289658345 289658371
    0x2030c1e09040501090201021e030307140c010516090603060e010509040f1a0406050709080d11010b180f0f13080c16030b04210512060a050405091e011b08 68
    0x385900144054100b00d50a80300ca075140d1401c03070115a41400724a400c005040c00c8030404003a00802c140d500d000040c0b0329802c1c0320380761098592aa51b035600343c804461004001b07011904e400c09c000342e041d088110703055012038025400822402d0003405803c06840020201034520781c81d181c1080202240540709485084585180100ac21107000001400540e038613140381d000d081c680760010454400510903010000c2c1c00c2c80070302840b200403880440c841001d00d0500d0243c0c032046c40301c5005000ca4210503a2000d14903181c43d181141d1181e8080c0726000034a100306007527940d404c0040465004403212203e00f403040003014005412140a007465584410840d141c0d00ca00d0141106102c803140c01c15604101c01d4801c000401041c9603060004010440c07102607404840c00f0080c2c158020150b40080d640c0f0346600198068650600050003408020000d01c0316051050480344c540001c8107012a0076030410780b0048111505008a0703102d00420131000060f08038403841152280e8001c0d000d80780c210a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 289660845 1250 289659595 289659649
    0x304080d142104210507020402090f1c0b060d0f020d060f06030809040c110c04090516090203060102061005011704030e030d02010c02010e15010303180312050415020a02030c 76
    0x800d0003a4182d03074010811020b15410309003811001d0454010b1450034009903035240d002142d40c003005892034154152400358407081801c00150030310545d8070303101760862030000900e0703c0001021300e10100580038400701120742d110031007401110091060040e189000c561208401400e0519030244a1802003c00143c500b000f90400700035603200340e0080c2d940e00400311744910a03141c035108004400b40d550030f100c2084004211b40c0fa0b01c0300603588600307102e00d6841800c8024800309003c00a0300306501c03d406054280ca640340000250010385095005220b21300020b0b183c081404065401c1d0348050712888000c1c030f850703842c0000000f00200300b14108242d12030010402c1c1c60401498400f40d450b9000030866000c91403000f821039807120700c0d444965004501d00c03010003008000003411f50380c041c41d001c1c50100811240354800d0386241d00041c0564090100d605070240d000d0050019240150444501c207003040100f20f03a207440b64580651300d50001c840c010114035110740040075220340508402402c403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 289662095 1250 289660845 289660867
    0x60c0703120c032702131a040510081507051c0902060c0c1504030c0302040209011403161b1a09011107030503060901090608070902070201031401061e020304080d14 72
    0x681c25400c02e0002c03903241d25a041c1403031100300303251802c6900501d144102e4101900002c400584041c40c100d82d00b543c800c203202182d1441c03001100a46c0014200740142e0408800301c08441e070452080d00440d01a21072a17800c50359000b02000d0040c103403580e5803400c090800700eaa507056079419044607442540c50850034016110352015040c84034000340900010300c00d0b18144000e4805468001090400400c018000118404003103810340f50191001a2200c00220058849407900c5411205008001c002c009010400e501030141038074155941400da03e50703c3d251065100c1000d400205003814050740442920750101289621044003400800c148100c40720642d0954410103050b000214000b04100140c00d00ea03964600600300741e40100215441c3c84002ca4a400840c0100b10030140c00198090035a807194105010242c04d03e04603210650356031101511a044030501d0381c002c1c1881244d038164050000c801d9404641c2620081c01e0680042042140e240c98404c40b68580c180007400180866 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 289663345 1250 289662095 289662101
    0xa030e0a14010207030e06031012060b0d080703030606020318041e050109390c0314030106081e0106091202030a060608031c0b0d15091a180a0203060c070312 69
    0x101407000594580305418001c0c02da1540c410414002c039010018071102403c1e07507601408692050740341c0681d0807050724040c0044d00324040210b60105100d4180e00034410348000500d0001d200303403070070081c00b50744d00801c0c0e0300d03400384e809410862501d10b01c401c0144c0c102030300104210309110035201800005070341301404a034000e810016485586003858600c0c40940360384620270f0251080c044032070009240780c1d040309529490f80f00d020414055246800c05028101207130311706004400c4941c0300e42c2c450400400c40300701155201c4620001c40115220460000380440c1030328101e50312140c00e80e08140306d01c5040c0c04800d0040340c00d4810110142e01084103413058001801c41d04001d10f0b40c40041e0304803540c40c218020218900649000d00301a055564048021100e035030080f0240c19400005844034001d181d541005009031000d00c00c001003d5800400710303407241140d5208000c0802d120544195220b1850030b0007034040c4d00c40c0000c140161496070140907110b2080c07800400d02500b914080c001d07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 289664595 1250 289663345 289663373
    0xc01090303020901030e0c060703030c05041d041203021216050f0706060e370b0409050a0615050d0803041b030c030b160819061e051005040b0a030e0a 66
    0x81d40403030004901c0da814090354400c13010080081c07c81003001c1002680605c11008020305159440600b040c1680c02403043d80c00a02e050309182c071220380c001c2d2503155030741c00845044484019000c9a4000d0354040e1003035421103c150180d0462942d510314000620610244689092000906c8100e500540210042c40028072601d0045442441c1c100c50600c8000b01a10980e45d0418010a403924021078402420004610300c440b42000094500e50000034240c03031400f41c5d08282045805028040000f076150f006c103110340810080300a141c0301440c0400707002e00800307500c4030044002e100420000005950030038080c4640202541501c140c03a00228516401100c042c04240c40130003e0000700301116502408100046200080082e4010b200c0000105450028500700d8610584904141e0240c03001e824550984070400c958181d0410f140380c000c7c41124400c0e442160403148841c4500c0c15201101e000040b0f16040408600060300a4590010702d008a440707006100808210701440c05c1c01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 289665845 1250 289664595 289664597
    0x10201060b0d0e01200d0b01120f0b0a0b040810090c0f0f030b0f0106080402131104090b0a05031c05070512030703051801051009090302030c06150a1a07080c030c010903 74
    0x3aa036503c040440c0e00b501c030b6105008885200072211200344811100031150503000c08400003070240d00403401651041000807507030011030310b803c41984103c0c1e050382c41190b4034075040b00d00001c410b58035008408948100d0007050f08540040300d0600c2c09400740d4000084240c49943c85e09442d07502d5404410b5008842d0b0310417150031070b09050800620030303056890307074218500c90f00c607800303540c10404064218500900024000d031180c580c01100b0315440da02040d0385200800d800360780e640d9607045541c00f0b445800c0b44144641041c0d9400202c3e0b20f000a0b100101001d0000d94045810064034242c4141d04130840548150007080042000c0c402e41d41c1c02548180415100050281050310b180c0303020031001d91000c00700b44c1c9000180100543e4650340c2d0400c44206101c041041140d81c60105e046028043d4a501c01d486013038140452030b030791072448480315a426035001b0b400980c3d680340f03903181c1c0d20040c1800d45089801c0040902003001a00200450206101143e280608011403a82107503a84541070f4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 289667095 1250 289665845 289665851
    0x109090c27030b070903080a0c030509120c03100603170309070306020409060e0606160809180405030c0f0616050d060518091c0503150a0f08030a0207240c02010201060b0d 75
    0x40704201d01c1c2c0c414580c101c139180c60002d90240c21a034594640b4803507005242c01b841607191340002010f00c03170012592002001307404e041d50121182c0d16556282040e4030440e02c00d0181884c4280a00d006110303a4048a8005245c940b0310fa1903800120515807001d03054001e1030280d0307003020022031090300040008041c0b014001036801d18182c030400340e0340c0002c4c01c580c1c0300e07440070014243c14140480e50001c0040c1c00c42c3d103603540c40e4128000141f41c420045520340224507034800700403d005010000c0d0801507941c800340d0318031048107210581c803107508407000f400547c101c0202a5000d03200740058500c42c1c621000000e4940d8030f45002520b488030741041461308030828001c000d0120b00030300544e800d001e1a459800d0810684130380113030440c00020083c02c0826030b04108039520b551058002402443c40010620f1a01c4c0c444070300f561241e029803e4600544511000005c00040580c0702800000790038001030f508d00f84440c0304980c00d1001c02030680c110f40d01c071000850f403044494018020f840d41d500b000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 289668345 1250 289667095 289667099
    0x9040c0503100605060d050a0213030c05090601180e06010314010e04050d1d12030f07300e090a1407030b011704020109030b130f031d0a050109090c27 66
    0x42c0750030032141182d01024140401000382d0b8480500703840314200c5400c800b01d00381c3c1c0e030783e00b2a10082c003d82148110312119403900105106000d180d604c140c1e1000e440c032988030b580d640015690300d525110072000c1c1404404081011000304080d00e40c01070b40515010440e241d0262126104803401c0c3c110691082c00352042c0800c101080000c000350b0115424180420710446138443c91a98083c52030501030300b0010551005600288221284e150041c07192a80364617003070500078801d003024607040004e45030300c54140c85200007000c001d4401680c2541d5a8800380112070522502c00406010720700f40301c0c0c82d4400040303407a00d08800680300e995a9500001c0251001000620a10242c1c520a0a8400050a1001607680800008152604841039200c603484a80300012060903292000c0c11007001e08180e00201513000341205c50840064410a6290525208200c19884039120341408144290707403c20074200113400844007040c45081a00348002d0100b8100062101d4070f200030a122440001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 289669595 1250 289668345 289668349
    0x10030606080717060f04090804080c1828020903070e0703060605131e0f03110a1706270f061b03040c12082b0f09050309100c0209040c05 60
    0x100c0307640090580b4008603881070f0007504103035040780500040d0141140c8840d04985449540100c0030a0783e220390718658039940c1c0d03000e1988400d0021040d5104580c010244c05c91501c1041415024109030300703411008031446044604883e8411000d04001d680a004e6401655401c1c040100241100d503803029140c900148000d040f904640c0040003440401d0082401c070b43c480004007130070f907403000c21000c0103003d803405040e031828040d601c0008403680c440e4001c07080080114200c086000140c90f0f0140054540c444174454214620503010680d018400261022190384900000c440300c002d2880c440c038800350307800350a025642c00e0b07150f140d5200d402030000140140c415114040c85400b4802e0031400c065031108080101e81c40707003403500300d040300202080c0030074402100e60801103944110200507000c060020a2100c4036000034000d4076040c8d00070010760f180e000300340b104c5501001035071601d25600101302d001c210f46c210340c408201c0104826001038a601c03c00500507401514802d011520f0141 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 289670845 1250 289669595 289669607
    0x8130b090a02040b0427022b02010f0306061b020604090903050306090f01030c18061701090201081f1707090e1c02070605040303050c010f0f060518010b0306011d10030606 75
    0x40d000d40a549013550092400003100782041117106401d5010401a1b40c0307000113124100030300b1076641510002d0500b0751070056010407400e40b00c2e100780c0780d2290b9040252403d4045500d248102404200000030341104194081c140030601031000744010b003490344403020315007180d52240c000c80c0481c0e4000140240c0c0d1501c8000c550744070302c05003c080e10303e40c1541d031801c00b000700358814280c542c03909441802c05910740ea00b11802810842074060720354210550f0700350103461204030903808141c0704008102200c1008820401c1e03040c0c03040f1210102490f00c0c10080750548106d0015045005204020444030b0035409280c4101a600b402090110301c1214002400000b070414881590310141c0d080040641020984040300d4042c00d00c2c0d42c44401c0c5040c082d014100600c4038a911520b800c0f00050590340c1c6600100941d5001e0358100e40042c3d0109100010120a00440203540b4003440026460b41c81203200800310ba003811044004a40e803000400d0941044400760790129480d54001d02c0300a84c445 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 289672095 1250 289670845 289670861
    0x212010506040501091502070e04121101060f050d02060706110c0d020f0a030e0d020901150306050102010203251704080301060305060402090d2a08010e010e0f0c0108130b090a0204 79
    0x140e0042c40d1a140100203000c140e818890710405481030003201070780c14003d0103a1030003050070342c002414500d4140b412021030503551442c0c00200d000800c0741400d040c014800c00341030720140040c1170074240c20801045403d100d0310301e04a90002c010820000021424010100303a030300c0b110b20040d03d40d9200c605180c1040081706001c030071036000c51b1040103407410009550417800d8040c2170500c0100d4600c4046022625520340c06034010040c0c50000812a00006c4501c11907001340c0d408012150f12a801282030748019141007895003a00300f0b0444025a22108809201c03080342400c9812070810803151100b88812542500c072400088010803e40f60540a00350307110000b2a4114900080c1d07000040d100c001d4810081c201541507410311007900044034000c03407420f01c010f004174401c42d590341c4094040c186021a0340900e5080101650b030404001660f0300c41a00c170791000d00540301007400111242c11000b4011601615905030640c045504041d101e801641f051015108804290051100340c600301 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 289673345 1250 289672095 289672099
    0x1021c060e0c03060409060b04090506061c0308061003060e0103060207020405060913060c140c01020408011a091603020f07110901061d01030209132a0c0804150c06020d02120105 78
    0x74000b08080d081d4900c0440e503002d001200c00281b401d25034203011006000011215800524008000e81405000912113110b044108c40c5003d855001c1507030f2807694180d0100c000c01040012000c07512070314140f6200189810a0f00e000100c640d600c5109c0300f4400800c0c1c2c0242d84040e400100102541000d01485a01a0302501e04c030951b030400000e082000c450346d84010740b40782c1c0c0c0d0710305c4002964400c0c040c1100080301c80a965880740107100540e4000d501c0b91040c040250320341000001d489a460340303d0b05404038001c01048443c1e031699200c4030403151200e0601d04140d401c0041d0384c260015500540340c1103008210241000c648075062040303841c4103030040c0c01031105c2d070988040852145410a441d0107421700e405616000694081800303005240031011925044c08101d4004125440308486660000c0d401048100340c0000c1c25544440b2601000c1d10124007000248900030300c0a8410720685002e1404104100c0d250711030380200d821250f0203c240d141c0000c0c1c0304d6480c00700d6400c002d01420381 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 289674595 1250 289673345 289673369
    0x14151216080c340606060306090b0d020d0201050a03150e070206180c0f190801020a0f08040305040905040f0c0e01050a0801020903151803070503040501120e06010e0907030501021c06 80
    0x20904001040f03180300d83d4148907860303650314000c4404041c0b41d40c0e102a5600a00070b00c060342e203410014024142900601d90200e01d0000344222074500034500d94007041d000f410786450700070581c0045640707a02c8000d1100c281601d80000e0900b00f01c480e185c09005002c1c01d4850003044c1007014000707051801c013034525104041c007588115041c0c40f01240242c1c40c60801c480c414110721551001c1819000d035940362501c1d0b801004000a08040103400400310208140d0760b6402c5046a00703000d40c0e065a05803005800180148002d0001c030207994841c0340c000e4002e8007540c21070085030740c03008903182e0a504080303e00082040104028104503030904040c204520095040496210209550341c0c0c1450704c0e40c00e5900b2a402180c00030b5032111aa440c1105000305a981c1c40c42c00d0304006559900512890b030008140340300d43e106400c2c0324400e94006c01404005803102c0c0c0d103000b003140ca201c0005400079080340250040040021800d20040803041c0d0300c5880c000702824111803200840d1025400030603000c0c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 289675845 1250 289674595 289674607
    0xd050a08070c15080105060a090b030a090c060807080a051005030f0f07050628050c03040602070303080105120a03230c06010f1215091104060e0a0f0614151216080c 72
    0x180040788a815103105684c0300d40c9030700c48c00b003044410031110f41c4801c124010000601402c007202e500058800d0307000780f0000c25a07595175102264072040c104c50100c006600440403512480e0150440c903040840c11905a000644800005c0e00700243c00181032401d030302c20f0070b5501c062003060148000504080b95807a0608082c803040913031074545624240c1c48510a004280822405041074a100001e0781040b652616240d100c013a5880d02640010b0303020404000c00014a0f140240029200300941c0015000380b82c186e582c140c4400030a0002178090110703403a52906641e2041001c3c166800302c0300c004202e6075140282c6203480804e030350411943c41040110303202c003103040f0452800c8020342e51840061020018144800702140168034240d0190402e00c1c006608058500c000e40645880c90701045003651041d07120b01181c03058411400420000c0c01ca41546103030111031203101044c006099454030224203480312104400b01d6465500b0a294172080031469032040500750311844441c5054a007203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 289677095 1250 289675845 289675847
    0x8220503010b181e07080a0b10050f0c0c1306050a0b0c06060d050f0303010314011d1b04021e0307180501022e060b030613022104020d050a08070c15 65
    0x10f0a4840740c4192182c00d90041880c40d904c00d5200200b0003900340030300d0564241254000d00207241625660710f4079007450210780c46d501e40b0002e0782d030034214070343c42d014540190f03440b580c40b407a0402e40222815001b204d5820707501d40c841c01d41c1c1105007132440074006920b13410f0408202101206402c0001c046100b4040d4030066900081d44981120040300c81a40c840164640b0720700d490444511030800d400003000000401c004162005c0c50082e2002c000d002c1d0303042c2c00c080304480016511130340034158048609605581d010400550703210001400162422546030f110045c880880c0900c402c204100008221307100c1da0114401910700240001c0c4d2403d14a0100006c2da2040384800c854000d00020841e46500b0b1500708018010a0034200140a1940c0d2100400d440b41c0048583c240103c4280420709003910b02803084448205c118141e113404006010800c000c0f079032005100301c0c0c20071390f442425400300e5001c2002c401810702c180070a035075030700c203614085804081a50001d0201d0010042082c42e1b5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 289678345 1250 289677095 289677109
    0x7090204050a14060d020a0309110d0201021005070201231509040c0b090103020d181106040e0c07020d050604060b1c0503030f0408160b011a0c250308220503010b 71
    0x40f031040e2207160b210b030b4200d00004c642e403103036a10300c0c001a0701c0010000c4400b6010f4122040d00350088101c070100c001e60000b0f00c18002c43e2104000c0c0182c0104000c1c00300b80003a94840c0381c03c9205071000041440850079041054060050060040320901d0b08100003007402800f295110300081d524000182026030707030035146180600404007500400309083d6000d074440d6058900c408941d01d0300780300442404a00200011854005480c102e864515105090074001c0440303049910004080d602980c401d03034403003241d80103c482240c0c026041d98110011401c108080d80c080c81c044c2c0340009195130700c0d6040080984904c440c80001852641055001c5500072040d261700440b034100a000b2640d8a00d803008041c881c10420079840343e03c3d0362004050100126019050310001031241c0003010034420701214134041c011110100d40c1c040010700020083c622a0340240c0310320781c072081e8569a101d035240d030071580020fa07824102c001000240342440d060a9280c2008207410381c0200b01e10700070080480d000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 289679595 1250 289678345 289678349
    0x316030c140c0a1e02010806010e0f1e060c07060f0f1205040c0503030d0b1206090c0d030309050717011a090a02091813030215132904060b0307090204050a 68
    0x107014082641004a0030900001560b80d621080e960408003000501006813001a10180e00103103040c0c00151095008039038150090302c005140b0801040480100101d1905803607001002c12126016090355443d40c4001c0e241f11088140500080d504100004100e250523485400400c01202860980c4d40c0e0448400700c043c5042c0b400220703040e5183c3c02d121a01102a62020303405100004608803c02e40d40d0f4801c81180100b2a20440141804105a9603e0342c09451030324543d0000784d20003036507241418800b04628824107020884002649500c1d050601c10f91005004908002c140c0704000e00c2882045140088442c601752821007200100d00b10582c014000001c07140d00103141e075465640d510306815280480c200da101c080c0b908215412107200b034410118054410302c00b822400003450300780c3c00c1c411204070a1002c1011310580b200508100175803884003a804100603510002c18204039030900c298010741d4041552004c0c601414030f09480740c2d1103d2285481404244a907584020740042 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 289680845 1250 289679595 289679627
    0x310081b06030a0e0a120201020310090e100c110102180f0402030714030604020408060910061508040f020d05011805161a130f180f060302011704110303040b0316030c 73
    0x807055442c641045c94080444800342904480c0c485561010380d05400945c03280303804c1605850250307910140d00060751181c5d9a00760694100d18032844241e520f503805448904501c1c58004051103d10300d5035401ca0b4416040700010940c9403c8441d080d04154510b2460184180c40840c95450841e80003408829080c401070302405001002c5085070ba190380550307010b04109016a2114184112181d540721201501250820b08000d400121500700300f001080000c05a01d50b411259030703da4940c4002210303108101d034400c0050f0045e03c007240d000d00c2500712400c541400f500c424040e0341821480d104074225541c2e099980381ca400c1c401c403207681200314070110300105030302d40b10581e01890000110179a00150000c09150f20005159241864900d118688072242000b44124182140c001e880c05404007901044d203c040319002e030b2281d840f0301035000d4059904000c01c1d6612000107800c550241e030085202400100601010071407180b1715910400d5141020400e8269142020703201c408417054090b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 289682095 1250 289680845 289680851
    0x106050315071b0302070824090a02100e01090f060807032a1b080f03010f0f05061c060b0a0f0e030f0606101b150507020106050a170a06020310081b06030a 68
    0x501014020890240074006031f070107481081c900703021410411040460310100490940d23000c24803103480402c0c1ca802064014000704a40300820038143c89102c62180d43c50304011441c240001c4d1b030041d02b910700d0054851a0389846c07107420300d40d600800b80c030200760704804810424400c40800c0c410b0803146030b1040450b07080030843d010307850748404852500948042c002c508000b40c0b0b414118030a0005606946e442030601c1115611503910b01840011800313496001501040300c820500c80800900c4003003100107102107182c03511212580d017980c00080d20b95003c501e100006a08013500310005070540c900660041040040d44040d00e40d650f000507104501500400b10110105489040d03581400150407040500d50f200c0745c6440b400c1200f1980003031300c081c0e26080104061a1040c02402c0894100500106042c2d00b04142002000c004013100112445a00c10141c0020b9150010310b100d800620120610245481480d0b0704000015a40940e19147e407060032140380d0b540e80a4030b412132801c3d1000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 289683345 1250 289682095 289682147
    0x90906060d1a010608010303090905010b2502030f0607090503030708030a09020109080607020601030c080d200309150408010506090c070b0a061e0305010f0e120a0e06040305010605031507 82
    0x100b8100d00c01c00d0511a140c2400c001242c0c0b1500242603074102d0703100c0d59a40c00200d80d1500004221a02030090100d06241044401366506114a21110380e02e0310ad1138004c0341348100c0c2e001074507180d034004549003181c000501304213200d030b04200410007c25007a40a103180c96100e54030a03203a80310042102c10160303500c0c2050701c25a44140c8603070002e4001e020455070b407030070405c8001e9914503003444112486020352201150f0a4404201103c0001c001d480d214001c80200e10144d0851450550300880d52006000405050ba81d03048d1481ea038584059203a82d0b2581000c000600b56074006003414019400e4200303000e0001c4e1041d00f1150040d40000034285a074031081d2500010341510b6002814019a501e4108202842c405000b41101d02c00d400801010b00840804402d403503030303030120205503084860581c09105035034008051306a000d01c1e00d00d1030901d9000000d00c02c2e41068105407800c9e9500c4800703105a04040100220304424030702e41d0005403800150060000711401941c00940c2805110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 289684595 1250 289683345 289683353
    0x307051f0b090a060302040c0f080f0604110f03011e12080c1501030501020c01150501020717030d05070f030e01090b0c0d0b04050726010e04081309020a050702030c090906060d 77
    0x800c4a40070080c1406414180040b20704064145030100b80d1185140252044259006411074150b42d41280c6aa0040750341d207120385800038000403d2650003070341b10903180c0d088240200c0280302c1604a000241d8480d41441c0c43d10103811403054414114103a4804240f00c03030310000e0310300740400741e2041c102c03a03071059201101c82c28408101c1e040d00c06d06030f1982c0044108a0b041d0042c01021040b100200b1603070380440708000d4191514420180560881d000a1005041c40b40031886002408404c4030300d8805003914000403502c0840d200c00000e0240c02071840341c1c82d458028008003c0c00c1100900010340340d43c6a03411040000781100d00000d80020745501d03012529009202c4c45400184204524a0b04c008058060400040500c01440803004401460360220800ca410795040200c1c2c0502070b40c4540e180b550315030081c0c2c109810301e406031400088071980c900060103405d0f00d036a1074a40710800c1c0d2051515180c89070503a03910625405003000b210700d400050456000d40100d03202120440c00c0c1c18 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 289685845 1250 289684595 289684601
    0x7080609030a021c031803030506011101150b0a0e10090e010b040807090b03100c120e030304171b0d03020d0608030712030b0109090f060806070c0f030e0111010e0d020c030307051f 79
    0x441b50f142c0300c0103080b9100500d5015401184540380a8070f40549078081180c6c1103003201d0b00500c00301d4480445500c1842900a008041c1203604100d013030001031101c0c0840003030700c6000c80d0f06564001078154481031011300319003000135004000703020015080c0b505081c0c0494a80700c5038046c1d10412aa44c6186401a0703400f00302c924940305a11804015075150354000400c8e4042030007444113680c0c244a228001711000004880c070650708a6002c00c0440b41d0005102d071a584402c407220017030048a8000380c8091810b00ca03402e2424060f031401aa200d0b6540034160a86020750300c0940680c00500c240c40c0454418072511001d0b00c8140b40000c2c010301c1042c0180e036500c00a4004040b0315140000d5402c2948a69201500380c031030303140032078074203075030f503180854108803000070080040354401c0c804c8000a00a843c1d11095600c14188000341d0b04403c01010708580221941e0405540610300c0c0d0b5200940501140d450901d0641c00f031441c003025501c5c1c90396191201c0d01a03100c0b01c507a40101d9000b010060f4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 289687095 1250 289685845 289685861
    0x71703070e06160b07020a020a050d050322030515160804020603061311040f031502042403060302090702150114300a051c080112020d0302120c07080609030a021c03 72
    0x141141c0c03058140605c1c020350354100035200f03d00401446001040624152640120f0103501500461400d06082000c4a4511608660f94074a52022001000240c0180000860400c0c018419241450030500700010b9260807441e480501105005200140c6c4603402142d0f8801805c1e80c04140d445005003a9000074403070509104110300c80424041111001082c03e102164028281a50000350009403c8200d105500c0f40318081226410a081580c03005024007484903110f0400041c03d5540ea0040f41090000b00e4101005801c8415264450304258040d907004d000401c005407005004500800c501d5038903c14000e0000b8108036002c84000b5013044080380b0040b4140a03291900368030b03d415a916420240d103c00c02031441090f640d0301900c50401907040715090103a018035001c03030f5002c1c07042d00044040c2c29011070160702ca1501002030314030014039002c00000c0080c12001e140401230380c10518040e103030304c40c00d403c1040703417000b21075002540c000411840003200f018003910b80805da00030b101c09 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 289688345 1250 289687095 289687103
    0xa0c2003011b02100606091a040306020d14070f0f18080d021c02061303110c09040b0603100506100305130b010602030406081f15031e02071703070e0616 67
    0x114110b20151002d03101c4001900e00b902101c20380f101020340b00d010307142240944000150300c07900400102c81c01c248180141190440810f00d032584a440b050143d070302c400c00f100307a100e844000b032940d01d524030003c0c0c81e440b804518011541d0b0741180801010054816107140c01c000400441172a6840c00400303607401010036408072001d80806540107034594203846a50502110742500f1090039a0001ca807042c8070341c04060041400d404140d0341625040240386c107086032807088001c1c0d00310310749803054030f0343c000ca0007020720204034070708441050300c3c0c40111001c20340900d0030a8107103d4039880318500b0302019012800c002c90701d50307100342d407a103c1500704a83c050210030380000001511030300480180191160b03030361072400310f680304241101c0c2940c3c0d15560141844e030400080283d94200102085413a050345004106607202403074a04004204c03010b0f10091590000d203903402c202c0804446c8540c088000c099a00b14a01600c004c0c0844a007451128080d8400103101c6550899500305030445c180d01c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 289689595 1250 289688345 289688351
    0xf0604140c22050f090604060c0306080f0a05210909090f0d050a03060609080d03050a0e150a06050f1e030c0d0605040201021204140607080c031c110a0c200301 70
    0x140c41180c00d41c002c0203240e424841c50600801c441440150025100e5241c43c2c00928040c1c48917a02c0c000104034502c10031007003596a030700108420900380f11521340c2c0030656004200600340741c14241c0c01d140400044c02c04000c03d50302c06210812000d815a51a03410403a0018550b0341d5400c541401c00c208180d9000d224010172301c40e00043c64100b4040d000403c01540d04101491301c0e4502507070300c0220b0307008041865000350864005181700340c0104e9400b80c481d80c808501500078944607440d0a0681c52601e800c1c400541c10040a01450711030080241411548481d40160500c00701e207402e141c0c1c1094034200c59080e151001151020070903e9502d0b5400b030050300e0002200e0401100408041d1802ca006000300e0900180102481c415030b02610b6031101d010704003800d480c0401c10700354070440040703440000078000d034005003000707102400281010035409901c1c580741842c0c140440d0b039190740e03042c000c00d41840216000f03640401041c0a00d548806109800909001440324941d056100c181c2d00d982 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 289690845 1250 289689595 289689619
    0x30a020918060f04031707090510050406030e0105040809010c0602090a030b060f0d031215050a1d0a060602070b090d05010507030e010b030703050615010507080a030504140f0604140c 80
    0x40c119106841c219070390a07a4031036240c014902421031015a80a80001c890281c461304c085080c2c0034454000c07429042c40320302c8568450200f008001c800c0c1c0144041607020604000070354043c0070f01111290264001c01c0f0500e030964036249140a101d40d0b20741004102008407003000300e254120b8003442ca000b0403422030a556443c04c0f0301200c5040381c1c13403809a50309030200d6807203061007480032880d80d80c03503154417410317601c0b1420040040c807c0c1c05d40b1000c240205140022640c540c0b40520029242c41214284900141d0106113000c0741e01501c1940f00624181c4d040216607800b045c030105885800b0a01d0766650001e00c0001c81c800a04ac0000d000c40d41703040705000c01c1d241c05502c038400d011000c00c003c1c80b180c0d0b008010541c0703030b071460f1101130030300c0d0001400111030002414801c1e0002405041071350500d06e90b038a803a9010b8000c00d20400119035120107200501c2401c0d041520550541c40062451b0080c05a2094a50f400900010544035000c2c4021000050034000324bc0780c940e0103460302c56040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 289692095 1250 289690845 289690861
    0x3091207080403020103060602010917031e1306050c0f03010303121b08010f060e090a02032203030603020120030910020c030316060b04020406080c0705010605090f071101062102030a0209 82
    0x190043c44100e02080c40c2400004019006004940369142c100c8117071002d5600700000b20315240d0004060120811440d2180191450030140c100d001e04d00031203801c2028944e500c0c1080031928041c11401c0c59100c20711100d81040154000c4906403a41450103000c9440705840440241045485241301040c0c103185029102e944010001e040ba0343e8030b07a84103103a035030340c0e5020341d00001c0d138481d445d030050b06080000d2168801c507002560030100c052020000b001030304440c00d04c25640004d00701e0009498040400c190360b4000d80c42d00c25148550910307190202c0b01c550041c0c1d03a00c24512901d005032840d1203440300c2140217003c4041151000740680396602c045850890350b03249030000c200d80440c6001c50003516402c20344290f0f0261110340d111886c650b16170b1a0110714030b401c520401c07145507403203220100d00e85e22080702c070368041c0782203100410705410320460161050f045040100c000c6d0707240c000704111240b41e6403559206005024189619417180d800401c1c03c1050100000c0e40085c5c0d03900610582c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 289693345 1250 289692095 289692097
    0xb04030c0b010e13110a050406030507091b0804030c11190e0a0207080a140d09150513200102030421030f08060d030e040917131409010603020309120708 67
    0xe1840750420610707582e01ca5440c0b1000300310540c1c144c41d1010310104100001000e008144241c0740008045001240d6a200082c058403d69007040314141c006440070010040140945026001540750581d000b4231304100060410f080200080c08014034009a0014040702809904c490395010b400c105590501800c0b840e00c00c0110f20440b01182c141e000010568001c510079103140e01d610a0382c2038601030501390b044500b10b0103034069180044c0f080040640443c41441102d2303910784503800012007282c2d503400c4603041760402004000041c05055044000a6407031a581400d8000d2105544034a485400103d2030340c055604050361088020780a5440d00d2886107803904420b2081d41d644201d29480c080440d8401416600306070000c014003801c90002e80900c504042c0510b000d03200003600c0c40d035511170b150001c20484034001122000250b424081103590465130103000c0c3c0d44035072404542c1c20303004180740d00414401d007810035602001250f141c00e014400600b0b60b50002111350703200c2415060072501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 289694595 1250 289693345 289693367
    0x18020d1d06010503160b04061808031c1109240706050f090d0c03020706050a0c0503031906080d02030304020402030604060e0c1c0b060d0b0103110f040f12050d0c0201020a0b0403 78
    0x864841c0d285804545103001794140151143c0d10a0141880d107040415540020400382011101507500d0000c03c01070b10800103450806240624000c9401e40d500b445011501101d112824540c810001c2d40166200c820004490b030b03010300401400590341c80c40c0d800c00d40c020f00c00014401424881404101400e07420094044d0382280256105814000016108810040d000402507003203110100f00b03c900410240c08640c00f80e06050380524256030311380e401e40c0d004031603141001012601d0000c01d01d245204000c041c0003190008d00030311800e246c01035a47c0c00000c000a01c10b94000000136920b031a140c2005c40100482c001a01090400c0c0404802e643c020316021440c100d0020300519007203040b03000740070402002900362441d124501182e100589850749290341495100c1800c2c016008171400100b84142d500358120391920b0910032006180c4107a680b2440110b9202688100800c1000c03d0f021150708440c10911588221880103078101000d0344c1000d06039800c80e0302080181070b004080402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 289695845 1250 289694595 289694599
    0x220b040e1f090c06081902040902120702010e0307080318070b070506130b0402010c050a0b011203090f0605091c050d0f020c0d05030901200601060905030706080118020d1d060105 78
    0x5044044014408480d050715000d40250b000241c100000c500407a202a00040b0034844d181c0c2c406141d081c0300302a0307230003540148180c40e800a903120542224400c916008115031000748a0030035802140f81c0d80380103602c4c0c043e255880000100c0c8131030b002c05c4044000098801c007940c80c0d0640c0d4075a4060540c110100030f545501840780021a00856a18800c14450f8841d02580351920351b9001180c807c1d1840740c048440d8400c050000c8040b411303030f550381d600a10410801550814137132900901d0103c0d0349d8009000d160000b00280101c03904101990b043e01c10603615503000a603840c228030007042c08000060090b0159000e071030f00300d0b584824074017620481c50b02215036034101101800340030788110b0740241183d002031040301e40e2980300d448040b0f400f13501e228140d94911084a56030b424608203a00842c007040340c00d40100060f0a05014800003002e190030b100c0501d61426801c0c40002c2d0f0680e45056034560300107000c00d200b81855101c0b02c030801d52041c0f4071b0507505814518a64521003809458 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 289697095 1250 289695845 289695883
    0x1b09010e040c0f2616170a1506090806070804030207030606030501061a03060a0303050d141302030105090f060c0706060306021219020406050f0304021c0602041a09220b040e 76
    0x204195404904014403c500b0103d031000c556910050b000e1800012080c5c20108100000381039490104854560b003c0c2c100c0d20f0001918958015003006081802c2d8081c00070b00110520410213400701007102903001c803003414101c0d999a1145000c03800c000316038000401041c44c261000c000d12030154894016600b414405002d141d4042241400b0307070100300d5001380c6c04480c0c50800c4c00028827803005440d141640c50790104210844d6600300070b005000700c4208034038a504480d0303003080d8a400d010301600040342e000546182400104515114038008000030801503000411808002460340410002d64001c882103407183c50403c0c01030450403094440500d0030314040442030001c0124070854044816a0f12a1850100c03080002100d03504002d00c181d81c0072030f01c4c0030300708421411000010f481074410880160b8035801d00240096118045884c04414802802001c03a1902d0300802541000c10b1640028001c00060000700051325900004079007043c1041c0a000b840400021200ca54607030004a40d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 289698345 1250 289697095 289697117
    0x1803090d052103090709060b09010f0e0a090f1d1203070207180e01060b0406020307060506040b03030a02030a020f06010e07050309011b0504050f0d170c070b16020f01081b09010e040c0f 81
    0x4209440c4180112450b00000b00418039513076010b000345443c3c14026040c03d5101c0d000754000550070544580c4041c11063f1100c224882c503004030310503078502c03605c0a0340303000004200c140669030b59403507405540200007001000c24041e500802c140002010141030456855001490800c050000580c070742002e50300703001c800320b6003889150682d0700365001e550095082850986640010b0803004d80300c41d401c207a5580326414261030900c000d091000c43c68000f180d03030301444100245844100001680c15401041c018030110a019401540140c614500143c613034490390400c0d801840c8000155914011044603403104c80d4201014108541e4200c40322071055640f08244800410440340c018400310b5044240041d0903140b9000c1d201240f402003c45558a441c3e0024100560040e4804102200180070a504520b440d038200d040022007880d04a12078102481e80403510b640070b50080302e081c40003085014035640704181b50004e00305c0041c0305004019242002078400b003034044800002810300004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 289699595 1250 289698345 289698359
    0x60806061f030b040b06070302010204180207030806010c05010209030a05071d010b030a09030c0c0303080103120e09041115040b0a020610081b04020714070e1803090d0521030907 78
    0x4080e4010031240c81d5186180548030704070010f0422210b000d90180d5191501c0e10705465540181c0801c5101c0e400040c2d580b07041226100c1090040c0119030f8919004028400000c0c0d400740105800440a0800382c100150b40d150031030180c082c0d404a2a018800d50700034000b803041c000350540456074076581595183c80360303048108007a68240180b084000040010620803040380d0321841040b03000345040781c402030081e52481750740203090344250005147d490042c4140010b410201c4070381c452604040f03151105100c042100424000d00103840b00d0480e9001c074034552607904042070806c02000403243d45a44444170403042c1c0e00840002c1005204281c005002220140400d00030345140d2402860090100f02102d2000c0e0300b880811a001502031050000107500b43c0291402e84c2c0100029201250500c2081003103580001c0a039442241924981e4650300c0c00071040b40d012038410340304000710b00800e0505502d06818115102d15400d0034404100310282a44c01130b5015540e54008d4550306651015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 289700845 1250 289699595 289699609
    0x14030c010207031704030b0106050304031403150f0f0301090305071101211a1c03110111162306150d020a0b0d0e0706030b0405010b030c16060b1306080606 68
    0x151a40503900040c000d0000c80c4291000000d100c50102003249025120717a100b012101c020380c041004160080140802c25820030320890071400b000c01c589040d850941c0d0b07400e10b102c401a00e81d600403400c40690000e90b0301c2e103542080302840064002d000410b0113141c000c2980d4081c4406465980103002100b2083d88900284450000414000c803100c1c09103000107401443c03003070850305241c0807030501c001441c0c580404405050350b42c012001441e1045040180080b0340c6d44103100c846902d01000740720b00c05102c000b0b50360104e030003203051035015416141245c41200078006000c800c0340b2800d2040020b40000504511031411340c40c80070000e480700b9003403211180300c1c400d001350702c80701e20102400340003003100c0540014101203c3c081255070301e440c50641022003940010300020344403801802182054090a401014840707059491803a103000700c00d84030b000d404401202c010b50803080c04213000341da1704404040d0390300a140200158071078442c0b000908003440740d081c6c1405100e00049803450844 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 289702095 1250 289700845 289700863
    0x15051801030309030201050f090405040f050d090503030a18050a03081308010b06030f150904050321040203150606040e0903030a180308010e0702100905070f0b0a020a0803061305101403 81
    0x62a030a5030f044c155030064806400940c0c4420746c800062080403159985c9010322030007140100103000b0100710030b00340305040020b03c0b00070400b0b0045000f000c1266890000444580b4030581c6480443d62400118a84202d40c2c90b030300040d4001c143c0d01000c03041c400050000c0029500710702c0c06000e110355401c0030a099238080071341c6070781c000d0040c80060841c41e0411001c503440b09160094180704460f50700020703003000c415202a1070503840405c0545052040e88400c100303801a17070071500340c3c6181581c0005c1e502d13030140c84150140c41801d000300700c8d10385580c010760340900941100b010451611000700340ea02d0304212808070f106800c0c141c4500c8c1140da40c2d000102d0050b01a07407040401c2e07082103206c07000400050035440452190720840c0503030900c0391243d44901d0780715101a1845919101c2090007910840e0000310340c4540c20440146800d0f0006005030300700764400f495075225070b9054001000076000da000c58045d80c1c188020080003c00001d0203100f919901d110f030b0200c5582c0d95080c1941d414140d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 289703345 1250 289702095 289702097
    0x324010c0f030323070305060a080c0f04020723010b0901140607060504111915020607020a0b06010e040f0c080c03100308090609060703092912060112150518010303 72
    0x40c1c4020000ca44640c010301940030b05007941801e0703008844c01d2040440fa089500c000001c1c1d03100e040c05a140f0300110403000805011001f00101c1404400184c200c203031481e41e1900c984e900203001c50400108100400c1e140203000b00a44d204502050b8072030103003001c98952842904010008034145d00018401c0362000c0e4003409107400c10b2015540c0c180100b001810544142d140c0340003140f2070750348090011a0030b1994491140250b85099a00707800d010208202e201950001c07010010000e07070014503580100d80000c045a1146c80e4900140e82618150f81d40e55001814400705060f40b49144e081140280104d5640b8803c9540700c4000c0e00142c00203880104440d03007102d000b04082992500a04641440100b84625080c840400242617900141d021004038a4600b4104002a405000b200c00a2024882d080340018150000485440785501e030480a20750800840d03a180d11840e010540d160301450104030003449010000c9030480c20f031048620421141890001c26034101c1d182604071307941 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 289704595 1250 289703345 289703363
    0x6050403061b0c06090309051306140402030c030402060d0e070905040b160504050d0501060e0a050105090702150a18150e0c0411070809011e08180a020d020f030703080324010c 77
    0x484e03841d20040c10250501780d0401c94220008109603680c44c1d101c400c4000344040000b400b528001603e0313503100320404000d114a00c10310801c04004403043c100c2c2c1e4440d034100c880e0750b03a801100b0030031002481150505c0d40103200d5a580840c20040c01d40c003d901890003840354940325542c10600300070320401c81056400080341408100700c1800d0564500c0603d0b8412000498020307205c1e800d010f4806012581c03485c41d140c4800c0104010b08042200359007107000b0b80b010303048408410070b10036003c8102800d03203411907503640c45102c2004c00301d1003203100f525805960788040341010405580a0038400340c60301040d0007070400842c20303881e051107141e0340c4001c4481400d040140c03c1e110078140e5000300b038040c0c3c103002140b000ea0742d00303000032141007002c2600c6407610440e600340f980080705010011408030600f42e014003080005661482403001074a43d0445002c05000360403000700e0b050104990008211b41000310500070481c41800381264001a80f6034a201c0099460004641d040020000984040c207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 289705845 1250 289704595 289704617
    0x901151418090f0610030309080607050301030f140313080105010f05150313050a050d08010b160b04020102100e0f060610120506151218061e090705030706050403061b 73
    0x907040340c0580c1c4102442d003511002c440c10400c69007000000ca804401016042030180101600140080041c091a800400c1546000c04019215200c10300000c0e041d410440680380801c2400300114044002407416651100e101c100c10b200d006040d401004503035401c103400407403841c111007885021218001c281c5d018070105001800f43c29400075040c5d122040b8007421a0011501c03c000480115205c0e80083c01e41e0620341ca0700620898043e00030710141001040050072000030004104d401c550003000707a0710306485500c0182d281000e821002136145082c00d820404000021a40070740b4102703200185c4541c0c3da202e0040104807054046040c0c0403130310514000600050580c48070b07601c06006030412a29850301c4c0106d0301c150b04506401400f8141b040c0c03c00681080d00080700603d1041c450041c001400c00d03e40420410010a01d1510748100440c001418100c2c20806480142400f030103130790a19445400040040d8400d00090320070360b052022120010301500104030118020fa45c607004104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 289707095 1250 289705845 289705879
    0x30a0203070807050a08030103030f090e0c09040506210a0302011b0206040f0326061309120c0309050d1110110a320c011205090604060e03040e09011514 67
    0x5000750005507131502c1030314030850000e03001c140118061402500d8101000c0d0b40340764001d0000f40300c0e400841c5000b090000b0b000300c1154020a82e91144011603000c940b5039500408100f801e540402d840011a0780e90700026070520010482050850180d402442880840031140b4000c02c8548058801030b484100042e001c506007011483c1400e2091a105140e02d500e11103030303000307041050120f1015106000911000303162800200c00d604034190301c1800520a2a120490f92110806904040c00701170041007041612603101e00001d042d000300310001039a12400c0c64029000451140d03405080c203440140c61035402040e01844e038004441c001d0007480b4242d030b0342c00b42c8001100b0f44588900c80d000c00c402d0304c0030710101c82424207102c07420080241d44403500c00140b404020728600303000340d8900821300c441e030704010404650158115002040d12400900301a00c0d61140c1e030706c2807002e00309c02c07814070110607410341100d00c0d8102010030003c0000c0c3c42d4000d603410030314030b001c01c1a0f00c1040da486100c465 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 289708345 1250 289707095 289707097
    0xf0b0f0904140303070207092712031107050127080a050901120c08040506011a030604090807050d020303010e060913112d03060c04050901060309080f160c0602030a02030708 76
    0x2a1041d01c5814400c03640c010b250303195400a0b10044056048020140209425407050b100030310030040d11b16036811410041003c01c820f4455001e003214a001c0c0c440003005000750440388c2d00d010720303200180c1e0300c5116052160003440702440002003d000400c19801c1c04911030341c210720441c4c025040d00c2c80d007035883d0026640ba0340901402410300c0003465000100b00e1003032052424480198455000500d41860601e0078860143c10540509402c80412120a40c418040da071340603409480010301001182042c03540f9000d485001803680c480c500c24000a5640030000e14100e03154001c0c003851580301c410400c00c1c1e00404485040c100400d0051810108a400c40b0f00022144081d0454052509000c4c403240190f14004080040000c030300030710710a90604100c002d5001d034218000c6810b09050000040081e18180304081c2056140c8548074144500c4600301e90340d10b850200210750743c0c0200040100c0441d800a029100e6440301d54001034074500100441d195000183d0113036251480691701c04a807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 289709595 1250 289708345 289708351
    0xb010e130504150908130b0c0a0212031201270c050708090118080c150c060402010f0306080d030507110d0503131103060903030f010f060912080c0d030f0f0b0f09 71
    0x1e4060324a010f421940400c1c8501070f40280100780e03072a0b94044901c01d100d041c00345940301080343d280801c42800304000108141e460185c2c1100c40c0c42840e01031589052840c0980182101815030b60300000403203d0f0381c6140d00400043c91104001040b8941c110101255400c2a000c40071900405c213803400541000c0c01040c0100c014108850034281c8600c50461b040c0245e08480450b6200405001403403800941001150b034040e4003840c609090402c80d1602c1c0e01d40540024180300c0c0010440f142035020740c00200140c5008811918200e5213854028040d103070a0f10003c01013905206c0401c14408080361014604181307881c0d140c0307103071240c4d104400750700d01542081e00c408a10b014440351a9405010032409000407100441e12410f2140d441e282c03403517040e4820f192119003c40b00300b101e250444200c4007254030850444145560605269541d4850407020b0304080c001e5045d20030038a40c1640c8141c0c5084045401000000c4215003001b0480b015078085c10b81c807045e9188188880c0c6800b1010ba58 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 289710845 1250 289709595 289709603
    0x4080a12021f1e050c0a0e0607080d0506090106020303041208060f030a1a1609061d12060108060a0b0d110f1503010311011d01080711070303020703060b010e130504 72
    0x210b900680940c549107a4880b0306655000c2d00c0300c20310000101c01c102c0f484040710080000304040c2c206404902c201303105080041060010307000910015540d16000c1d20b24064001c126a551034481d81e00540003010304942d2184105404e4001003000341c0300005480c4519130204185261508040d0182c0f0388a00c000c16065001c410010a6051514140014244103100c0c29824161420215200340b81d907000900c6c4000715544148407400c05940661648115240e50501e229814a00036032205030741921410107400845410b003448842e900040e10030704844418040c1c5441d9111520454259416400941c0e4030903014105600410701031340b5828032080b001081c0d441c210504201180304403103230078090031029101200420a1042c2950000c0e442403092070030203130751100c20050301d4200018142c42740c10812078400052003240517102c0200710039aa1803c48400c90343c2d070f1034000d40e1202d950104641d0107040c40042070b000d500400710b280c00c1c0b01008004510003140b082c0400300a080040007070b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 289712095 1250 289710845 289710853
    0x406060e0904021908030403240902031203130c06050307080601020c01140d20070309050a1a07020301092102150408070b0703020f070c030b0601020604020916030209100504050307060504080a1202 86
    0x17a2424040000308029485109030103070301d80220314100414a1803504031740c1001c0c00c009a1500580c0c000c60041c4d00c45401181a980741d0f2100d980901128050600043c0f425000c0d580100754250440c0180d44145c201c0c5e81d40200740e90f90782004a07196248501183d010444410105000e100c2c864060600041d010000250b2020f0f0008109106800a0041024140e001807000140740c2e001303c240c1c01034041a039103c03580030315022a03010b40007200d81103c800355401081200c210f54080d0010000c0b650000f03101c0c0d0020801211480703031042c0701030040025124072071011480070031001401d4800c5400407022818100162030700c515000c0300901c60400c042e0700b0071101c081319082c0c6000d00625401142c04030b042e00d0642c45c110860040c040c08030341c15036010104000050342e0b421100703544a60712a84074603001074003541c207a01901034400c14a9125044d5200b0101d0582d000c1c020700210f6070f08508480c085c9664220544840c825800307960b105402000b50a408a60300c0c0a07411b607000900d00c111 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 289713345 1250 289712095 289712099
    0x1008100209030f070312080903070302100b030a021005090f040b09060402090d1a07120b0d0602090d080414150f09010f171008010c0e0315040303060314010b0406060e09040219 77
    0x3d1308040302500115141143c1540850580382e0145072594011a01d20003186040103545010b541c941030071800040840c1c0304c54071880651070500140540d1a0302a01c048640a040c500151403030b000004002e024203440d80445129140c00c0c0201e0303003d404068038021181e21001d00f07200c0a507001c4100c5941101c0800004400a05c5c21400c1c041d89030701a101c880858200580d0040841005104c18103505003424051851581c0b17103001096000d030304c03900044c0d0700c030460b0000c100141000303c806002e1800205000480403e4034441e80d001040480d0b9030341c134501404903580c0103030044801c80300034103100f4084800e055018680c40c644201a07401d040324691508219000c030340404640c52a450031764003004000310007090080405503141030600031070001c1c403207000c40d80d25441480384109104240010405040c0a0392007080515085000b0f844010b032150041c9000c0c4c680c1034002c038084c40c6844800540c40d4403a02d000c0300b1802c0002e002e1000ca40b104c1e020091141c8400c506100c10b03100081c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 289714595 1250 289713345 289713373
    0x201030902060711010807080f070c0204111b010b09040f1103070e0114040515061c0b12030a080105010804240b060d0b0a1e03030f14070308090105100810020903 71
    0x1810f4101d01c41c4540160750700040c0001088000c0152200f0244040f030410700188020480c8050351001c0b0901d80203007541c2060000a02506070750740e400380035007400115680c0c40a10a45030890988507800240302c4401030000f8040304843c2140d024213109000811900090744010402e29400002822585083c1e2181c44280c2d100c103081c1d11403686085940e800060504244c0500d0340c1c41100c2e0400c20091000c0080462628443c0c12a0301c499898441160315401318194040009020007514038000e030740f800091903540c0e03441400c00f40040784d0141d0000449601c0398107031900c41d980c07141925040b0f1625401d0354000040407031000c900c3c01c3c0c44082c1c010039512100054402c5a00314040410001c2c400014042a444d150300308a030744540c00110501001c100410000880c3c0c2d2615002401c088804000c495004070711401007440000081c0140078141c1c04285c2074003d054041c0200104c0d100c042844c103100180b44101d1100344c220403118000340413241d01030100c03400054192612a01301c805 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 289715845 1250 289714595 289714597
    0xd0521070503070816080c090d06050709031412040506070f1209170318090402010219080409050105120d03020c01060302090c030417070b01122102060612190f020103090206 76
    0x1403454006240441000501e56000c1c80054102e007030814200e0f000060300320300400441c0010120440d0040000f0b80280c80e4588440046469402403020411800e000340300814002c258441640e813488800038081603c80003042c0b20203219081002d0a107012300e8101031103481c2d04000340070f80d400410400e900000c20b10905800000303210303076564540c0450034411103110b6400340001d001e445503c148180040c0c2d01d80c40c00151a080c8044410301e900e995507100407450584400744c800c40020034110807400b00941540034200f691000c2c0824051a138803a07003401140418600741d100c45034800076108074424002e40c000c2980341480310000c00c07559240e801103500c8d9601500d502d074100ca4000100000e00c03404a01021034800c80078006464036445403141062442d040c0170b080c2c2e00d00054580c010400075a402106208050902070190707101404070080e4880b14100c0f440c034005c0000d854109070205002c0344522507290b0a103814500200c2c5501e07210b18008089070201e050546d180311030400343e44d81d10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 289717095 1250 289715845 289715851
    0x1141302040b0a031d0d0219140d030b01080f040b0708040c1203051b010b06040902090102150406021914120a02160807060c03050c0301030b043206180d0521 69
    0x510049205002869001900c5c02040403030000741d080840610040d0354041503081c2900e45030301c0c0950221400f401c040000558580560720035204100010350b0850705508041003e6100f40c0300c1e020103070f640c09015017100c041120000c2062020000145c681409109a1500075003d845c034200c020b0740311015403c00680d2640150b01190011a0030490301c01d0b440c00d00c0350072030b0542c0000d20141000002081e050300030703401400c0000d82c010030304040c207900c00c202001c3d61440140101c40c503403c0c503040c03480007035100441040340050b02a0251400c64080c01000100c8000302d0042860f040110542809589000e400003035072940030840c1003a0680c130741c81354940c0c06008400c1c0782e0380c07194140341040071100c5080c02d0b201414100b4080101d106d9190741501e04403904219144255907070b81c0f07002898555084c20049a441200d0300c15854154010481c00d040301c1d1090441c4c00a8403880c44021108a840d40307524a142d110026501c06c0b2807082e0003074810002d1449a0300d00c10100740d40700e058808030403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 289718345 1250 289717095 289717097
    0x3022e020a06051f06050c0a06020711180603060c09010c0c0602062a1902010b0a0b030106031109030703110111150609070e1f0c0c0b030a0506060301141302040b0a 72
    0x7000c084000d10810780710700380c1c0055403046602c00e80c510018203241c0006203485048180440804c088481c0b01051103602040f41c1d12030300840d510b071258540000c240b003070000e8590084d012109100840c0c10600460b0b4040d0320010001e11040c4da8411500d040d990100030b0300390400c940d5425840004482c0400e00e8080c1149030003902c01446c2148a0a18002100380d0f4542c032900c0800542c1d003000082002c880c0d0303100080000307000c5001108001c2e805492070010f02a08040e0304c040016000740400050340c143c030030f07681e024050103900480300c00c128040c000742160b141c0c1060301c0c02c1001910141200100d480c060402c0c0b400c080a0040443c00c0101d017100000300d00e9510b03000c00180b4900300c00210b074080118102115200360803404240c4041c0c42c6911a0a2840e8080750001c400e4003680301e00d2015540862103203507868440c404048550006d440c000b2016080a0103d4064600034090302d042e20780c0d1282c1d03001911020fa0402c01c100b485011110f4915500b0800400c94214400007403454902e1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 289719595 1250 289718345 289718353
    0x60b03010b030610091d0a0e0a050a150605090f060111030d050103021c0b0a0c020313060521310209010801090b06030106060e04091b060903290103022e02 68
    0x4a84188038640061580b03950402a0051060100d001d40050003501d80040e07401d821b0f115507800300e80100405007141034000600c2841208010048001090015244510116045846401100e100340c0e1142c0c001c41342d100074544c00040c0c15010320148e00354040c0c8145080300350034a817050300c43d0855000900e5198070544800040c815402c152480000d80070070900303151102203203519941d0042c50701503c0384031410703140e00389254040d1007041a01d0030403c281240d880b465076525406041d03a408030040c4400d0035032412540070340340980760b03680784101e00584070750320310420324111500c1010350880300408090410b1906c40240c2c84000c4000c0c040c0540c1c0000284860b424240081c4d842030003403000f4882e81c1440341c05d02000c3c0d804040189810000da0307012880440b01d03e8501101404003880c4030000c0900e18000607095070003441c440c1140c2c001c0e00390a1100c164000c0103901d182a450704100030640581c01040141005400d03800030740c400c4541c04403904022006401600c400c40480c500580c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 289720845 1250 289719595 289719601
    0xd0605100317070201080403030509120d06080f060c04030f0c240219030906141605011401092f0706050f01060e010306080c10050409061e090207030c060b0301060b03010b03 76
    0x190100c0901d19515030b054843e0410885500080008100600c02800c00da21035001c01c4901c0000c100c0741c2807401a800c03400340c44115903001a8020043c9100703401c924030413015106015580030a4450055a1102d04145410305584801c522040f00758022900d84881c2c070ba000440d212901c2c8194000c1071040b45684a100c0c0d0a10300078a001e8040003c90109147c8106010000703400c444c00004580f144e0800900ba041652401d004600900f55120711000c80c44031f0403c200315042d03008080340000e4009400c540d9803107c0c021011100749040c030403411030fa03001c41d40181c5ca0b0226070000010300d0245507989003504540d03c0e135068403010754010700c000075a030b00148007464001010b5604040300307107030820425183c83c035520f0b40c1d89020049940940070007030328161540c1c030500c2144d01600000398140308030f1f90340700320481c2c1e030740c000000b80519100858000305588405000322003c5a80541d18aa0000581e8907202e0003050a400540c1d450b6503150380000e0104040c2e4040c500809040c807045031285 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 289722095 1250 289720845 289720853
    0x408010c0f020309010914010c05030c010606020610030b0f0c04120606032a090209031203090a03090902181201020c070f1806031e02040f06080f010c020c010207030206090d06051003 80
    0x701040c0540096402c140300440c03540c2d80c0640e02e1002c40e58201440c980c0d035039080c401601e80c40f4441c84007401034080011010709550b415000801103400b1750342100c0e0320780d652a2140718110be550100900d80745800000c034007100310b1220010f4100382c1141550780f81941d079518010131298610400c5501c04d8988100b042805031015400315a050000401d07889100d0521003042980402d0080010059000c00e81d501c181d101004203040c0c00c41c8a25009989081880301259a0785c0c84000440c00100b0201740032444c07013a03a0003585c440101e4070074030203100341c86001080900071300351035002920366082c003640354008000c01c0544000d00502c028011014140310280080a11000511020508110080000840d40c01d416449600ba140607100300c40d1a6100040c0035180c282c00d84d00805080540200f030614020610701030801c03064008000b0507204000c04d03a21041d102480c58056000b01c4020000350400320001d111000380107081c010b055810740d60304811204280c65142c000c0c803004400784100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 289723345 1250 289722095 289722107
    0x50f010b010503010b0406031107020d08040e070c0b070c0f0203060a0c1d06090d06020c0706030605010e0307060f270803070311120a050c030d0e03180f0a0501050a020f01020408010c 80
    0x400a00c2c16500d50341c1000e156035604c0c4290f00c00c01c4101552540c4a02c00300710f80c0da041d00d03001c55004141c0e2005104c1030a012400d07821601540400407021000f180d00e82e40242d407940c0610380e021070645120740d141d07c0c05840a1440c5d25040d40c1150900d520540142d5062003440d00c500d128076000078040f96200d1004003800035000c2c0d81d1180701c0c60844020510707617070a0252510031104030380f01019010301d49802c2c0068007442e8000b0794580300700c14012507a260513410503030681c0d2003030307884c3c0d0030812034001010364522242c82a0030106002c0290600054800c0c80821944c03600e015400d04105007030200040b4440783e41d0b200000e180c0001c5130400805a00c440b54610304480300d0020082d45c0c44420140120307114583c80c110500000003054a1030751014400e13900c1c080f590a008220012003117210580b25480745038401d1904108a00c446a01d183c4603000001425010308610f0070700b0700b440d0054a550740020b03140800c2d4461042c0b000036496003400280041c0040b034001090116041501a02c0c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 289724595 1250 289723345 289723361
    0x306050f1e240307080c1804020d09050a06090b0c0c03030601180306140a0e011512050c120f2407140d141006030605010206070e041503050f01 63
    0xc2465100004142640c0d0021104420745440c14580350707405948002a030810202c29001c46404010341404141e20090000355114201c6512a05200e68403911050018030514440f11420810f41360f0800b1503060076070280034001d404050002c0c403141e583e141e0501c0c0181221045900c00c0e111b8103003004100507014104c0d08440041f074101c0c02c0c050a151410f03240d0000038800c2d41000032072403040d2144a8441c00c054001c40d00300908008065000314034501c016000c0740c504140c9402c2100c1030721134140502c5261a60b01c1540c0b1071041450038023012010704604000c0079034061090304088010b5556038154000c00d042030400a105111840c0b00c15424081480345110222500c858415004035802c0b00c902c0c0d0181007460810501000415240e1f11b07401200c0e001c2c2030641c60710401c030800d1041100300d00e0040c01301d130552254095503000110296072a80c02060f0058204101140e4124040c00040072015401040400c502c0d200bc103084040104503401540d441e800402002810700c070030320034665 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 289725845 1250 289724595 289724599
    0x61505030405100902010903080c0d020c010e0f010804152f031006050a11070b07020103060e0601090e100b1c0c0305060f010507060b04060f081c20030d0f02030106030605 75
    0x400c40c90180c03a00c0340c0311000d4065024840303840705103800840e88075144820145900c41080ca49440c0481325040d0b9911490814202604c01c1946001c003648c042e010003c2c16090040c00603080681c0000111074144015200300c68041c010100309420007060b005508000c900e40e24590b0596a1064203020a801c03540b6440701c0706401041030005000c204501241658420300300750b80d607891040d074100d4524800c0302c1a03108078010020049062141e50b0000d01096001360713410701c2825162000c82c61407002c203803410f60101d03a00000410001e0a141c46166016451080c1e005030b40307035a04008815a4011042e041c0120352640f01c1c00e244440a20a544242e8070514040009103000c001046200e00401c60481c10300401140c03120030066150005c0c414990058402d00c2410b0b0340b4142c51841c950280200ca038240030303030b05a10700c0320f0381140441d8404141c25030f5500700800c1c0885c0910856011100c8240407070200700300d40c401c62901c030b014181c008400b121005903030f507161000c001c00f111010b80081d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 289727095 1250 289725845 289725847
    0xc021903020306060622080c03070911040e0403050708040f0f090b03150a090218090106081204150903021009051c030e091e0f0a0b0607020d030c110d06061505 70
    0x21001d0b071000079030503a2111050b1105503a176201d0f00034000c00c030007540c0190840c20740d0000c40403d05c1400802d50101911080d012501d5203501c80d45007100352103600103840002c50041c4020840c400804100c690014040e04100f071505040d0f8035440240d034816040040c2c480e43e1120208112401c07900550010003030440108a00d110030b600207910350540b0403200702c02e41a154042002d00310715502c080b19135a0300401c81d0b80c0c2d800c0111045000c1c1d407402c8924410b694038080300020480000f103a90410000c00c60301d101c4ca07060501d4050050a600700200c1e40401c42d02c0b0401000580f2035034896038011030b40707455004c403691400c0c04100011007400f00304524400c900641100207074009030441b209503002c40da4500035980d00e0310701043c000709550040660401d040b06108401040043c0c01d8004c041c0d4910034020400143c040c0103540c0314002c0c0094009003480001004070f80302d14441d071b41c2540300340303052200700803441d00184500500f4941529441e13070b2040304018500801005000a0301c0f903040c52 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 289728345 1250 289727095 289727099
    0x1080d44070e040903050703030b0f03010c0c020301180b130f0602040b030405010b06131412151503010c090b0c0705030706050c0f010b0f1c0807032f100c020102070609030c0219 78
    0xa1103070281f600020b0915440d1941455103039641c3c2941c0c1850600135000b08130ba1440302400412030200071409074000d51034400d40c1888041d01041c0780348007681041c1e40c0c882c0d90700d03500520101c4070244002070f6203103800c0551402c005042400244020005083c0e45a10303400d25040403421114070b0b0141c1489910100008103000c0c1000460f48221007440300c02988007001c440110701d9881c0d0501d14a4024025850301c0020384002c0c2e0141030090000b0322070200340714644018182210402608040404c040700010400c44100000812a000c02d03602641e050540c0c034008681342501d15009040882c9000c2111188218100300802c0c03991480002400000506e0b00401c0c2e910040b00f01c450301603400c40ca111020034445c0035100300c041e60700080e0b00f070341d4a00b2070a00134058a00b114a036607806d80340301c070890702040d102d0340080c0c8540410b101130021400250b002d04010400d00100109554083c0400004241148180e00c0160300944039030003103009620400001144407010754075070020078201 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 289729595 1250 289728345 289728347
    0x7032111120901020c030f0a0c1a09040e01020d0608030408150c0d0e0f0d0503060406080a05060708090a02060d0e150c0406080402010e0607050a02030601080d44070e040903 76
    0x14900d4200181c182280d0301c0034a500101e0070007428444c42034040c4100381e190300c0c00c000300017620820a03001d10411028541c890004122080075400550209901441300390058501a03000900c0c0d007003054001441c1038802d18110058541650140ca840e82004c2020045141c3c240004040d012841131064a07510f4103c013102d405001c0e130707003040250035500d110040d18420100143c26035a0054011941d01e40c502040091807517000b1a0400e006902300200002c031003900040030b91751254410003400c200d0313a408a0849a840c40141400540d100300b286402c09611250300401c3e155040c04004a000d40c101c55415103411018035092400d0088002007200c4007000e20162800d440c060b15100000fa00c1d2400100c4103c407181ca4840c2d403111001074020b040142c000707941200ca9100b5000c3c1c921076130707075000c003141c54a1482400402041d00f15080042d0074281a0805081214012040294801c1140075603a0322440c100d0007101e2810040030312902942068a04e085020125001e1002540c00c0c0c0d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 289730845 1250 289729595 289729603
    0x2070e0601030b0a0b0904060e010b041d010b18030313060512060a0602030f03100b0c010b040c020102033606070815060304020d120e030d05070309050d0b070f020a0507032111 77
    0xc40c0d80303050080030486d001d25907543d40181c0010b2040303c5200540356100d004025040d44948690403080f5004000c0040300011464814102c030324018105090011510031240000c2c104e443c81d940c03600080040542c1c2e803400c0c0e03241d03402811981c4c0d100d0f40c650246264145140b10701a007082d00c0303081d41010401800f5400001c031201544000c49054a070b8550421200b04240d15400100200c3d802068118140300e055104d00c1c0b10010481c2d05020448914105034200c0c40f094903a51745a6080c0f100f07882d6140d08503042d01104421620b03410075030701c16000099060450030303100d0f00b0000c3d12000c103020700203080c040707415032104049950700d245040c1a40044d5000040b10f4006105d00c02c64642031468034013525501448081c09010f65206214180d07004040c2c0e031080c0c000710085280404041035908140300400e02c0c0c680e1110034000c507602c070100251000f07100359002c6400c41c4100d02c545000980c0603c185001940b1501850a0540809492022030034611012904000c0d44082c11941004001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 289732095 1250 289730845 289730849
    0x60e0307050a030c0c080105191506140703110105040b0603071409061011070f080f06011409060607170d050105010201020a1d0d05061e09070b03010b0f09090702070e0601030b0a 78
    0x8140704c0c81e5000b003072520300800c440f00d40c4240c4940d403800081014448045880c0c0381c001c103074490200300c0041d601543c01c03600d002500410f400a0600f40900f04881c1078513000b040d5240c00ba040c017480102200303a10501b521001c41e01210301424a8041c025507003410048000a0b1400e070001003850005100802e031400c0006021a12403090f803035160450601a00c02250703146840819034070b905131607410310600c4003414454000180305029007443c500d075002c25414180c401c3c03242d8620a4150000c06c000b41c2282c042d0003164000c034100304900010b24150003920391191014030068032166596562411914140e000c1c60540e401041102203841d80030303250f50801d08500c2c484404411408021903094240d2800040c02449800c0c01d2000f0800c2c2050703401500c260307082c0070900aa1341c1490ba15110700c060700c18007404110500060000d40140d8024080c030360b400b000001c1c28003d0328000034000c0301d016508038015810203881440040082c04c9101d03030041080c202031044009100c045880c4101038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 289733345 1250 289732095 289732097
    0x10215070203031f030501050f09100c05070609030302090a1401030b310209060d0e010606020a020607060b01120f020d0f0506030703031101020d050103210305100b0703031b0c060e0307050a03 84
    0x12450312145403500480c4017030354110000700550b1a0040d01026103050907102d98420340720302a00c15000c0c0100b4001d80044200a69680c1e09001c0c8030359810340903080d080030840030304d90240107403181d81d1a00ba0307a580041c0702540140c800c0c07000c0748001508480b807018010303029000c041c01c00b400410100f0040c0359076184034102441d00200c0958400003d000326131103150300040004036005c511450340c0088148041040017008059600e0105136624500800003e410a1302404018080340c2d8a620a096100041c1404c0002072100d081c1c410480c0d80d840c0e292401162f004c00e0550a1010610510b81c40500b030070810401c030b00381030000075030381c283c94130000302042403000072004031540c02e4054800103201040c09110300d584925206c16a04480c540c0d4840d85090f00c19082c098505c28043c0c503001d942001c40c103151142c20048030143d9544400004d905168665400f00301001031104142c991b003040e6910342004500c1c0c0e207071083c15124420640c0b40158810700c991404140d011880709507443d81 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 289734595 1250 289733345 289733371
    0x1602060c0a050c011103070e09100303020c1908070b12060316140d14011b0c151844040506070222020d0c0201051308090409050111040501021507020303 67
    0x1032803c034050007091441991284012051121480e007061007040a408122445986503580282042c0140c10b0b901c409030040c0d00100c41c43c8002d081404503042c5010710081103000e1300351200000d40c90f200700c03540910b80c14480085c694655140d041d09881e00541c04078090002c240500114501e802281e000c0e1180c417540f0a400f4050581e41d151900300e2150b40314014032055514a1040b50003049400301c0b54503072458007101040214811082e1a038981e62001c0070381120785195482c8401401065000740441552007261f0003c40d8039188280c1c0300081200c0444c01041c1c0e11102c01480300440705480f03019006644020400044850964094840a49006d61201180c1c000100d009440c0710b1040004d06c20b10300c0c45d406030000303500117090381c1c02642001c0c01500d5141c00100e0894038100c400d1061070b880040d220000030741002c02400c440c00010300110701c01400342c840138211141c0c104064803407030000500300060f5170140420044c41340c081001c001123152100010f5204e01c0000c0000d440d03150 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 289735845 1250 289734595 289734607
    0x8091f02210c1c02060717010902030c04081009030905120307200a03050a020a0b041d06040e071d06040c0519021e0d17100311060c12031602060c0a05 66
    0x480c1c00203651000054008603209502c0c03a803c84000262182188030041c01204009000180140c049500202d8440c1114802e87c0c60240848025000a405280b400400b0000000c0c600c0b020042860104002c0720009480d02e000c0c940945415480c1d401035000d990001c003248000074020040d03510041e000081c0d80d01410090030310105041d030217074101d9807228140b000030082c00350011742d44006910035039450340015140c0c0108145c81c02644502d20070001700d21403010030108029002c81d00900080d0010446005520714181400c0d69500044c94410380c44640c0c5145c120f00e80c507120b03000181a5801c00c11030540441c0100984a84004049807000d50302040540c00d108010400318165510200d424036500309449546500f8a182e1360000125a8421032900900c0010a02c0c01411019482240c8501d140e03212015541d080240c40d900c00701c21b0003040010f8000380710b04189002600c1440e9035038076001c030280031141d40704100401154040c4e8200001d800b1080308580750a0003504100340c49030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 289737095 1250 289735845 289735903
    0x503120904060518150618130605060313050106301b090203190b09150a0902030106080415021306080c1b0c0301140609010302040908070f08091f02 65
    0x1000e503000a400000d80c4d56540000c1030a0301c1480e000702d03945034000c0c04402454041040e14090300d011a01d070307000c540e002820b191a0030040d24189242d090f0340461440c0e59000040c0c03082d001222500700b80700c4c02a050744100002031240602501040c000b03607000c500b400b6000b10840e00400d80e40341640048c00d4112013849500c20310f00d440900e02821190750941c8030002580a0340095809021262420108149072141400b444014030000740031720b2171680c0d44020082c072144220320030075080400305a010842c034070300d8001180a03001079140e000890620385043e40d81440c1c1c42c0307482e445030740c8180502213a0040501c1203408981c0545050011511100030b048514411241c000540050107660145032100114001c014804210020401100c5d00c4112280603001144c0003580300074400e0051006140036031004000c9400358004a0510000f80d40c1c842507070321000d6042d51a10b4000c100484a407410360340458955201c149411405180c00030040d6560040781c6610f480403440b004165050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 289738345 1250 289737095 289737101
    0xc190810020f07121b0501020d050601020a02030d1409060c010b100908060a110d0c031406031f020a05090a06050403020a0506180409050c0d03270e2d190b0306010503120904 76
    0x580781c1701d662500c0c40030035850068001d6100513102c1c0812414107000030322940c0042500b50f071494003d4041d020a06c1140011505882c03906c200520100083c4889a52900c9500c060721402e030350703500001000c0b6400350803c0505219001e6080401441400500600c80702241d0582c01c180b69110100300b0540000c980d680c10f00503c03000c1c01079079207000c9007880c085900d504209a044c098400c00005902c03032005240c0c56450413204242440c040c400441a0b02002d0781c01032542c02d45c18a061030a00c41c0038400901441c5543d4007413400200f0201c0c0c2801986803080c0050006d080484800d40340c01c41414041c500800c40400c1c0030700c500c2d6030b003051400348041408010408030004040c5c0703466158030f103001b0306001c00c00342c65034150300e1191040e103141203400c0e19000240c0d009070380100309580d1416202c4000c0e5000c09900c03001c0c0080a001c03034959100410300e150064400e094051400110046c00303904403011168810710a600007001000a030b1004a001e090040c0d0030b441c0e0703a03641e19102000c503000e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 289739595 1250 289738345 289738367
    0x603020c01020f070f0b0f0c180a0f0f06020d02190b060f03070b07060e06060a0308031008070905061c0b0712110a0206090f01090308180c190810020f0712 68
    0x143e020000d100030402031200514640e407403244040303106585035040c183e00304003030894811280250800284101042464000c3c0480800a082000194444400ca01c01141981c00840c4c921815901803250940600c01020203450320310007484183c00c0041d16485a142528010b0221450751001c5103050b12140d4003002d06c4417000d41212900c039640d1080d0309066005503010380c1c10030300c1d10040282d0003034003155844c040d1000a2043c2d0305d40d821602c40f0351842d032020340b545010070068800014948010b0018400130b14500600091074902981030200940881c0d018500c90707007040c401c5000007400540c0c0b00f6004400d9161021307011801d81c0c1210300400108148402c0030340086041505140d00080e05e42c41114560141d80e100410a5081401d0300c0e030074480100411100000a04203e0003d038500f46003841c407104681c820040072000c64000515546000400440c0740c000b4441c4420030030007515805800c1c5011460218410108901d0b8001c0800040484184840004a04e40700d00340b1864 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 289740845 1250 289739595 289739617
    0xc0a02010906060e070201060f030203070311130905010902011205040309061404080304030506010504060b07050d030f06090e0a0b0c04061b032604050105100303020c09060102011d06220c0603020c0102 88
    0x4112a241c81e40c00c11130b0300c000c450881c0158207000c400f1401d02c950492140840340e020703000305032407411691110300141075400c20300c0d00006505a90410031451380102ea010501980c0002003400d80da0000600e00c3d0901c0a5900b131036401c1c50140b01c00241c0c0320102004480c61454614544040c940000300c2d944581d6008880314417020501000b4808e020416034102c400442e01008181d95a03140307071210f80654400609030303403c0145003940c041e00ae034019100300e5004480004542d915062102e04440c0c0e034528102c0240e21580c000030800c02080030050304600700c408028201807418000074048840c40480100c1c40d00c1e40800c0b8010180181000062204210a841281d901060610801c0002103e040e1076542c281008152408149646e1006490f0103170b01070401004001c0500c40c01c450090000e074115982c60751111b01c403443c0101c951000c01d0519002d0980c40c1004200c1c40000c1c0500820480780c4031800a801700000c0414140008891803800d0140c7c0b5601c500700007600a00a00303032103807 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 289742095 1250 289740845 289740851
    0xc05040f030c14121b06040f080307030e010801050f0d060912020d030b04061406091815090109110a0c1a0403050705060f07050306040e030d11030106020615090c0a02010906 76
    0x842004007030b01d030030000d83d280d0300038040900c0c04400c10440004410a250544d80e0854410281c1e000e2507203c003801021030151405184c2a51180d00b41d0208940d9400f000181c3c1003c03030884100740e03001101c0d50001000b441d1800c402d50400000400503002c10307502030b1058400c5903880e010821241c0241120766040081009440c0004001945030b04440c2e4035600024a0b19a03022001d1600d88150801e841e0301c5020111801954828401c403a442144100e51214030b01c200c28120701c00d5010400d2040e00d402c81120708940000b01400f443e0035041e04100e03c00c1d07003041078001c5000f901206840317081060b45000860062141401146194520000304401e074110f0200404c0c55003003801070007124411022220640d803400919401c030701e0141c0710040040c3c82000450558540b0790001e80b0410740c02c0d0142c81c60b1907050034000d000c403800b5000310a49410040010400c254052280c99403107543c85000c1001320400c800040c41c0d2000042030615120000710b04001414401d612020341075501c40010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 289743345 1250 289742095 289742099
    0x150d080315010906080c0a121409031e03220c080d09031a191508030d0605040605010206090309130b0904050f161a090612010b0409050609190c05040f 66
    0x280310701450312220340030840004001803800c1c800c114181c0b05588260440d814002c034818201c40d9103401400444141c0c3c3c5a40b0007000042c0100d14031401030050314015595150b114441c070011040810b109400e0860070302c1040b42d4070340d40761018150b003000400e07400d68500642c60a103154407115006031080d482414494561a50041c102205590213003001d00c00d43d070100f80c404001400c0441d8440c0d442c1040d40755100000c45160400d02070804500b858184003519440c18a24680207070240c400a1521120100f199080912030040507140a1000d4103d51a0401c0c42560b60722030003c005024030f49800418112030b00c03035030054401440007441101d02d4141810720b43d03070326142111600e203e4040c1e45920030030740003002c1c0b00c0012188a814658070540b0303510381100d100c0d0440300c07a89400c2402000304403000c0c041461a01d0280400780000e41d2160b04120700c840841d140201500d008400b090103100340440c9020f40e5040602d4841d00208020101e004102c42e140102e9001600e05a603403900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 289744595 1250 289743345 289743361
    0xd02010506090a09050c01111e010b210307081303020d14070e091f0f02030103080c0c01020c1c0302010902031903030b0303040b03010b0a020f0d030e0606041103150d0803 75
    0x100901404080b00c01c49659210081c00c0002c0b24450b40b0001d1250f4040d42204081e540159000c0c40880740e044188c0d650850340703440321514611518040041079640b403c8200d40c600e031000350500001c1c504031102c0010300f01c6110860b40ea1240810240c10728001284903112002121a40806103034041e110069002d5075241082e000805002c0800507400b036104042000c3c0c0006480502c9407180e40010840307000400001e114031b00041e042d00400a4554508042c680c0b054002503000f58800c10752150384072000100c03542843c000d00c034006c1c1150071500740c160303155882c0034101c02800c5414401d014012401e1905078014001c00d20001c0d054010f26014403e4450412074201c0c11500949050110b8025a020035441e0301c514045c94131890402d000501000546070003400182080b401100c0e002000422004d180c124020f064600298a540e0004031145050100342d8100d031058030288014861844000300500004040501000e5814034a85e09035a6030000d2403007040d000500260390781000a1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 289745845 1250 289744595 289744601
    0x91203020d0e0a08090d0201030e1b010906020105010e04060b01020f011a030d09120b0615070f03030f0c02070e060a180614030a0507060f050d022805090901031e050d0201 75
    0x40a505000d02d4501a40d22031200400c20104103940500078030b1804407043c0820040300007260007a810580c0d984402007400703600308108061942604108a95001c041d4001009540140c02c61070840e41480010081401c2052040da04654000d0380410780711880c40c0104d150140b02d0003811350b10760a040b2042c3c40210050040b5688020a80560380c054080100a13502084d06100c2c411103410801d84c00008602e00d4584a504820010440c0c407a18a51002261282c0c00000042d04d2016282241108154061003203888010f00401c040c40300c0c0700780e214060740350884ca100341d850300544600003542a0340d0764152440a0810000c1100e0001e582c00c00c00401480180a6000d51a20740300c6484400d107030020f48004519407040c02048081e0502100700e41c0e00c400e040020090200603c04036041000d18006000c050414441561043c12108040c8007410f42030150703e41484010020b0b8100c680700c2e1400301d4150b81c1c001ca21203200e6003402854036018910320b1001b6005003e4540548104c0764190 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 289747095 1250 289745845 289745857
    0xe0402121303090501020a0b040f05010b0607051f05281509020c01150b190302040b0a08151002030a0810050a0f09051f090c111603051e061909120302 66
    0xe5110140f1a8031030006903070301c1d1710700c10000d0590f0400034000747c0095291030802480c00e00c07a4001081349100100417400c1038001c03982c01ca42070342280000a0b50020490400d000e03610081c002842907081503003020095208104c8a03610801c00c48072314005032400760308018184080131005030b4416549040f940002c1d001001601910f509012103828501d020f00c510105803900b45141900d031000c42c3c0c604950010200c0044018503800344000161440c0c10b40c041c011441543e01c1e01002c928003102070b41d00c510b0103041d0b034610406c080da40041100b81d00009403040783d60b072410140c1d101d44828141d1788074817446502050340060508004120781c10440c0c005402c42e08190b0045c0085c1c8c5694000002c2c00d06d80036803409a1035400042040705601d03d801000f655407040c00d100e401701d2020b01006042000c155a04021108140d10420404c40100b050404030510144904108070682101c01c1e11010080c0c100c00500709030b02c150503a858010350013580346913405050f03034810070086a80500a50000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 289748201 1106 289747095 289747097
    0x2040207060b03060709080d181208120705071505060609130c020c03030f0301051215040b012402060705031902030a02070b06010c030801060e0402121303 68
    0x52005059850040001080382c0c03051500b8035140c4031000d4004010010003240422841a0200303070284100c3e0a171501c1a668032081d202d000032043c1580003e0111140840300f8000c018180b401420040c59280e55509160784441d42606d207401007079000740064000ba0f521030106812507000719407128000300000d00b0140c1c17600200390038074042d000441403140e4410b078190b44039404201d1003c542e10100d00861812045e251249d01a0006200340c5001d00c4198010a0b07070070b00d0a000348032003000c204080404c5440d06081c440c0c0b40d00700c01c4c810701c0c516068514440341c440805110000404006400074001c58681410440b000e600c02440010103040b00d00381107031495003030f000550203290220710250300c0f9000d44c1085501414003034103983c12b004048494070b0010f50080d108070704551581c100941040c0748034010501902c150b0b02a02859240c2c5001c010000c152148140020b5001e = true := by decide +kernel

theorem cover : BRFrame.Cov 289568345 289748201 := by
  have h0 := BRFrame.cov_init 289568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 289568345 ≤ n) (h2 : n < 289748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
