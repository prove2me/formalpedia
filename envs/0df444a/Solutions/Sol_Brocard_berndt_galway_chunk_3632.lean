-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3632
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:13:32.635016+00:00
-- url     : https://prove2.me/submissions/d344f132-b651-43df-9515-447f58d24ed9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 653057553 ≤ n < 653237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 653058803 1250 653057553 653057579
    0x20409050a05060d1205070f0b06010206010f050319020a09020c031b1c20071211040506010801031b030b0a020703031406011e020f03221e051302160b06010306 70
    0x4044c0c1c1000c01c09010401041c620070702040521001d0400d1441e0041c1c0e81c45442c80c801e8202c40a4a20040e40320602a00303580c100710040c01015041c101c1c806050500780060303100c510035003a042d040715001400d01e09554501644034014502c2d00070842d0b4840681d070156032203030054a204000c0d5880c0108452518001241d8195204040584200c1a03001610305485c40b04d0701c81c01042e00c1c2c0d4aa02d074842c0b100c040800004014012420010381c6040b03140c40e18000c1071008403d00340c012414102446902d9801000c00f0b41540c1c0d002c00c120f420b101c460031f550724000301c441d031000d01100813444c14446000916802040d007940aa075003070121900621411100a500b030341c0c550f00084d03014004114400da10382000351402403502c15100b405002c4401c242c0b07140c02c10b0300300d04510b207159207aa4101d1502203c8080060065001e2444110070f40102000d0084461040c54069200c01405280981c1c3da036040340d07403000e10100401200c9a6600740440740180844809002c685001c00200f40c0d03055200d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 653060053 1250 653058803 653058811
    0x3050307020d0501090f051f0608070b1e0406032319020a0509032b1409010c0f1e06051e0a0b030f0f030706060b0913150b0d020409050a05 61
    0x4015403a064090782800310101c030214081c2c41c1550385041c2040000d2a83d8031290a041c0203100610a6503c110580442542070400c1280c8051408404200305817012401804443c2e02d0740c0c0d410707103845035020644121500e04010360800600041d02142d4150150f0200021104c82c4000600c10105600d203007407104070954400c444a21001c01c0a10b5603040e42c2c00422013107041e807602d54200300c80200402d1070102654014032030b080b50410981c01d80900a0304201c2d64152034503003c03032115140e070001c04541c494000d080b81000701c4150030b003061140d40c2044030089075003c01030060400307090041d460403c1c001c02d401c0b1340180c140400300c1d84011411000815807407403149481004d484004c602002042c40e2128143c06000781002004080c40c140604424100300d9405103030f41d00000d14100b0126031320f0b0342040c4030300a801e021843c1d1944801c101510156000400000c0c810b21482d11015100c1e083e40c48101c25010014034400c0c0000503802600c11101084000c1c0a5916008026400e69000315 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 653061303 1250 653060053 653060063
    0x607031b0206270a06020715060f032a080309030c0105270f0306190f140613140916051503040b070908030720032109060d0c032403 58
    0x302190301e8400c40c061014410044802e003500d01407124018138100b4002030f006480705035020900c0c0040c8400c21403521900e401c81c9400b045220b040040b403500302da5641c000540001140010741848918484034061501c4040102180306541c500060303960354072098880b070207401031150040d02035006000317541c43c01d4881601880410100b40d041d10042c41c1c005809588105428080075080d20288038990055811b280d1207440f1280d01c3c1c40351b905840c0240b41e0700b001e841c81d16415080d0000d0070002c0e40c0c1c10460888400c8500c2c044803007413001921001030410300e150100c8082c040c40000000703034000c03162403440184c660180c0d24010040c84203480b242b203000b0030a00b040002d00013201449043e50150844c1402c0c2c6110307850795241481d64000b9041102d82c9548003c559554303c070311000408240700d0481c01400c00c015085506e0521040000c1c0000501001090920859684105484d55250407136810480d40b041c03110000c01074031041c0410b48941c648940804c034190700220100707003a20317001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 653062553 1250 653061303 653061313
    0x3020c040b0402040302060f0417030c19050123011e0e01090c0507080a030b041b0c06020904110c01060e1f05130f09060c020d030905191e050607031b02 67
    0x64080c0006010310007202540315a08001c04801a41d850024240031403000c2001a2039504081c004900c0e0011441c0091069100b80006c0e80c0080b0005031070a484c070800034040840346440e15001c5d01424401080c00d041405146040e000421000c5c9543d0403038200c0d4800b02820011140b0080b04d9031f81c140180700c6d03656454801401120340030303000080501c540b413070014070300505501c03008403d030443e00b03e9900180d1140c00070b01e0145854010001d01c40d00d00e0300300c000100103855010304101e1404000800d0300740c012450001c00d540303c3e480788c066100540c900503607581489231214002c0c00341e0f02400414103003000c00306260b800341e6150382c00c400c0d0690080c00e10b102d04120030412034650080303001c00010b07150b54050840544034081c40d004c41d4400c06000c10084d801d420042d003410750000c940c50404d403504101c030002c0f030380000d46540521110444804d84c0580360400340c0b8242e486004d120b000c098034100503010408000b0f0054414070300e6907002c01c15280b8091091400c2030340b40c28404010317804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 653063803 1250 653062553 653062573
    0x8060d0b0117070308040603020c070603020a020a021219051c020a02030303040b190f1a060f12060d02040203070f0905100f030c020c1c02030c040902030307080d0905150103110901030302 82
    0x3030041c0303801e42c008100101e0300039a80e01d03501c881155005800c0900006c0d0080365030450200200015000b904d4641810342c00e003041c46070020360315048a403000c0c1c460348240800e1a080030040c4011040d03214500f410001411840c02d0180da6406008010003c8280581400c0400b40c03020070003003103070f9a0042c0178600e99180c5840704845c13440098000242c83e29030040380002d01c212441076804850b009800414080b000d004108c00f140d4900b10914044c0300c003040110b10104040b0215203222803076242c2000030380c4480c0c011036803541c015a17000750000e1000041c4214103812080315040102556180c0b1520f0740c8a00034480c2446c41c514180011601c2030120480c5d49005c1e070480c1150458030f20490b5800c40c210000620200d6110700010b500c0c0d120080d541040d4181401001c001c041c2c2a5028020740c1c8450b80440c4c1d0341e02c61041f02512003000072a02590032002504106002030300718048443c6100f9504521810003800e200489401d1100c0074070310080d04241401e0f50480350150050250200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 653065053 1250 653063803 653063819
    0x603011406070503090a0f060f02070f181803030e0613030e040c020c030a031808070b0703080c1e0a0807031401031e06020f13060c110f1512060108060d0b01 69
    0x1210300c00f2100c0340000e110840c41c607113444171000f008140c0d203400106414504503003c1c101e0700000034040115042454240030a442461800089071018081c8110346210034460000414101d046c0060a9035085500c405040e499006907003d8840fa4055414544808000a0b1071004694005021848002401c0500c2c6040d0340210290700c0580150703000d21420078000b90404071001800c4010a28507044141c0c0001030108039009049003000034110a410880309104c1405a40d400900f00000d00d000100e03c803d590095586030784010034012001802080c844103aa00070488860024200e04000788800e032190040b0001c01100e900342011507400d5403140d07142035102c0b158071081e0070000c00101c800603209100070a020400141e1303042d114540800c40d004140c000d98080700812100b880c41d00b02140e91280d8403c020001120504141340152001c26640d010f90032001404032000318036028411005803001d40300740c200342e992400d00d545203000c008904091140141c462803c000060000721 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 653066303 1250 653065053 653065057
    0x60610022a040603080d0c0905120a060c180f090f060e0402191703030901051503031804090f0501090204060603021608071e14061e06060702040b0307230603011406 72
    0x1c40041c20100b24940c0b03907140d50745598444500405030030b5550001e404503503881500700c4090306045030310074504a201c4174401e65802ca4400c2c00b80c00b40f5175404080d491035001780f05501c2c0c10040341441010340c2c1ea80b40389281150300c9500c00d10007080d08009902c0c500d84502d01c6500e0036549040e5400e200c135182c1d0b40a2014a454414450540c4514041c0103e103e441c41034400b10b80d00324503c004c50362403030607541407070a48a016010b030000ea081101404116940881038442e80d01c0480c800d201102403000002d009403101d41000b500480d110062070050103019080745502d6030003030b24140081c1d036440108604900c501005400a224072040b541c00262000d001008464000e004503040710f514101010049158800c0846001e2043c0d13516041c507200c240000c03a4070907000001c1b40b1102c201e1440c1c5c894141002400e2610900700095600b0841d03482e980403140d940006402c0f202410344810620000d400c1c03e00d800501c404003aa10790015103803a50440b03040e2a0200c42104c007602c60782007441065 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 653067553 1250 653066303 653066383
    0xd090f033c120609020310080c031c180b070f050105130201020c0d11060c07080708010b090708040515070f030b0609030307110a08010c05190825020a080c06061002 72
    0x303945410000559020745c1c0007a40c017440d2009400c0180c24601105141b6085400c9145030194005414040c82601461a8500407850500f4940c1d1071410450310b5a0140b06280c2049802523004542d84c020b0001504071004001e01c00c02c0200016150907001424804541c880280144d2141c0ea021030315040400f448a070184c484c54150408261032400900250011401d5289561024900700141901003000d4401402ea4030001c01110012074085610784000510a00501c07444001050421000300204500c1b03060110403035a8a0814190060950301744200717690010f41400da80d052280340c46822128110401002586010455501c0f6040c0921b50802c103540100c15200004030700d2030a005020240c9060303581c3c56920341000c007085808a42c0f69116504110402080010143c202e4040700d0494030711800540701d444480070100c1ca42446007900401300d1401051409182c0e83c000b903942d0003101c080360031220400700c94404a983e0100c5062541e260901000c8807075500480a00e4560b03c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 653068803 1250 653067553 653067587
    0x6020c1c02030a1b080703060b150301030f11150c070501030b0315160212040b03060301050a050105090f09011b1805040c0f05181c1104021e0d090f033c 67
    0xd00350b99070001031b06200c03c6510584845844001c0c50801d840c2c0210303103d0f0b04600c14a2894115411034a415a21403200f0b24014a1002c0781000d42082d5170702c60503400c103024949a5260741c0d03410340b45a81900e40c1e9013442070030b01003410b0000203442840d011135070280100030400e8510155071011a8455080080209401540070301c1d2205000c45042d94000e1020300804c0b8080c681c0d0f0b007000f8052500312800203000c0690340b842c2c10010b12161340e6600710582c0002e03e1240300159503c0d001d82c01401461480008018407801042c0314020b99041103281e0408080d85605002140d5180240415610703110340101c005152081d0a914450040300503212041c0020600520034442c0004990205008010404015041b025940805c031201c040240440d00c01e9500394203003207072245107542454400029008420012554049002c5140e100101c01c0740c01180f48001c04901d4100a451a202c80c014840400c1c450102040981809296a401125242c110300e00301c00c41150704446820302c1a0100007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 653070053 1250 653068803 653068853
    0x601052208060c0310050f1005072406050a0e0405062a04060801080118081c02090405040c05131a1012330b04060302031f06020c1c02030a 61
    0x1461000410500e807090f40f0000542d030703aa0601d817030a030205480a62050748504a016401c8030305850b2034001c01c00441060402c01d8503045c292405801c4000c00c480c08100101c044a10309800f502030780c00101c21900f0654000f1603003030700e42d1210031040d0300495019010713600c0080404c040d81c3c01c01001c410740310700000030750700200a801c1074608254131680c00500080d20140040c00410303c03c0c401c2050240304003407600082e00c40c1e6a1072784980c0c05485510006207510f00c1008031074042e5501103811860f0020020000d510345898650000d81c403c0c0106030290305500030104e20b0740407501c0303559560360155032450040d980b0b8008018881001e401201c2c10810071546140c07507401280030307040c00b854981d10355080d0007003049400103803c40800e850800c0e48400001c00c20041500c042107409907141494090303501d55030000c100021104800da403514100808400040a036804144440c0d1414121118030005108040c00c0c071504000d0f0300041e40c960000b00000000500095070b0349280a01d0344049a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 653071303 1250 653070053 653070059
    0xa030b0408030411010c0b01170f0115080705011103030f0a0f05040302150a0903080f1e01031101090e010b1603020f240106030501061d0103110d0b1806010522 70
    0x8400820a94080710a0301c4003006220410101c00202c00500c1c0c07007840d04500c400e60b90b44540d610002d040c0704441ca103003420154040c02502c244114031602060b20001d000400c6060700d00b0540d81e000e40f140e02c40c1d80c010202e002c140f66208196050b10140d20000460650b201c00c907a1808042c8068284104a81c2da000d030445003887c0b07406014030840c0242c02810031402140320300d100c4194006c0c5800e001034580400c100c0082e8100d0180d0b60003d049158100c401c1c6e50f80c220fa01e8410800112030b1024a0307013880000100b01b0500184841e41c4002ea81e080100b079540c40340900642030a00507504008001d00201803000b5100344c0380758010b406441154907899004000d582010b40412241210fa44042c82217103202c1c0e4116495801000a460200869032501000034800b44468000454128000c104c1d1020750f0300c20f401540280348124442a65400030100100c014444281c000f030103205541c0c24664140030809100384100c0c01030711107d01d40a00100c110f045040c1c0000c5104000704010408 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 653072553 1250 653071303 653071313
    0x909110918070e040b010512041407031202010b030a0f030f030615020106170c030c22020301170c0415060c0204020c101e09080f0a3c18140a03 63
    0x1910110401c80c01e070903414a00e20042061800c91401802142009a04012640c4c0320040398a451045244800c4a8840e032400103000354514080341c180344145480130080c0301080e00a49e00c484150703002001104500e03014107850b5203820305d028111030b410364000c1d40071a004040c101c00b51001840c0010f1b8958807841c600400ca5443c54403d03005070741d40d0398144419582540c60780510284940201489600c4100107603945410880c501d024480c02902200c407000149002d030200d11081d00c0c259100d41e118607645c0300040312a480a500c0348250358404e0381c0c0b070916202c0c40000010148103803902c2d5040800580320035180c5201280c00541c200f140351008101031111542e5a40800340101d50f40381951881c0740b81ca03012241001d0401c0c40c081440d0001f5042d03d007102c5045d03c154241a0701c5108441341664403c4040304c4d0b40c802d80601c4c0926110500441c24619100c40c8a6820401c81e20080481101d0304c0c02d10303084400c0e00005000050001c0801030380541c90512005166449858032582c030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 653073803 1250 653072553 653072569
    0x25140307271109010905040203040203070501050721020d080c03090c090c0f120a0e0d0206011401090801141008010c050d1503051009110103110d0b1f170705040609091109 75
    0x15200b45100301090305042c0d9a84466040002c01c400c66081d4210308140e00042c0e00c030340c881d04c111070502400003880420849070140200d0748540000a01c50b0329001ca000c069124140c08070b189000410f000f00017150740c403002d02900d0041d0240c200034241405070500740603c13404058001d0010b43d030b09003c4c1c0c582504018000f00750b01b003800d2510b88414200800700c0425180444105a40d5030000c0c0c4031002440c3c0e000442c40c0c1100c0034000703120883c82001e00103840001464008400d45e50a1000b024140120901d00b139004840d11589440c01d1079560301882c4c201c40b2154400000980c003081a602c0c060215005082c1540c410007025010965990714603180c40d040025400001d0b441d0080708040c00000c0440e405c1100c800c0c2414442155092404103a900c100360200d20607a984000c02c1b100c50305c03620350924071f000d44040d0050100d61034640143c54041e4007510111071405040c00140c0f21403165040e43d048640c20f880740510903003003403c208080c102c2d811450703140510034442082d695039201e03c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 653075053 1250 653073803 653073821
    0xd06060207080c010201060806040b042303030615130e1e071107050901030807060e0f0f1501050a0f180b06030403030e0d1713050f2514030727 63
    0x10440700303203060401810260300c1c8207000d041d645810800c103c250700204410b64025030104691586594615141031000c00d007104840580844074005c0190300030003c021800b488084a103020352b40192240003c9500c0380c1003050144e00026035013013100c032070100722981e000300406211042500045200140000084410b940041c951410310380d00b00b401440b007240540401d0380c0d06007540d030641d2242c403110301c01c003c0010003030b580e60099541e0744102844002131a02d43c100603680c5000c802d406440c0c1d940740d00f90310121443c040344000216443c0031114903080705c09014414130054608039810180105000d03e000c0c1071511048200030640c0c0d410000d61040d032190314001400407141307a1013460709903410020400e1001c038082190b001031061a15542c440140103c0104030403091505904144a5150308003044c4201c100c00801d0000c01d90400c20345034910901036070300700d0703407005000307427030801b5003811340e003503001440d00707029142180c0381c0300443e00f0100410b07044003044440c407001220100c5e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 653076303 1250 653075053 653075057
    0xc03050714070e0711150a1d06191e050903041a19020f1b01020f03120a110a1d040902090406051b13050405060409080c031201061704020f060d0606 65
    0x2d0014800301c540010025002200751070240205900704014070746c1c6100840d54120701821000008101c82225001a103042d104100f003156040308030311140741d4400301078400111002c03070407441c002e08550511540350504840b8203042550603188960100a2401404480481c042080040340080da9a1003814561b0703000003c00750384205600e031b00d901c030310244c4444004640015002030070369540000d040c0e400008180800442c0000c2d200103034a05101c100c0340e4051800045148042d4000c00345c50303140b0809089800340a000b400c207030744034444e10924040b070b030100c3c3c0000340840f0b0400c0000c29524206202904c0041e0b0a041c44e00000c03e0588101d5044030300a846104000382000d112002c000d824010f08051400d2183c1d9003c0c96610844134002d09009e11383d2800042c4156850390014140c25801c80310341c5554042e9255290b840e580144242c0c0c80c0d0810ba2000040c01c40c1c0324681403507540c42100c0e00e1a102c0d0b100e030341c20802c5010006103903d600c840f05120318000300e80a449400000c16a40e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 653077553 1250 653076303 653076313
    0x130603080712030c09080628060b09030c1002190516080a03022107031101180807031106040314070501110f0a0306051203030f0702010f0f0209090f0c0a0c03050714 72
    0x320310003d042d00c0300400c88070100301c2d04000800910300002030098205541030070f00d41001800400c49210a924605103207002801c2c503900040c29600c2000410300f0700c10580c00d6803c2c0c80700742403d0040c0a006218a040185c0c044095840381240d000010306926200b41d0036100301c08003a00000a1190041d003141203250800300a010400da0100403a00100e90144540003c003800c149100e50700e40104440078040c40400740c1c00d4030b4603010070362050651230322408150740d160360302d8100001c4a0300046801c80110715048a200103134000042ea151065500d44d8030031002035020b0040c5c0301180c001c464100c0300c1d0364170340b03200201040868000e8070301e440b8018080f648601e1344100007815504164070007801440c2c0381281e5000343c0c502100300ca81c40000322410306460745910384101c0c010303c00305041c500b903d8986a006c00c0c8004640d002004400811070b2880c0c01502c0341031108182c40b60a0703442c2180f02408000392100c4600a10103c48124024200305003418610740711618028214400c141d625040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 653078803 1250 653077553 653077583
    0x3062202070b01050f090906060f03070801110702012c040b0f040c2705130b0a0807030f03080108010c171314010501030c0b0a0503150a08011401051f020307021306030807 75
    0x1c40c0e240106034981c12142c066942c100307d61008d449490140c0814002d440044c4d07486415101004900000c08044e00200001c0591032040318040c6c2042004a00060380188441c400001d5071029503544403030311380403a195640034010400248411645181c10803011425680790350b413144500c840d8800c0948031640e0031503890380710088081c1c0f240000100030032070781da00b40000e4071005141c00d402000b945000444901c4200001c05001f01a130020100d8860754101004001c07042c60543d65031482030b101c030112030762950011400c1c2d030143c0004c140010f400620701a80d000f112080720790007400b0304103403030f0340b00000d5155000140c6c030b4101c406440380c2d1148010820425480c0d00c0f02d0091010307001b100d0403e400c00c040200607202c05010145006a080c00906041c1e9501d20154003d02984008009010701c0f2902c5a0200d10244542845201c000c1d110494500041d6181c20b00c43d003c50740034516008003075003080b000c000c80d0340d20146200d039610004400181104000d02c170030307030080e8015100801 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 653080053 1250 653078803 653078809
    0x9070303030e01090512030a11070f0b100b120a0e0a03090305061506040902030a0b06120612030c0a150b120304090b0612010e0403020f010507180b0f03062202070b0105 74
    0x240840b284851a8906030116000c100040b8625501403000b50401c2d0380c98460001940240c41d0f114030b08440da00000074005c0820002ca081440340da40b003002040c000b65030741d545807140894540701e0302040c440c04201b001c1c440000405a5940140d00d9840050310940c00b001480c0b41c0b05640c80c1c120081881b0340c8050017072080400060764044d03051201440800c01c040017007030f1140110b10a1009285c0c0100c0800c1040107a5044440f0550b0302030419078940f2005601000c50110903035005000e01c0101d400088124000700072a51b1030002403008182002c8076644102c0d170722940c0a403000350301c2d5481e8115101d1741c1c4c400d42210103120180300110317100d0342018410380440390f00e1031070701c2c0c460a42080140300e007901505141d411584074000d4082150b44a0a05a06200d0445500e504d00d510304002c12000c01c2d0401d40d14540c07103250b0150308140a488005d03030f441511808548203400c0000b40001101840e241c514800d0108800c0d00d07000c20071030241d074a00281d801400040300c1d112031410042c00242 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 653081303 1250 653080053 653080061
    0x203061201110a180f061b05060c0d1506080c0d06030c030606081006151b0f080a020c0301021c180b0a05060405061903060f0905032a0615010e0a0e0907030303 70
    0x100300440300e0380f051131425082403480c1d19144104007c0c03000b0032211010f80b00821140c00249604001503c00324500322108411070fa00c58481801020b1504039010800c8100200c4c0606691954072941c080d03484075400030806070003265440c108103407510380201c00281003441c9035008520480000c1591410030801c60f0a1110f00f0007100c003010f1911100f00401911020031100c1640342d820680000b0032185603410344481200006031101c40c0c1110a601000055002000071040503030a5400a5a68004141c2070340f080c00720b100c01e0200c0820008100c07412a07440b50148000d4107801600641e900e03501c00002090440d050110a5500c2c0100f007100e00307041c080c041d40607800301e50715010003018003100800842540405407085d5620400461002d19560240101941150480e40c448030744984403440c460305544542e0441440000c01d81c45038a0000d1080c1c098081910810303069040c2400440b5286080001e20b0340c058044800010485800200705000d250008003074020f103406c40c10064151 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 653082553 1250 653081303 653081327
    0x30705150c03010510140c0f070929030c030a030c11010519210216021e06310603090b07020f0c010c0602040b0c060a0612030509040203061201110a 65
    0x964064810481403000c410101c81c10344204550f010b2130240c240038100c803440c440301b02e891400e00000403580f298020018840407105104002c172072025444642c150181c2c1c443e003101c01c60050720040c0590922001700d0002080d0a0041d085940c06101440060b14040302544d094000c02c01d40d01ca03c0e014020210341200c0302080a081c814900042c2c0508039880140c80407416041000301d615900c1d00e001502c814400c0d400009109549468440d92041044a05500102d201e0388001b04840c0041c940001c1138403182c000240503078141016000a000114031108844a00c00d0300005001d06080d01c041c03841000e0b110594002411015038605410030307060280407001503511041c06128180c100080f125107001b02841c145446030008e160000c0030303005581040348812004545541c8103240000c22501c40c01d1105001e210160b44d59000c40008008180098001038080044225908040c1c00654016801030600d451940395406003d08550313060070310b07022800000448507030955104190701d42c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 653083803 1250 653082553 653082583
    0x408010609020f0714010e06091b0a14090a06030f0c0303021011041401090b1909060c020d020609060d0603080a120501150f110607050304230604032f030705 69
    0x3d815660840b0000780e004141c4c00034440e58144010701511042904001e11441c4114111541d070300307190200549400281d444040104140749103013032a03140c00042c01c4112001000103010302e003c01001d100500b0303001080c1003070f1161591000000601c0000140407500c2c0a10034420034103086280013401c0c841203882d8002c0b190b0030100c0301c00010501c0d20488040300c00b5074034a101041c2a9500503201203079542d10510244101243c2566043c0c0381000040340c0032602e5071001ea00b16220242038510060000010b0340101590110740c0050404000504d20640000c000354148111819403205803101a042194000380100303080c13014541090401c10030341c489440900c61981080e6140d10107070300c05140307030040040c01c000d01030304103001302d4035441c801c0180350940394249425400a446c581c0151811510f051412103940b5080800540f008000b403140c1000e050103407203039101103540c2c4c004046140407008181600310f4400c01208400241c060400025648640090a010341049808407c0200d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 653085053 1250 653083803 653083807
    0xf040506090a05180a05030901140c030304111f0f120e10091b060801050a0e22110d030c0b0c1e160b0f16030b030c0d15050c040801060902 61
    0x350790781c50350901d0340021070000000c0c1941e5480c40e0b05814010090440003a400340b8070403001400004070052103001800c1e01e94036418440304026543d103104045100100380c0040c070109000a0002160610305440141189a104030a400986058841840002c0405c514188014605401c80710340055160380441c20805500d04a5420740c8880c40507170001c5d406903071190340320b0800082400c2142100d141c16603102403551502d2010b0300409007805410703c1002200400108804900d40b4144603144000000a0342d51080b0004142c031000b21100b181d9046050044c1c422507129024000c11480c000d41d2504101e124a08003104a91000342107410090410059150303040401c0c08040003010311700c400300c2d0b40ca1100c01c50400d200e071070720b10009101740096001e100503549030f4403d99001d0242c1742080c0007021040303041a001c4840d03070101aa0181c20200400d20f06281c03041100d00d03010300034092462501e081c02c5484048400031100000744c01c40104041c443d032a0300b403140002520310004114 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 653086303 1250 653085053 653085061
    0xe0d080601140c01020d050117010b040c1b050a080d020d0e0307080324090c0901020c0103200f070c0b0304030909060f170f0604110f0103140c2203060b0f0405 70
    0x80205505411004155400241003d50100300354100c54409805200403c45035860702001208081c1c498940c98880d82400c03a1712109162070f2091411340c03000b54880117070f40011071540341d0034071646860903144ea0107440741110206020500034841d505082d40016030300c0c2a04400b0008440751501805880e51062104500181c1c00108580e00401e001d20f07000d002c100700c4214503820294042a180c2c00a040c001030180c041203200190110510036020b841c145441400114100d0391100e02d02e203d1a003100c604072991140c000009c00c003500305544800c5c0352018a4448058a0711254810380700000c0c0001007100781680804d00e4005043c805005000369494200081ca940f001130049500b20720003401c241c44461000c1001d02d0120300c0d400240d41c1e051500b400c250030608600c1900d180201c2c2003801d003030601d6202e031103268915540c20000758507903218101d8110444c0c02510200c0c2400d81d1180c40b481125403544085001148070308000304003925054240001e80650344040f03030245061034184 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 653087553 1250 653086303 653086307
    0x50a0c0c050a0320010608010504031205190b01030e16080f07030b060906040603020d06060f090b060301151704050c0406151b02131e14090a0807020109180e0d080601 73
    0x2e14040c0741c05181c00948881d985002484000d508650700c0810b619050f400a104181074005c140b01d640039441d0a454101311400000a486045a850380401c8000004134403000c0a83d2103042c03a410306140c00942c9a2101c01c00c00d244c440b02c4a01691030000b045002c01c03000c24204102038005040d80d01130205945941d840820341c800c00b400151051501c080001c4082d1101d50148009617001421114154400d0500c00d000741224000c8e082210140c05010501c070f6400c3c0502d80501002034210b51450f0f18040240c00000c000046040c10880142115904201c1c04203d40b030003140144094440030300d01600300402c0701c1080c3d10190b4050064400d0906043e0411568080100ca40e0302c00d10ba403520a100042801100c024500c500c1071502c0300990001400c8010f0480b501c1040de005c004068080c408070b2090301080319000700c10346c8880c007404000303000f600141513400c0c81810030150b500d44502000141602c44101c4460309a60341e0700da071004c4402000a620165610f080a2055051039000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 653088803 1250 653087553 653087563
    0x5030d0c0c0306051e0106180f060c021c02043206090105101709031b06010302030a080f09031e0d0c03050307180b04120210080c030411012001050a0c0c05 68
    0xd4809613403100010b0130400e0600d980690350524021640c441e40c1c4440000e1f10199101103150701c030359618030340810b07140d0155042005960681d1994210480140e0030006060166040e00075101e50241c09400180c54030300070180c0503500c90b654002d1081103803036165906122000300580c88249907041c00f420303480d60030103d419240305496009603072003164421760703441807407c02039520450500100003007001d001c4091700381041381440800203000010503803030b6602c2080c04041d6064021402442c0041c00e260000c00400d0303025981c00c0e0a2141140c006400c215254001c0c91450402c5080103207881d00612100440c1c00c0756041000200102383c038010311900000b807016007400100d496142d800c4d261a0006001014103e02c3c00345d07210b85030903c90865040040c3c0803401002c032142c0591585000b045440c0c416801c0204040c00c40d0741c2d584406c8512234040060360306010421401f0342403800b0490300c404c606080440049280d00701441c88108460802954900300840c1c0a40b00f8000380c40462 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 653090053 1250 653088803 653088809
    0xb0c18060d06030b0f04021c050f070801052707091d03070614010b03191107051b010201050f010e0403030903170f0f07020703080906280f0201060906051011030d02120105030d0c0c 79
    0x1008d9094505610303100d403070603800041d2214244140580080c1e941015004075101b0801d0715030100310f6031138600c05e2800000b820b144542180d00f0009003131201181a50241d41803a10040080541c0840c1d843d1103804c503800030345c007a14220344072031800d4003150107510300500414480d210f80c0d103107140c80760302100d00700602030b584044281c44659a86002403c1001d503110700e500201950129082120040e4107001813490090165003080d000902404c4181c1d4901d04842c51982005000d81c2c45640480040c40060011010b2045d41c55050410034400e00690344100d003400201780725403c0581244c845050010007074411580000d01c2030000541310ba040c0c50f50080d05440030703034803602c0060100d10008203001d50404041c000c000e105002070b03031000701c9010000b0349400030050309031510500c9068420310b000d040c1d004464600030041640c807c4650b259403d0b02a4252818501c017140258180ea20211444200c90340ca5070041c0140d01c1e040c480604111140c0c00c0c04ca50240382e6540d14244088144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 653091303 1250 653090053 653090089
    0x1805160e012007090f1b08150102070b0a02010e0708010612020910051507060b0d020f01050c0106080607020307140106060c080f0427180b0c18060d06030b0f0402 71
    0x2030160361240c00050400b072000850542d50000d480341c500034010281c0007035800d103040c107040300e00340342100108060000007144d40d07480d0b032140d5400b00300702c0043d20b50501b068118882c1180005041003117901500703032440990300114030b6140406401c4c2c40c00d407080e003001c18542d141510030070044100c8000c00f65441d5042d2034445442e82c81c1c900c0080c1d0980d20303500903504004540040b11510718040010304100c0e115010402201c114682400070280c4107110081d0800c000c1c1c0c21034101d96000300b001c1e00320071000c18004103540e0303103c000d1907051107030944030130000d0b90000c20900200312070303020301d040b0501e0510020481035150040043c80c643c1381d0000030700410000102c05560081d500c044a01400d001d400a141000f5500d8244856246001c104000c06140016580310b010020582515039600002c64864030780b00d42ca108440c07948260385403080c440020007c00f2051b1100000f406d05810b54410006440c1c0c0b66040c408030045000b4080103500850208200050765421010021b5201070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 653092553 1250 653091303 653091317
    0x1060b09040b040207060903051b0c09040f050102070210020606041a06070f050a080418050a14180c090a05040c1505190903080d09021003020715150509011805160e01 73
    0x4440441c0c0248145c0070b01030700b140d050080240c20300d90003000800401242540c14a240d00b5001d03082910b646c0c11414040d4040040000701b0041195002c51080b0f80780240b00052611000d1f0f130019035125058a500c0003d0382080341000010726140c806d51916484402400040c0c1c06414001186441401801000207000070f40c03030070a00c81c08102442e03815600c0070b2010307510350b00c40341090044400d4407201480d04e4100380000311140014001d035a040b86012544065079120403012401290002c4944071640c4104040004c007541c030800902d006108071000003074182002e00301070b0000360507608241003807024402c0c44941c25a0040403038034903080300100544211511041107521080c5940080e00101c03011130b40044814881e40301c0484240308407840c1c150310b0100d4606034180d0041000141440303031804200c148040440c0c0028131100d0031072014140700f41c0c840c0c0001c2d0000400b81c00009001c555002d002d811091144151500303c2c20522071181d000b41c02c0c1800800c00107500d1941810040c403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 653093803 1250 653092553 653092571
    0x11060c01060815190c0f0804020402210a0608070513020f0904020c030a030b1e04023007031103010b042102030706111504081e070b0406061701060b0904 67
    0xa512000103050b40800703850340840f00c0c0b210505a508280c4802008802422010b01d4110151044000d094004c0c3c650405148600ea01601c41400c01002660042c0d0200b0141c40c0c0460566a00205261200c2ea50002400c03c400c01000300c07012a0440c0d0b600d03500c07901c030038815991070240307081c00712042d041d0159889020046e03202203030085814280e04140089101440c94030003001410f12206550b070200b0544204108002d1a40c0340c00c900358000124143d1001018202500102603101640c2d42c070700140d840f81448140300343c008095030480c0758144000d1103502c40c1d160188a000c1e0b2031032441c480c04e41d4104060301495100c0e522488030701e216201c00c4503250840003c504852503800405039800e1954a80c40903003118034a40d00741d044c500030303900c800103460411080c1d54003c54004103110304001c07100054444c1c00856115010301020140000000101c0c0b4201107841030744160804030304145807584001c0295801d101700c00e00c603418030300103001103003500c010b0700da03661400c440219240c10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 653095053 1250 653093803 653093827
    0xf0f070201020706050112020118061d041e02070210170703020702011115070f02190b0415020f0a0305090a202404140315040303090317090c0114071106 67
    0x30480c3c8006090a08000001614100c60401c0c0e013080e5000f030b2a60607200d03014428604990046005640104d0b801c4400d0750360036080a8141202d45501600005800aa01c600317060b00191041c507980310550000b1310340c41182045000003a001500f0b04041d0400c40c44440c0000403404028029001c0580c04500b44c425684200040b5501714807a905440e01d02d402c15111080703001080380c0040200e0306c0706d2058806103200081807102d2400d40010310034108400c0d0341d250b4000c0c80c023030070640d16141c06400c40002a5468801800ca0031049080300340d03901c2e00c03040080c054600c02080e62a02d81c00810313004011134510584414000600d00800d41315001141c002a0310106030130104908040d00b03070900382c040244400400c140c1d0221940381c8490362a1340c0416a84504400441142c240341340081000a070081e04600c0d501d82c401d0801c0600700081780c081000545003290902c0071075101d1503221081c0d5070405a003103918191002018602042600c54003c1e01106142080c0903410028040005203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 653096303 1250 653095053 653095057
    0xa030e1e100f020705030a0c09050901060b040b090109140d060902010302041a030f010b0c2e02181806100e130c0804031107181d1903030605090f0f07020102 69
    0x9900105070001206244074010300b0740840d001c82d200544a409004030b601d140c0001c0410550340d000454241c01410881d80700d0280c48003070508480d07076489007004070304c0d45048006000030b04510014a03444030082c00004144250981c0135143c103840202c103510098844d03c180b03060264000c1d01c00302d582069440128001c1c070495201d1400700d074211080004030046013004500610110900080598031290580050f10504007002e000f640264040304142c03070110350350f01d8a40510341c0c160009558008003c3c060341e1202120392074016240351801c0d0249404011080c0702c8004184828a0b85015004100200d0b8882d00040a10240e0f0025919554a0441c405085e0340c1142080c441841c0b038240181c480e105c2500c2c12000b09076400c3c408400104001422421207940c01410585060300400c604003c5c42828001c070001c0010040403801c0039805c001143e0355040b80d81d48141030345514203000b0100c0b881030300f100780b00300704903000e020f07a003000301000c0c90b0070005211400032031b83c0307458209a0081c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 653097553 1250 653096303 653096359
    0x6030c0c0b0703060e0a0203060f01181d09010c090305100e07090e0307020901060f0801063b120a0c062115050f1c171e0406110a030e 59
    0x6106040400c0146640351300140211500c4800045040d10380501e044143d000c200d48030f80c0c02500e20b10301000d1541c4241c0c941840100140ca2443e01c1c00e03101c2070b0215040400f000c89401d00302c60f05091203602c640906c00d82910524610b00f00003811f08650b01c16440360303290440d0f07203c0c56440381c01042c8400b205003c1301c0e0081a2a9000304854410700c02016142e07001322505921072546500000307440c03400742a500349000343d0303540c1d580501d07800c7c01d1068440d40301481a44031000600c031680940500080180d003910720541d19119411100001002007500340d44030048041d40060501e60b002642e407400c20000c1d20203904052005450315019035400700c61101e0703140718440c01d1240e8186003403400c2510030155807042da001101301d421041485040c0c00c0030589074090294010385000801c0420100a12090342c82e25040c0c500b08094103c9d1946448641954a0420b0300140420200d500030003802101500e0708050002603410b6200079020900030b803406802600340c040300c0041c00312100000466 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 653098803 1250 653097553 653097563
    0x4060f0e061f0608010308030f07030603300c08070803130f121b02100f02101d100912030c050708070503070311060606070201030e01060e181b0a06030c0c 68
    0x45860900c00d48030900c5031070310810358000102d80e0041001072046003c541a20380000003031b455030701e46100c03000702d6100042c600d100b01552420040005158100c400302c6481c01001d500c8900b2445400849405c00c1c0e5003491014411100443ca0000d2041001d0303600003508500d015441c0e69443c08040b0249250b25401002c1c45500c000700002c100c40441c0004800029170f0f90901e400c0c03a04101e6001001000c04040d611100c07000003460301d98400c04403028619024419200b45002d0045070501380c0d0700682c4214507500c001c040c440a030403410820b8241940081e68244001d2040d40c031212400c4100d80a1441099190f040f003c4101d4010000c44c0c00003070340250116a2540103050082d117940210800720300103044040c2d06101c01600048190181c01c009000e9072609485038019802400c4e8064400001d540b94103000400d4404261100d200c0c03a01000d01fa000c030070002d100a030822000d01012411885608603aa0003900c92144441c16a001410300080c020501881511407084000000340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 653100053 1250 653098803 653098813
    0x201032c0a0302011a1e191202040506150406180803030711101b1d0a090b03120a020a02091f18060b03010b03071808030a031a0f0904060f0e 62
    0x40c00e000040302400d40d80268020050014000341580f00710b0b5036441c0d503952055506030b0b0502c07040521861044280303030092062a001485100da002030402a900840f20315111022250560516000c3c59034040c0c0700f101d00040f41110411030034000d000b140102c1e4108040d4010840b6040904030040c006816174100312903d03840d18040040041e40390300400449030081c02100c800004860142c13941c02074003502c0c0c400380040984000c40307040170b054184070791854200c50000080c2d162481c804e0064640c1d480d020961441e24410b052807c0c1c03102010303d0301038008010007c00194042511000307d90304503000601034549121780d04522070410b0040e801c0c0603010b0400605041030210040703400b1145a000e000c01c5d0b03940c2c5a48240e03070000f446200000941040003403482c6200390265a03030200705c05603000c20503807241907080c030f0b503001001d04101103640c030110901200080d0b803090002003011510440c1c10b20924020414100c4c01070001042301d9254500c105c50010980c115461108942e42110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 653101303 1250 653100053 653100131
    0x210207080f010902041a01021b0303090a030f05061f030308070c1e0b060105070305120a060e04080a1b021311090409050601180b01050301150504120f020f060301080a020103 76
    0x30b00802252804034840d52070300c21a2922000d4146240c0c1c03101605070047c0c180300300b6500d4084c01020328404000d916000800c4032400d5039403440d1b6600084c5000f101d001402680502d81603152200140003130348085803410072120315071140c0132160103482d40341c509100541c94800041d01c0c3c0c42da41c0400141180343c100141c01002d084198200b425a004226440161f00c0f001d0054640c0c0c80344da180640081c101b04444890320a65502480e0043c1a42c2000181d6a80d14903020b04402c00541d41210001c0303000520109a5610914014003440d10000520b20541e00742d000808148042c2800070b03e444e2200b03c000040d0070210700b640c40420303014000303102449913032820b281c84800900401034015009140e8000e0031030f00c0c0c41040c0c190641030b140c2610b50b03408d101c490740c118926207a2080421000304804200e41003060b0a10192911803000320f007400d41944100318024640c0c041c6140110001c0c0010084584005080745040703030282070029008070a51420003040c1202c803816138122052034044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 653102553 1250 653101303 653101333
    0x1031d0d030b060306060d0b0d0f0b010807230919060609030303051e071803050118150b0307090e030c2b0c0201020c041a130c140721020708 62
    0x42404040581d804100d01040902000b103603020a442c441c5d0404e07424000070000100d66030180d00b2a56000741482c40c40c02c190782d1118256640b4500440d00d01c04000d00412481d48108684d40207003036504003400418004003c8050f00c00c00b00400240b0901640000c503040c4006181a034000000412090003540e444500c050004080e5100450000380341100040c405c2030603110940d508c104200d82410f0540b07940504440800e00c1e0500a068002107550000005500744540004800041ca01c09010460fa08042d100c801e1a00444604a8202000c40c036082da004134600044c4d480300403002840a80f85da807521701c3d40c050310034075880d5482010009590f1400400100e8258000c800c5105004440c0510840e10f807410000000e02590010755175a1103440c0c1a04846001c11103200741c00c4035103103a640007401d4804400e44400c207032a80c8500d1002e2aa500104596034801045d0034580340c48603590b542c14042030700c03806c00b00359a8052000a03080c4e0380309001141c01085d8080450315042c002a11f1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 653103803 1250 653102553 653102563
    0x1d011206030803100f140f18070305010e070201020307120e10060f050909071217070515040302160f0512070b0a0801090f05090c0103050601020c03030d140a151401031d 74
    0x3900d240d04008600041c14501c00385c030b03400586400321345655400c00144c0a1021040400b501198049400d84440d80c00b2184812020710804003590045000e51401d1281c240c1d1070f00240402046900400804c07407119003209240050704a074502c001801e8030001d0080f42090442003620f03100d5410030400082d20307210300c5400c0003034810407210320405440310310b04556901a01e1007000b01c1c60840c0414040400c6e055000c1c00c0901a86440441ca0200c09a844900702020b402020841c1c0b4952414401815810843d2207a407003400085900042d0078010a03003e18851071048620424090145007010003003440003200510410f00c1d2680c4034441c0001c007a000d500b0034001c11036118034011a41c40b460380d01d13000783e5024a549a01030400b007800780c40110040c0100a003120705521584854200310f4030100000c00e040c41c45510000359614694070a07108804c4054000d0002070300704070301c1019007040380d0120011500031042d2032220891a000582c05080c010a00c410b19002d1554001540000851 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 653105053 1250 653103803 653103811
    0x10509041a150702090c0708040302040615020c01020601060c0f0204020f1b0d030c0f03090212060a0b09090105011d07170a27150c020a020405090703140606011d011206030803 77
    0xe0252400803020820410b24010706001a600000040c0414684903000c0001c08640d0300500d10545816269004982a02c22a51040004041460b154400b071503050040407801c0400344050119549800801401d08010510203000b500300c54072040115551641102c1040c004600420b1303c8500300b0303019001000c1c50207901c0040e806801070040d034080c803d03c60413030030305110348a076440011a10422002082c0a0a0490300103403501000d800d00a81000031a120ba00d080b400840c100401c1014032221a0003e000c010882e81440018042c840b40540410003284000f0b5440105688410f03048030420a2441c0c0da416696203d418001410035940003683c0030780d200790b96880a008190282000050a01c0c0c0103000c00c40d0080b6020403490382d1b0b80100d13088901c1031044884c1d061054000400700e41c1305031032101503680301c01c1c000c1080002c24210140c00700f201e0000703000d01c0e1901c00d001070a40c0321241d44c541e41d01d0f84136951440380d5038001d001100244101840400c840b54413407070a01c040c0d500541e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 653106303 1250 653105053 653105059
    0x3290f0a0608060909071a180406091a03060408160c03060c05031b18060a050d0518011d030f07020114190810060225030b1e010510020303070c02010509041a 69
    0x1300000700d40c82c0d0f0001764030041b2680c00300b0110344400b071144140142e400c60b542c2c0b81c400607298403c40c5400ea54a0150b0030280840520005211b1000a101110100d5130541d56010790400002c01022070803080036960955007020311141d02c15503502c0c003207c2c880e03141d810050555141104e400c84455200b40594415801c803420704607410f4010700c0401440c000c201500350241400c15002c001307810f190001d03040511840c00d1050400e80c10410000541d001103c00040340480509500e400320b80900550b404410a8000c05544c8480092165107a104010064420001c006202011a407080c1c0090f20f42c212541c0c14503840348030800010001d02b0594007070f880010b54000200c9d02d464a4484441d00b100c2103900102070804203615005a820b400680f02c1803501104c403c0003000c2540c1c00c0d60a8454500704402c21541c0e2440c0c1030421120302d040e00261700840100d240810381070b40000881e0740041c40f5040c110031100d03441c40125507610680220a4001e400c0c02200d4900007581c0c2c4850420305411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 653107553 1250 653106303 653106319
    0x30b01031a01420809010f060e07080603030904050f07110f0c010804061401120312020405090a051b0c0109051e15180706050706050703290f0a060806 66
    0x20191400d61030020700480444a036000c8203400040e200340c0c85451003888003002c1c03018160742c0c0b40c41c0f92600445444850301181d000d9080060190082c0300c1d9981400701c03850104a41030800708000160100140500c050040c00c0c4045030042d9030400623641c1d130369002481800b007403610b220703c030407406c2040c4d0300040800d03101074542070090808158210b055410000410750086c00c0c00045541040241041d5172155a88490510384014910b60a010300f0030303044030b00b10450f0b43d440c004002c5c1c0b042c07002c2e940300780303106000501150b0354105006410240000c00810251900c074510902d01d120710f800200e0800b40042e81c0140c401e01034000e0b0003102e0149050f41c0c0c6d4040b00c010712464800036400040800e8000e070001402045440130103540101544c4050780e004580c02194624081c400c2e00410041900483c0680400106000340350f844680c602e42841783c2140c06220300c0180000c41446e2a1114074141c000d032064482440e204500030f0018201c861155982902a0449400759280c900850701 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 653108803 1250 653107553 653107583
    0x115180509030a030f090b160908010204120321051f08032517030f0f0603031305121011030105011b200114070b010f0f060905060304021504030b0103 66
    0xd1190520950821000d10b180c01e0f00c510b0110700074171480d180700d21082c3d91480c4a00100740700380c0303405115203400c042c00711030704031410405041c00d941c40e03010b80282da00401041c8035203003811800c0400c04d50705003060761080d400c000e01524842001c07d006840189002e017001040e49140240c07150b550b003d86c601e104102d48510300183c4070320500007103084011080101c504010101d000402509000d0000c1c041440206483c092a5500540d12040414642810722086d02241c1802c1a0003040480c0111b1501807403031040c80002c2d04a00c01e951065294a400511080b810301542011070000c14040214607091074640c14190804c0c040c0314009040c0c003840c5500820219802021036030020580385220514881042004002c54034043c10401d010215025554440010b000c00c031b03201e0a000941581008aa100998603e500080b040d00148604210352134200b03001c0d40c00d81d9415100c0c00d98079501c1c0e002042c2210900100275860181c00900001413100009407071303068038071465100094920b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 653110053 1250 653108803 653108849
    0x130905060f0a1a1c0503040512010230061306050604120c0506161101050d0c0e1002060c04170102160c03030201061d0604020901110609010c080f010605040501050a0201020403050115 80
    0xf1070803444580003034124110041342d060000b14560307024440e400300e9140c50740707400200e030f44849100000c0340169008200340b000c07000c000e40c56880070740420555202200c01070264008540c0d0141c07096005180e0320813540c54059451b0049805041d011345503a9640c0d0381c41c078064030000c1c2180402da8000103030f80d8002c250741c90401d04039030b0090203401581070b00314460b413203801010445403000c506001b0104002ca204065a000b840032041c0c560310b4040031084500280413170340200748140d400715008402001124003440741070b42c1c1a280b480c0480c0b20400c03c008600d500902c9011070350040d8452039000c004c00c01983e44080020703a84070342d0080c40740ca950b8000f88119407200c0e1040b83c0100c0302c7d210000d04d55007030136809407032071810507d0100e00c1d889101e00514241481547c00c80c030b03641d441e81c002d43c880380d800c09511500282c03503040011281d8545200101a80114010b103810040d00040300d03203240d8401d4041d28065500080200211428102c2c5200300c42d90512410f590001c281c844001c00d10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 653111303 1250 653110053 653110091
    0xa1701050f060a0506210403050c010b0904080a0e0301060302030f0d140c030a0509011b0b150607111c0602130e010504090f0b0619141c050c130905060f0a 68
    0x80b00503002d800c0c0ea81c1072a0800186030440310a41c0810644044e111106440605e103c03402680a038940304d9844412a42003800d4400001c00107005101240074071000420110458900306c2c1d040c84c210100038100320000e401b6045541c800b80d85445040f101010200c400300f9507047d03910480d02e43c6521044690010200d40c007602281c00c0e40d03904203101103c0c02602130300c0103281d90281490003142e820408840c1d01103229400708241d86200d501c2c0d04110022040395015075091700112401424034102d641d802190081000b1703024000c100e00018022400485031342d011880750302100c15503c4030968101c03104054031510071807811010040000401d42014482d4400c91500412103020351001c0b07444102031008080c106a42203001038003854403501e0038038002ca003c4c128076008040c0a1800b4010080390544804100750592804020440090400030f44c41ca506e5074107807402580c5111110800340103000ca01d402504600811081001c400402045107201d4038506a04115035880a0049001c403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 653112553 1250 653111303 653111311
    0xa08210103050a150219120b010c0b04060921020309040606080c0304061d0f0309270a0902010302090a080d080a050c040b1b010204030c0f27020a020c0a1701050f 71
    0x140c0c1000f0a1140460b00300006240c04540d401e03000343c0f0348080f2001454001c041c01c04000006208840c0000030f0b903c084c000e50751018400d01e03004113428560348416010303250241c030050070300340d540d0720000401a11440500600c9084464046400c088141c040e4582c1d08c001d07d16441940b5005004c160716008060050041c03084100040c00c580d500e6031401c00410001881c1d02c0707501c3e0301802503810480100702d081c44043c000750245480c1c1e000c50b014080c079159980c10034004a03451203002448000c036090810303071043c0f0540000c00e11500700d0006800a01c240c042d095005030340f1000105001c880059042e10940c050f0381d8040c00c91b614006401d045410554584a0780e90081004000700d22034040600040c44c40e41842c0b0281e07009220b20542203078001e80c411101c1c0c03800040200081c074840d040381401008140400502d03250303c00c90114040141111090980e940444d07070b0302c466031080054082e5080054040190780f601e52802511001080e00c25060660034100041c6801d03100c00140703806 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 653113803 1250 653112553 653112563
    0x50106060801081006060c120e0603090f0705090c070b19020304060b09070804050d111509010c021b09010e1302040603051f06030b01060c030512010e22022805030a08210103 76
    0xc8040590303a8403240d608c442d55007400c00c00300c024400d18031342d030b43e000071030240707a1107001002206003010400c2c4c20300f549644490f1044141204100d850054541111241c036440f004248507540c0701240c02ca454104018003005461010081204001040c0e11000240004a51460b402d0395031903030440b4078410440c0c0041c9141c02c614600e43d030a034095051000d46610180070307100342010401c20880d00d4401100c0c0b060540c0e4441c1384e2484075a40602583c0d060152030030303844d0b81c1404030502241030510103104070000410541c0015a19004c03560100308002d50090051000c250780e4107000350b0301e83c450380040d6803840c0400e6916184c0011392107054112540480f0903480c62b03107004810f84107603d0355801902840020000454052404150240a00f40400120310b40f42020003940c003c0310032180c80100811481d040a00260340d07140c00b0b0004240c03c01e0a6015075881900361000c5c8080203030305c4a6010301c6503550800401295001914a2007007022281e04c0080c052003518030480000c0c400500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 653115053 1250 653113803 653113817
    0x305040c0e16080603061018020f160204060602070f0b0a1407030c151a040f15080607022116050705030703030201020409180308150315070f09140102070b1605010606080108100606 79
    0x7915410f4841c0042070003400300050400c05428ac120f0681d5120041100400c018041c41c202146058407413a07010b0078031440180f50050400b0710b40f0300384412a00500352202c10100d84101c0103445030700c4681c80c1c800c00810560300e688003480d001d0706030b4000010071a00b00100f544500e0705183c852040600340f090000d030680458504000b404024401c000364961100c3c0c8035082004038a5016a100d4010190540100081d14109400a04212409021b09014107000b268070502005007000d40318001079460000282c2c22140c40e000c1d2400e14283c0c40300790140243c5400105068065004d03004807680c44c04240300c050b080407259203040640140c010003007204000030555106004200c40308144001e4200c84801d0424002c0b034501c0d420031104500001ca118503103001d604d80c000c0110b4010040c615110849d4501500042c0d102c01e42c0d4003070509102c0d03010500c5000716200241003104a0f4101c1c000f0402c0644a440040c0f201909005003d00d034851090f0751401049144500c0045840c0c2c1c1e59404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 653116303 1250 653115053 653115059
    0x30e01020c191a100e0f0f150a0302030f0d11010603081903090602070c080d2a050a0c06091e420201050a0f050c03070305040c0e160806030610 63
    0x400031986410054807074960040415100d4540f5000c403e0160307240c01561000c0c945000e4440d6003101008046600f102000800d000100c0200e0701600e8100f29a060542000d003070300808076903c000c007035002950501c00e041c0c03140120240441e0340c0c22448159038440c1820601d0529803030a0320b045110040c0301d200b003001602c044000880c005802d0b5440c911740810000c115865041c00d1b44c1101c5429210f0711007c002c1002851010800c02c030f42c0100c24108103000000450194101881c0d9540303c42032228006001c4080042c1407044044881e800920b881c412074940c8070003400d106040c09400c030651940780d0800509603070590f07a001200d10031142141040e051600d101c1041030355850589006c4580030b00c0080c1c01c680210303071018a0b2416400000c0524100141c0d2003a03942c0780740d2002d071191a040c00d10001c40e20040c11a039004d030440c200032a480c0c079680350100e0961f510358003141348426030100b84140d00e00344c1e034950480e040e050b41d10203005071940f004043d2550130540d41c007150054250010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 653117553 1250 653116303 653116333
    0xa0e0708210f0408070609060906080f010b0a030e1e06130507090b0109030b040b071d0d14150c0306010f030203010806060f060f07210201090209070804061b0f030e01020c 75
    0x2e1840622215a071410300342d4821140b40760240d01e070090004210b203034606015030350b40261400001d100c145401c400e54107112403a49034058040c0030f003210002002030741c2000c540c042d4208045020003076040b0303950000d0886103c04994200400340c0810701a00b004128170400d0309071520f20541d00200500681440c05103080000e00c15105240e0600400d6400000800c01d000d100d24440c40c01011503160130f01d06158001c1c0380201c002c41ea8406a4a11405001952909d010303a028266100e049202d00600450700b5500d40142640c40f4072a5400f800d0401505414140186000e41d00030f807140e1545900322203080c0d0503030009000c2c00343c0b150b20040010b6001e03e45101d0344403081001410043c40c09981456a4075030b68001346042e1004c60064031802c0d01c0038608c40c21040b284040d8802040b01404560019002c540702916201c2049000c0020409000440c0c0c000500d0b102215180c4001601c005c1c0c0151064078012900400f1a01d040c4100030121410700841b000d1070309240107406001d4030a00c030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 653118803 1250 653117553 653117557
    0x60c030c1e25021e0307090915090305190306140906060d0c0f0f052104150c0513080c0109030b0a0b0402160b1f09020a090f08010605120114040f1a0a0e070821 70
    0x2ea61000164400c0d0272142078904c90788001500903680d0070341d07400e2080c460341503070200550042c003090702d4071400b048069124084000038840817a28a0415101c81c00010b083d40180354012241c245040c0302500190f4000f46800002c0d800380d2a8207540c50000c0000784e64600800c0d80d0000c451240751080084101c540c0303101e0f54000d00c200740100b124000261010110313100c1500e40c2000c42c5c00051100020000d02c00404010042d840c020702c01d03110040b00003001074805100082004466101113000e666a0f90001403c104000c0d1046444141198200341204101031043d150341d80080c012038800c0b900068081c09181e0b6034080c00234514a4208000300942c0040c200d00200400890049401c403c0c1442440003043e038a400030500c40d0600b0301304003285e14440a000035580c500410212580e210403015a4002d0b017001c00990341044078140045280c00104002d500d01090004119200000d58803107802080c401049805664a44114540e07501805140300000b0006036560710f04e16201c880 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 653120053 1250 653118803 653118821
    0xf07082b140a0c110f0c0a090e0d03020f0403141e060403020a02010f0e09132f040c09032f0a0b030604050405070f06050c060c030c1e25021e030709 65
    0x3c0e290805181c250101818940c42c45d862410540051000d402c20b8603280c030114026101c1c3d140c0c2042400c1e00814010781d91b040c2403101201f45500420801d05684182060750010b64002e0501007221000302c068545402001c02d0340707601e610003252140340801000900a2080e07030f068000301101c40c05234005480d00c015100001b020003103041b12100e09034803120f8105001d5080c03580b4040c092036941c9411001b007400d5981006e01100203510100680c801e5480da0701c003204050ba80010324842241c3d0881d41d5244607000608803844c4150b45803068291500c4848403400360f00800c04240b480e032410409078401d5485100800744003440460428545170b400650054401d0088520300d0380c1c0c5000c074500451041c0d1046021420101300300c1e40d13a25007072004560190b90180c120b4035501d4805008481c5010f0349030a0b40c8000d240c000820030b00c540e02011154001d61042900c100060705400c60081c00601c0e070000c1b030281001c0140004c4502074000b60202c2903074024003408035a410840e03044000d00f0800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 653121303 1250 653120053 653120057
    0xf0f0309060213030b01051203090102070e0a0615111605011218050f0303150405010e0a0f0f1a0a1409011211060a050a080906040b0a020f07082b140a0c 67
    0xf1500300c003010002846401035100f1414810710398500410811802144030704a0303032030742007040480714680e07001c41c3c078500b81d0380c83c00300e46040341c0c40f0b540c3c0b110001c3c070507608000101024841e10394041134016100713124046450044403e031079503030f04a558030300c40e03117101d990b0200d00d201100003e40e070381d50307003107860744042405a00da0414056210744d8035000218511680c00d400020910481c203012229140e20207200b920140300c50351611400a604100041c4110700e100d03944d41588402c107089800050f03056035000002e0008c940c28051218082c0e03c03401461303100302c1100c1c1000500e4180144c810919460041c1022541d030728054240031030007595001190b40b46044180071400f9511580a0040341015a13941030700c80b0508500640811400351003041654010010040060b9001001990020b45001d000d62540c40c25401c214060040040c014208200440c81040884914409114000d04c40314003a030a07548034001c01007181e0200001e41c0785034440d1400a074808003607800c8452001558 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 653122553 1250 653121303 653121307
    0x17070632071b0f03080601110102070803040b040303202a19020118090f050c0702090c0c12070b04062406211a0102070602011e0c1115090d0f0f03090602 67
    0x259142e946210302c80f641100403031031403810701000e56808445001000c0d0404021450714801d6140d035282800b00034030050070818a03d00103020188240c01048280c04100c034a103e000008503076010507a000351816a404000780363740c0c003400388801e43c600704200d046038000d003c2c3d03102c0d41940404101c26080c02079041c0300d01d05513030129100d001c000c8100140b007200e0340081c3c0700840984820079100080d1005804180a010b11000f607562b41c003030b04e60050034400e074540d9240201d05525007080107501048000c1140400c110007403050003c1c0307062281d807041c1ca08000882160411010080a49035140510200c2c000140300541c003e8407010410454021904240c40300740e0110403e4a007540140c008c1e6404581c803900c0296010030000d0058042800203203c19040c01c281010480c1c0845010341e0f085864240101a040c02100d031011080f140e03005032900210761444140c860036046d90660214450083c0803880d05100d420640130301c540c42d0f690700c1000504104e045010385034006050301c10b5642 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 653123803 1250 653122553 653122607
    0x170a090b100f09020304050d1110060b030f060102011803120f020403051f0b1e060d02120106081506030f0702010b1306050307090e03090108041707063207 68
    0x20520a5610500340c12003116201c0382060b9090309000280d500c440700c810b0060003800001500860501140ea4032842c0c5901061079010541c1e103490072a050b0042c05d1464000b021a040c110f120040d0710444103280f03842c3c81c80c0c85140c0120300b204c0303108003400074030b082c03c00300000000e116001b410b11405e0185004280c3e0525004400200d0788298022a2a41e0101255549020014244801c0c2340002081046011440400701d100030340e500c00c11000b4602c551880081c42e503105010b03074016441d4900c085407036000d400c1c698810312100380143c0000c02d258100041c0603810708641c5484070361000d0301440c115150110900c1210402901350b60955498420400b1236454000c01c0c00c0420000d000c001c24810300e40820300d81090001c2d00811000c0d41400f0408191440c00030450303444260a00e00b010040d41d40c2d007807822062410101c0117451110001d149028010642c200400f00901b042404034505460440c00e60107454040d000c004400000c1c0000d804240a15000040c0c01e105118003c0740f10b007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 653125053 1250 653123803 653123813
    0x718090c0b130b0c0c1507050f120406121e09020a0b092b0f03020102041401090506192601050a140307061b0203070801271e020d08030702060703050a060501170a09 72
    0x1400c202a80c1d43d9030f80807640c07e060280c10001c50781d070700c9001b2002c0c02030f204d5400009069486503000e40c001f0300550007000c04c521607682d800040c3c06000c01007210900400c0d1a00f0001a00ea000e030107a1007108584c001240884070300040b00d902500007070075206400c00c4100503000c00c0101e142d202c1c4d80741119061a07000715040b050303d02144c0d03110fa030006075103504000c0c45017010581c3e010b03050f0401080f1041842242c030346a044540740550300d0306841428080c031000326000091854500c500341c0d10000c000c0d4442d001441c01c00c0c142ca004640e904d800b107031100300c1d0781f445138078001a0651513030012008020b003078015106403203205130764031001e01da0321102e40110346404860351041c14503a5554201540341001c0b80410007003003042d201a40c1980a184c0c80300140f000c9000c21805040020801e42011907480003140303806c6c250700c00903440d16841c207000c0294850b0011103195001c24108400110b12081c80e104003810f80328161610982c1c00c00801d946009403000030701e0003d20558514074100030030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 653126303 1250 653125053 653125069
    0x80c2212050d091403101d16060305010603020909040b150312071106040303090605090406120803040c05011b030c060e0a0c0614190e030718090c0b130b0c0c 69
    0x107020307000400c602e601c900760081140c1129480805001e0100540c003d00b40d90104010710110051940406e0518030f0241016030000c1d86002c02c0c2107881441410b10101d00e20303004034801c90319aa1000c0140c1c0e0390b01c803020740503407041d41c80c60b0b40e0001802e0006800504454410b035008a1600e000300342c2004c091010900e000020b14180992980200346a400c020030110840b041030400c0d60a5400e241c07a580e00039102c203155000c2c3c0700070b02c4800308030126203484662003034005062101804020744030700c1c100b0010030350040d941030b01c0f60509554003241e0f0394022002400074100031510090b1101081c2c4040316560007190f021150380391078400034202c9040811034034005601a04e00744500074941203002c0c040745600380012032040000e00c000a83d070b00d020002d03800c0002079404c203210481c49403800281800d8254006221201c001700ca0a0101e181c00c1d846200c03c2c6101d041d1040369180c03611520800c50089900b2842c15001c80c00045c0b02c00c80007400a484495100c1007202c440300b2405c0c00062443d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 653127553 1250 653126303 653126339
    0xd0e03030a0f1b0e090703090c1511010501030309050d0807020405010305063c060105070203150117030c0d18080f10050a02071110022803030606080c22 67
    0x65600c84200040c540740314455100000c00d84446818464815800688000d9991302024402e2510b9400140e9a5000e0f400c450f034582e51068140240341c0e1074001c10b4492480c03004160001949a84213509800c42c14070807a030589816864203602d6a10f000c080003c020384554040710390b02020b101c900300580310750007001c6c0a580f0a4001d4225890a181e10110b843e040344c0040e100c00c000d5583c0e442c00f050300703503520504d100c1907681c4c4001c1c656504801171703c09203e0600029007502c00d2450103004116100ea8403416241c045110112010042030f900f55240980c42e41e03644243c001d850f104030b5050142e90461800b01381b240024140540d40c0e6101c500300403c1e051115455003200a2508004c00c641c411550300145c000d80031824034103251690300200e103402402901940644405049590007081182e98103d040c0044c100311440250050400c1140f4000c21000701e814201d01007000c0f4010410503120360004a24030782410b2240a000c444000340f4845080201c00840c008118511540070b01141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 653128803 1250 653127553 653127571
    0x1f050421180f0314030304080403080f09090901060806090a050304170a08040906150311030628061812150902041d0105060f0901080307030c05150403090807090203010e0c0d0e0303 79
    0x800c07032a60405180c0110b040b958141c1342d8104204001c002015071040e5400c0e80e030020300042c0c4840214040e180c2c40d1061b050b40c158041449000c10100640540020054444407030a0b90740300e465010900e556400640c00050254100780b00c1400340c46903003010007070b030700f000c40080b52404403072501c0e08040760380950001791620340c0b20b010034041110003007510300f4851018034042200040201c405a1140409001d071072094141100c040b041003000391454a0340da0740300c46510b8100b9601d0700040e103002c001c07111800d5004a66080003500c400304500c2404019042100c4100d100c110b0240c10303000f09080c0790304a07802560b50030b0f510251a10a01c030083c5044022000240c641010410008074a602d00f0780e0b0303486007a1220050000b00e1011054540c829407500302190180c4c89450b100c0c0c01c0011055014588444440c01c01043c9944821410115200c0b50151f4400549540b1910240c0c8003d002c0c0788000940080403c4180624600804030a100c0c0c1400044407101c0c40040d174155401079592100d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 653130053 1250 653128803 653128829
    0x190504050a170a0908030f04091a12070303031103060303160c08061611010b06090f0f0904230601060221120a0609180b01060c02030f010c021f05042118 67
    0xa186400004103405000304170001d40c24501007a6540e0070a204030701407000059180c0440d01c4072243c3d9401d21109840000b070103480380b44180d803c0c0c965180340c20f00c4140e00190a2074081880302c0b081c0c2741100d0082c0b0b000340240d481c010411070b41e054103000000c0e0480c0e5500480c0000034100304184200340c02100b400a2a0840000710000140940124a003040d116458583c2190751560fa02c422500c0c261030070f4500b50020385000700001c2403518803080b1241c0204d442005c10082089241034050380000424002e414a0744030305020355114000d024110160344401115150781015081c500316203450000c0451619030000c8004850032400c0d501a4442d940700c0000f484160841c0c000c0c4095a00e5404201e80a05c02d29116080b9046062017050140003042c01e10400b5900c0c14000302e666920484001c0c01009510003009550305180700104070a001f02004c2d00d0124800c1c1e00940380a140c204000240001c401c0e51101d18100381d050316007050040e0688089107103aa0b03852804001e18008215079 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 653131303 1250 653130053 653130067
    0x27150c1e08061e0901150c2301051308070204020331030207050102010e03030c130b0a08060112050106020a0b090f011401030219050a090c0e06042606190504050a17 72
    0x80100340a00c0904001d03542d003e00392440e180e80e00000e0469075080c02d007111200392503030300362035400403900050f0010300c46901e6004600b556000e000e00c03401e83c1c0002040a5600d43c00308108100ca07040780100070b20810080500580740c1a00912f42000071106225081d03000303034818030405800d00b20724400c000625180c4405064042c404100200b000b030000740300104000354980d03201c1c4070040108484410200b2101d01d801c0d074881d1810007a00900d441c203a502c0490f880081c2c180c0804a80b282d00250300c1e881e100680c42d003280141c9040b1801d0703070003c210809140da6410f401000040c540502031003911030700c1c08030341c500b4020007030311852081da441469411401440099282004300411180182400b009142c42e00200d800449281c5280015000c090250442341c5007001a5403582c800408640480c801d9800c0034007000448100c0e2003104c0b45202054026200d00c07049440c05041b0318103031900540c1e1a4160030591380a4840d009a804001e12580c5d03002e40c1c1710b01d58402e00310644020400f4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 653132553 1250 653131303 653131309
    0x30405032502031c0906030e0a0f0503120c1c0c0e09100306050f011401050c100c0f0e010c050d1b1205093a051f27150c1e0806 56
    0xb60702200c4c01c00d840003d030a01d18001d042038405105007404c16035102162040200c041c041544500d40c801c2e0749200113400c40c10520703a02c0c1c0244603104501500f440c049112240c03a401243c80c6031003000e1b6000d201001920180000f04a600c5140c02806100900828140d80e046407251082115288078012a0b0450078240c049500041c8000e65600c2d014005110f070a071112240c0b50810000d28080e551414034040c258240410941c10041c01410200c5400c44190003e10440507001a5907400c003c0c5800480110340880d003150000e0311f1a0040f5001e03844492254280640d4160300001c07240403010181ea03045d0402401d000d40000250b000b20340c441c0c0c0340c9052507220b00c2480d022062200c440e1003da40300d0000150012040082080b01d42251302080341c02d01c01600c2000720400d042e449184104500006086085043ca0b43c05a10401800d03080e2950001c1042098204540c800510b6081000100408900000005100140c058150b22501e550010401400b40d580d0780e4070981000014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 653133803 1250 653132553 653132563
    0xe030d141905060a0317160b011d0f01050906041512061508030406030f0605090411030106060f02060a02071103100b0a0b09100e1c0501020315030703150203040503250203 75
    0x1090714000d08000603c56150361311150302042e40c1d00001e803801d166400360901301c3c4a1241c00c01203207132140c504601c03030300b807142da42441c5040b554955a184081103808a10252280e011980c0c1079200c56454018401b5080c00700140c2d41c0640c010b000020780342e03400204601d05003c0c42d44a10042039000500c1e40c10440203000390a158045030860702e02c81401e00100545900403405000c0415a840311400c0390702c00550010002800042c10040e2182828100244458003580d2316074000e6081540000b2180e100b09407010001809a02030502a103d1900000c0030350f120310380c2a42c140d032b4110552052980c080c403895010341c191040000e4a1880803003800100c0401303900142ea21803060081b49055104d0141b5050916a50320f4140e41c40000000010b000400389144005010100e0050404000701540190b01601510300050342d04c100e6881050382d602c80600000708a448000b07072581d54902d51b5009581c0192140003500c0c204821084509904d601c401400384000001c003007030009508003400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 653135053 1250 653133803 653133841
    0xa0e0c0d0b09161a160b01060201051803030601022503080f070312020f0d0f0f020a022a030c12010b1f0f0c03080c0901020102040801090803010f06020703020901090e030d14 76
    0x520110986000402d2040300d5000400b03011650300040c9070740001d600c1d00c281004179a4000a00442940c41d280024001e00007210706441041c02c0200f490588000001524461101640203040c040c5014424014070601e035200c001200d18031020103c0021102c00141607403040a1003525140c55141c10700910a80900d1005003c0c41e00c10490981c03007115800c100ca0072001c00000100300a544446400020019a5003c1c1c0703146201055030811650301058804076403900c1102174034121807502401c2e021644081080380c1c90b40c40000410514180198900c41580d881c200018004600e100441c55220114a0024040c03500c035100502654010284000c3d805d02803a010503011159035001d4124913002d00b02c00c0780074601080208042e0b200350101d40191a070782009000d20906490a449503800a000701c0045854161000c500e152001440380c0440b50014103086040e4070b00301d88a4018460405001c203140002c1119010300300301c0c0d00600d249040f8501703d6030344601d044100015040c0145c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 653136303 1250 653135053 653135083
    0x50c040501080c1c050d110a02030f030a03140f0f060622030b0919030e06160b06100804033e0a05120a020709050a1404060c02061803030a0e0c0d0b09 66
    0x150200041200011034100d030b006d8604004604c402d894020b80e00d0043d6519009501d1f22070f001d000400c1c2000400a407041c40000d840c20b0010700600107034244110310807648561042d12440000d0441c180441c4080e400101c0a005d042c0b038680380900320502e1195001c03900b20200d400d040d08008120069003c140c1c007682c258064032f02d042d41d8841c80000e0600301ca03c00380800c65610303820295070762110304503407040c0c113205902044c03486a80b515045400c41142c211707100b4000d201ca9981203a014001c002c1c8036661550b40c0c08003845102c6802c0140c2170030900341d03840d1880881340350240300c400c01c1d00c03103860840c2c101e0051550044034a000c034603000003c110b002d42130006102d0042d1050b0002802c6041d1030502170081907564490549038020030713503088600c4840d8a92000e000034841503a101100440076039017a1500c41d502c4200d00f01e540da01c0802c80e002150300070000200c0440c5983d1007082d14005110641d06a00c00038400100d003009070800640b41003801c0010300840ca0020010304c0789c080202 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 653137553 1250 653136303 653136349
    0x120717360907270e04051006060c060e01020403020d05010902030d111509030c010c1707030c050319110a03230402210705100c0203250909050c040501080c 68
    0x3001c10300c00d40300a070808040c004685412030402c1d610301d03031000c26080504144007502c0d6640c114091018810390f0207803554040c0f04820082d4403000c5c05800290b58140d222800e4540d81950781c1d40040c90702c0c00c21260555400e11000c001687d48200002e8400c1c0a8400460043e000303004250408100e04101014000d908980e46120340010803090f2101d91091a20482982c43d821658258410080d42120359440d0080445030660411514a0351002406038440b540c1d49240c02034040368a580c04440220310244009240603584682d50208141080c5011410302032901c812501074001805c0040441d403540ba0246441411144006c1e4212005069151504285d00804c0d6901032546100030108683d801a00b1020000c0244600030301d80035108107052140044001c0101d160608204c0c400c0c010b40482e500c1080401c58402d0f079115030401d986d02c031145407100a1001f0000c840c1c00303c515008131204604c1e0b5079200d00c2000d000703107030b0200a4800d000c08441005442460804044804108 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 653138803 1250 653137553 653137657
    0x406110c030c0103090201090302040c170f0c03180313060e1207051804030c0c08031801110c101701032111100c171006180602120717 59
    0x4250b03040034402e09000841e01d0740ca0004035080780082d08041e4100e410022240e011644c45100c0c51480388000d01094240d4031124010149004203035007800241d8814008200000c20031070400825441200c102c1e0f14290740b0100384a5242c1d404e60042d80401c540311609071150416041c039050150040c4060315102d0309210000d0801056000c91000610312400001c003003600414580c041e0640120303400507880d5840c0c002550701d0f0701c5084001c060414900c03240400d54081d2030000c1607140c1c140c0142c00002c1e0788c0c0050000301303c4003a120000f00f184013403a80b04880b180ea1256800303180502121034076100581302d11030341100441151020000308140c030b001c058401140305228132031900c9020a481c0d40c8008100c0d4903951074420a141c1040300c005218000c040d00c5030354403c440840e02c07906c1c0c541c0503001c10310302500d505124903405138000e0305414021410710001052090f11818840e11101180032201c0e4603174001d000c401d00060821188600594030780c2c07404145003001d18801c201d424070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 653140053 1250 653138803 653138809
    0x90e07120807020307080709020c160e0f0403020316080d0b030d0c080307090504020d2003090a0803130507081f0504020f060730141201050111010618020406110c 71
    0x30000401610364000407403020115501171082c500280b1110048989903625403150310003d41c820b01040c00c8038440d107000c10308250b008416520032124030f00184019907585400038508018020030031402c41c0810809000c10405640d1400d100500450f8030644a9010f01100012144134281251295100c010760050f5a50300490080030140d01941075516505c0c0c1d110140c49013030094000a90260011569400200d141e0b0310070340c00300038413042000c164510680030f10103c1c401940c030309901c0d0708442c030000301141e20680113541001d007c06869035814036548485081085070341005185802400b280324a00064a0204000394180b1008000509090380040c2c400014154072a0290402040304401d2160310014891700500e80c004401c3ea140119243c014140c55030540792300402c01881c0342100e15420101600c1c1600340350040807501303908020045d02c400d18000710844280d074071410701040031844044100c9200c09044000f50f151824014043c0100310700e0004184e00d41d11041e05c401c1c81c0d503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 653141303 1250 653140053 653140079
    0x7111e0a02060703030209060f07060b0a080d18080607080708010905070e0f030a15050105100e030c01030e120a0905210601090b040e03032401020d020616091e090e07 73
    0x507504890300d682d80c080074507098000e40644c091290344200085445038081081e5002400124465003041001130051802c104902d011406a621694010070b8202440c5000d099000560b00d80c0e07001d0070044941d101c0410780340401c1203030610002041882444a0141c20008241c094000200140310b18901000d000341fa03000303e07000c018030074540d000303c141090f00c050003241d4040307030403e071010f000282038280c40e8045c02082c4956806554400341d03000c032091040411610a00c0d005003e09803403400303c0011070241081d44c11820603409080c0840104071010802811034803001c2e260304804a2812040160b5100030b44175454200490540d108181c80d004140c0b00c1c1903070800480045d410300f95901003001045500700e0071030188000000c1c4420a00342ca03904081e8003001450703200a403503040c0012612956200c820401680c09000810218170050500e07205101076403410218059a41c011005001707180191100c010240c0c807030521001500d070164034a200b0001000303000141c5401d013851000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 653142553 1250 653141303 653141323
    0x80901050a090b0724091119080d030605090c07051e030d0c03150603061208030411040f0c17190b060903010203042906010915110607111e 61
    0x803000460956050050701e18102030143c1407440c0b034031481300c2e02d88544220516200382c40c130400c10f500b00e25051032182c0205c104e1543d0011071888000d00e030100b44000d2070502c0c200d20540d80106200403400c148200701c8062540b11b540c0d00454058904010321080006c080c080c0d00c0e01a00401542d00814000504040d050a501a02008a0484c2c10740e007411400b5185442c1c0d41d00d03043c02c0b030ac04421075268002e1007016903406c1c201c1300c410340e03200e409030216203561003201ca6100c05000f090b401314079028040c545c401e004000c203c00da050518005000c6032031640e800c29880d0b0f52200302da1032840d8440c0c40000c400881400828085c00d241918070000c2ca540c00c41c419061307444a105440c0340e01c1d4041582c8a1417000703030080d526800c00d443c0c401c0b0307602e44040d94a05904d00b00c500800925017500c8145014a00c1031f11501b2a0030700f0200001000007144941109100110f035018403426010854030344581107643d110024074002040700b501b001e084039100300d0082e000b0360301100718150108401c20a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 653143803 1250 653142553 653142557
    0x30709150c0b040f0201090302150d0e06010303020c01080709050406030803160e0f040c02030d150509150109060302091f261b0307120c030203010501030c02010203160e0406030f060209040612080901 87
    0x100400c2440102e0710440190002500b101001400ac034000c941070001e004000c182c15014040300840c22030741559074100748400781c0107034807105609881394055910580c2100c43d51403e00c0e00301b40c446000c501502e4080e481125440400410050a010b40181c11160307500c50b4540b0f8a22800208005240e000000242c64483c50b80c40035510b800c00e000708100c401e600720920080c4200350f0400052003041c1010301c26140100743c07400004100c40c0a900d4010030321035058603078512850400b44120000d400c034000b80c03908002d558005200c100c444650320b8100c403045a03502d4100300800f4040e0070040000c0495002c01240741d409010f0708500c0c100784038841e2000407a0b40c0703469030340713014003100e052080b1050348911034a00304a8240c0c0f20380c503400031410f0326420707282805101c0f4219401ca00304d120480e80c00781c6292440c0071102c03400740300350420000d4440080021410503126161405400341c200c0c0221a600c0d800601c0c03030080d00b0140142c4004101020804a4000c41601c42d0310603449150141e80c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 653145053 1250 653143803 653143823
    0xb0906060c0309180a2a0e061b01090c0902132d1502070506030411012d020a0b0a020403080a120213030318080c060417030708030709150c0b04 63
    0xd9040c01c1001580c50740c0c00c0c010701048007444030310600703040640c09450b1302d00341c0b50034003101c0ba9841461840d01e19100c03e040100c8441c3c0358000d00d0898220f000c0e00b14441d80240200454216100c002540c0031a56580000008d80c031000c61400300200300e42c1ea8850104180184655944950078990310380450360801c072100349451540e003854a0320000804801804040e0040c0840d000515448138504107a09408030780000e034440f070800190340000c4600428141070060b031030010f9407080c4090419403107840e5286403601e030780d51880d8200c0f83d40301d803800c80140e125150b07040601c01c01180e002c3e00482042001c51a0505603144c0c9410b0f48101c1d17015005000940d00c2c0c0f0b450041c95581214131307062502c1540711404d602c03403600803e0788104003c8107020750502800070907101004034100340c503220000c10440c9001c0c5004401a00c4030850f45807645d45010902803200420112001540b003982650b507213900b41801c1000103614014210445c0301084a03000c40700c00080c3c41e002c2c09603003040d004140e0032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 653146303 1250 653145053 653145067
    0x612070b03150a0e10090b0a03120c08030c2203030203040308030417040f051806010806010f030f0507030203240f0f0409020411030a0c11070e180307050d090501030b090606 76
    0x5068202003805540c0081c1d40300000a0b4034148061300a00440c140400c50345219600d41c01070041d1114031490710f40c80050302508100050a21321101911a0799041400090031280c441050036081156242c8403000d0003e007465071817040320740012540081d51404140a410f58a0003540c0380200e010081441c00001302203400e0200c02d00da24003c00780c0c0b10f0b0799296110b07250300007146020ba45100da2401010842e200b451028480d4030120311030031060b90b401d2090f50304c1400442308144c0c15a003100505a60b2007840820f99440d0240d00d20444e129140940e032414405000d103001c820154110071030b150295020801c0365607a40014100c650211071002014070f040d40064020151454000c0d800381c0f50450b00c074140340d03401028500c1501c00c0101042644440c0390262109001c4485d40a480d800c081001d00407002c05102d12a0407d10360788040300f10b6421414800c1c170f5948000025290343d4000341d0780307151840c0d000c5c0c14113014000030b1805001c10030140b008103280301006401d1611828004c5034030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 653147553 1250 653146303 653146321
    0x30e041104060e0303043807050705040b01050c2d01141b0703050a030b0604080105040506040308240904030512070503061302120601030c1b1401050a050403020a14160803120612070b03 81
    0x70031f5a20020280036940e2410307180842d5200c0451045501590400011104c20360059080d0b4030b610314800c0140c49029a81c035640d01503684040a4400720440b0540704106400302445102d0030202c6196000300c450512200711015009042a040f200d000200304550001c0d03400019500c1603c2d060602180038140c0780001102400345422407900d56103007070104010f10000240d001e000b207019882e100900c2c1c440a0f020780c400221f00003920300520300d0510703071409400c007a5200e640c0b140c02407030440e040c4a2490907040b014001503510100040307002c010b001c3d0b240382c420341c260f05180c40c0706c00c00c528011070751812a20003400200704506050740e800c4421090360080c2c3c001601c41c4c2011a03039026580461901d0039249004c0e0141510642c6007400055803c80306105003401a505500148942890740d6200400455100154080e501600a81303001e280c081c60406805040403001440d1190004220754007201402842c031031140c0c03058180c03801f1240002c00c00340280c9520b03080c50b0ba6a03a07030340c401c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 653148803 1250 653147553 653147639
    0x3c070506090109151806050f150618090406020d050103030203040e090601030b0612121603090803090607080c01022803151518180e06240d030e041104060e030304 71
    0x107046c85040c6070801080e40401a045440b500800300c0d091007400341c02040c07066070b01038a00c528103141081d040c40d080c1c42c6012041151f001d03106580242ca17019051990900b41c03007007131740103c0240c0e0002c1414010554940d10700360b801b12802006110300d44c0f5503220f00800da000540f54038003c40e425060b4100101d42440700c41c0d44d0318140b500e210750700c401020301c1e40b07001c4a00ca102600054661440881e4884010044138402107004210341c0c100300179030712598610b90042a1102d01e079076003042b10308181038035101810078080c1226a400c41480a0003005001da6030351003131040d880c0051010030b2142c4e01610f43e14a0045103145402f201640075a108400003501d2500100080440d0003c00e05071212103400c00034000b51441c0c02e4408586031690f026503200c4100c007210842d248610818241818101250707d100340c06072901d10406100c031000f250494245810994206500040512a15400200d04550903105400844c5000d00e01040040c0310000540101a4002980300032042c000421074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 653150053 1250 653148803 653148851
    0x41a0c070b1512070e0f090a120201020406080a0c020601031103160f05030d02060f0115030b04021c061d160e030f011b03020406053c07050609010915 66
    0x20901d0300600340849110000c5518080040c81403100c21002004040c0c003083d80000c030303404c0710f44013180b03034860031540f400c04d8600800d041c480b40700d10030768600401d004802e50000c400054000507511410304a00600c1c0c800010059440d0600784071107941515400100641129040003081310007d454600107420142e50400f181c800200b401d1001c14414805d0710385008946080b4126100c480c2d40b00c800340c2e182c0c541254032219442141004100e40501b038615901504d40c0d034580001c100007018005012600300c00c0713800320744180400102c01c41c0e50300c5204203009004104a140c0e1044840c3c109142d0341d0800524a82410624039040740c0804d019800412100710014183d41e0054100342c81d460080c002d107219801d491840c1a60014594080c0c401c64056680e02c0d41c03603602c1d00710ba001c10003c0d141039000c15280c0014109a2010549248030000000107000c90862035542509040403440c10201034100c20099140c0340000300043d10230700305030302400108400484c40c2d8034481e041102c1410524 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 653151303 1250 653150053 653150063
    0x509060a14040f0e0d0e092a0f070803010909050c03030f04060c080705010507050c070915030609110907020a0204050114091602030d020304030804020102061f09020903070504020d0501180203041a0c07 88
    0x1085c04000550400c03400765845000791242c86482c1d940405281c0328000080c0008050103000814211380d4a6000040c080190400003052406025a07142c8610344d05c2680410a0503a031001d4003030400009000f61038004804030000c0d4284040880000c1c01072045105650138030013180c0e070710700c00c01004100744da0290790464020016403520102c0036041e9401034a5484150088902c01305850300c051140d480d1403402c5421810b4802e0450ba034400042002490680d040c4442790549030460f901c4106040c8a02c1c080d9029140b0091a80b040c0300507a41e06811a031401a508074000d2404d444010b02c0d1680000000e03004000d103119518182e0a601c00c4802500311107000008010600d9003068a942c090b5100303a080f07d08540e50052040d4140c1c0c0d04081108070418111410000c141841c1c0180003200c0c8010151002e0036034550000b012684441d81d8040402d032140f0042205401c210020b00d040405150103610b90310301507a0341d5501040c1d0302280200b0b0560640454100e10080080e10b803c10b502c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 653152553 1250 653151303 653151313
    0x6080c0d0c0902070f14030f0301050411090901080705040c0203090f10140403080417011e0e01060e010e010303090f150c030c140a050f01231305060403090509060a14040f0e 76
    0x4c0c1c02c2ca841811a6400c00b5070303c0040d001180401190700004550701c6c070500c40200c900796402d040400018101e02001540d40d4102030107800c1130f031350b80d040e02e4600078800b0f40c000b4402103141409110035142c0e10060703801550000c2c48121803948980a02c0700741c810701154040c04042c415001550301e40140b41d42800402004580881008000307401003017034900c500c101a042c003540002c000d0a8840710001c00100400004d5030303641e03104040d0000c0d880d04826000100f245500c2d088030a2400d80c09034040d44808610800410074107030440721200280030811100c050650400140d1034411030405061000c122070034070b8030785c1854424813600541301d900404042100c000d140d034403981c83c40d4102c42901c090195007107064598805108684280340750020800e00d800401d40741da03806840017860143d03071542184a810024005000303081c4500e1080c2c0340c0f2070030b00342040140000308a00900e100c0c00303030b0721501080c050031a40700912103480300708550124000c43d604480001400b00000d01e1013580c421 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 653153803 1250 653152553 653152567
    0x27210702150d05090106050402040602030a031109031f0c0e09040b0c1207050a030e030a201002070c0305063301091a091c020a0e0a02070206030a05070f0306080c0d0c0902 75
    0xb00c0c1c2001d8040c02c030000c000d115040c0c8032000c100c100c0c8602d100d24000b613802005045181d44c0203401c5180e045a4050078941080c032041d020030f0501030354101041c0c200c3e000c2c0703800d801a07070518850039035082414540b54404411403400700e01d04090103800035103034482030350010300f500e80c00008a681c2d8045010b40800f03181800c1d40094402d40050004c07901007804c00c03581c0308a11600200351a812032070f568520506da800000840b4102c0c4a010714078800d80640303a109401c810203400249002c0b4420500614100c1ca141401c6040a074003610060012100032400519140708400652203c4040d050032150202c000e00162150b15490303010300200781440c4840ca070303540e2305030b406004080f209450807800e0070b42419910500c175030020700c0258450700100060010381c1d006a0603a03804401c0480041c80c14020360001607658104030398111410b501c80301004010b07584148280500b0003142000d003e40c608180d04c007900d03244d48130800d5000c1c010400814061100b0400c104000305400d076800c542c0d4480e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 653155053 1250 653153803 653153827
    0x8010618091b110c030304060509030a020d110a060f020a03030e0a230c0103050907030609020a1a0301031505100302150d09140f0a0b06010c03030b0301052721070215 73
    0xc1142c0150104414500c24909604007090800682d10020080c42c901030809805641982066130030a03050710443c0c00c46401a21030140c9a0a107030700a0b80c011043c0c044510810038000b8031350300820100010b803602c400c61281c0000c1c0182007031741e040c1408200f29000e00c020703516141b100311b0050083d802d1004081144e034585412802400740d210140c404040c0301c00d0040d0152401580d44c0714099005440404c04078060340d201490b0300344028501c602c041c2e0f48030440d0012010a807042450013800100410030060441100e2442250010050003240340840d00c0b45504916840007038012000100c91742c0c95501c94408564148810070401c11218809080051004c586640b031044a0309c83c80c1c034132240c04200050100003541c0c0c1f107100c504190b515000111402042004101e0a140e111410340300307169000c3c041c151146c410010303407441440c020006040d088200c1c842c061425040000c42d02140d000800319044d001000c100442d61310f012078804100d40d90009600303411ba208000c909440742031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 653156303 1250 653155053 653155091
    0xc010212071101060302030c10020118110307051516061d0705030d020601081e1009052422140a0b0f0109061401180e010612050c0a0801061809 63
    0x601e994410305001e442010362400c0f03941c5800301135071590006103002c489113071001350310070364905510012603405007100f1618080c100e064012204114000107042041c10100080801840100d840450405c030f100640310162140c41c001d8500ca4865400b40c100b0300840b50400a03e03221102da2039820041c0c104e0000c5d845004500449200380161860001c00620004a03141640c002d94040d022240b181c0b0428040c012040c51402c21a0240e020001826001c500c11010414010000343c2058440d03412030203c008141090700d140126800103114103c5400b030500440b00001e28103200640940c1c0c03c045005030030601114006100d43c41c8944100080c051900b4054001c0414038001d03a40c03180e101d101a906203008109417405404544a842e6100e80114241c00c1c6900422f00366003600c402c480d0202d040e007604800f01090903007842099000c501d20801e03500c82d2400031030a04006003140014645901031064030108645041054446000b10300c5480040640c1c03070040282500300617901f06d1034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 653157553 1250 653156303 653156311
    0x515090f0a090207210816030b1305010e0f0403050406031e05040c0515070201050a140d0c0f020705010e060702041e020406020a030f0c11060c010204170f1e060403030f020c010212 79
    0x130384803000640403000101035200c007a07102d060710f901b0800c0d550b41045900030b2801c4443d010405032602d41105036502c6582e8998a1214074000208966045c00c03208000940091300c0500241d8801040101007640441650151f0340b25140114140300500381c5c0c0101d04c1441d5560102c80c61a003400e10003000107800b02c080841d001500c1c0d40e41c212135a1000c8200c0d0b4003c0800180c08030b80c0420021051611801e4000710504400950ba41401080300d04d1208507604400c4c08000300d030080c074100d210755404008010040800340f0f485400007081901250060044840090065450b1103846007180903da12000451000c00f4045441d00da0300c0310029612403040c00154003040380248604c0c0054401d03020608455040240070000c02300f030f0000e00016600030340552803c0d541c01d200c0861014001c01280b064099403070024240c6103290312103030703040c00e801003614504200d03002204902640c010400a9010b601070400040305400310841d80060302c1401d045001a5100246960b002c00380c803d511401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 653158803 1250 653157553 653157563
    0x40506030903040f061809090f0609050a0606051c110604080d090504050a0506091528140303030f130f0b01060c061d121803010507050d050906010515090f0a090207 72
    0x13820740d070b000c05844102e01c1c4818650854184681884820200c0c0c1200c145544140001c039018402e0303840320422503910a1040300c042d0000c089120600c034990080c03c0103402d00310350160090802e0741000b01900032014004220f01c50f105500c0141d660342e60103480061032480103907241b00c0c055600c02040700180c0e0045500c200e1a060102d81c105005d4030070b0b28480c00c400b400c040a581c40c1d07000342210300d480051440d41d201070384265101e8418100640e2003030b480c100710148100682055401402900b08001d5103010703078000d002f0072800300c01c0901c4864222144106484150001c0d04004034400e042400152038045002c0000501d80c0d0b1003c5031030300c054000d0300c0810115100200d05202040124243c1640390700050261003400300040081060700e8504464030341c3c8126803c0408d00b0344408841c0ca402080d0007059107004803519002d05540300c0b0717082029003125810100000e500d418a002042d40c00003002c01c4001081c5c650104007015004000d2040880302c0c1e8505070503001c0c1d030019108440c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 653160053 1250 653158803 653158829
    0x30503040c0b0f2205040615030e0f0d08071701060e1201060b1801030209120303061003090201092d140114121f1205060f060306040b0a020a030204050603090304 71
    0x10b1841400810780300f80d480c0b50305107245044000020308010008044800010f250742c070070300290a5443d8446c19000345843e10074440c0040341c2000c0070b41102d00301c01100d480381d040016940c4640402045210881c03441e810640304603250180100d034000303003641c1c0702c2020513620400402e665400515815814000311000340310003c1d40031350765080c1c520740d04c0703035002d00501801602901c400403950071520040c185401424201e118002980d2503141ca260b0f080190800800e1020504005121280d00c00349030a0a10141510743c0c0003d201100a2054030619000c42c1c4100c1031f06908040ea908808803030680e556000d90310342030100407940e20780325208e01088568035500070000f020000c0e980284040140c03041c0329a500e01c10910341d1007011011905040070400f003c81d10249410f10300300018080c1d03008211a1501501002110802600c1140320354444005c010000d1070083d1115032003e2030400c05601c0d95003400c0d056003c8d010350303000540c2c000000302c1044281030b0008050011540d04440c0c0746 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 653161303 1250 653160053 653160059
    0x30605040621030f0c02040f0e070b0403080306043b0f0718180b0c07150e0a1704051012050711031912050408070b0603011803030f0e0a030503040c 65
    0x1180c0d020004003044241202d02c003070b10001c01d00030102c441c0c699140741441518070006a00003000c880308035250005c520f680342c1040701d100e038042003120090805050100e03c1c160035600c401c4614080108014400c1d5101c54a1109208000140d18010344408082160009951602e04045901114003134011b101e007e20300500b52034009081001c580c2601c01e20100c002d1001450340142c400d81c1d0400f50ba5000b0500558000f806e00507009205000242c400398440c4150300e1311400320100701010405140c24040d406802480100d03200701116408181028040c045090144036070080741c1c48582e00015031007160042c107070017184203d074442500000f000b0903030750440c05075440f0f007080f088540b40c0d92003400b0343c9050310f07501460b030400c1c5099800d00702d1151229500002c02c0e5001141c0c1211000300c003088545c01c000c03c00303000c29040001240240b000440c9208849040c28841201404040c1c83d103400c0b003041e0509501070350011048909860b04200c8605025105d5482960115030101d178442c000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 653162553 1250 653161303 653161319
    0x31206010e0109060e03070b0a0f08060f010836150a020c0604080309030c030406110f15130f05030706090201080a1a0d1a190c030203060f04090c08030a0306050406 72
    0x29034881601611610b900c1030030138008641040b100810f40e5018480d102c004650f00c60035078042c1983c0161035503421010010314200602008000c0c020350f010f905181848a51aa000b40c042d43e03003c800c060500500a2401c80d180a802860020b68454100c148900d06840440810202588101055000c40d20344600f806003040380306211340040c454002e0790100700090000c100644c1c000c060b0301d00326400c21000303100c030711b007154003a91042010032080092035242c41c00a01c5151b04918110000e8000143d13901d2101c849401c00418047c042c0c100c0c000450104550b841d08048102d0304902126140c03045440d01d03900801d0444801d03400700b00100001100c840c014000c4200500f200d10101e1110840e0030180700041c030000c031b170441d44071040205240a000b041c140c1c43c2c1c4030f00c0e0b01c1d422800014092460001c11110050384000425004008202c60303500c40c0c0b0144950fa5600f80c40000381c1c440d90781001618403007107402007519400700240c01c0c1c0c1245d80c150030070000c3e21070480b070401c00780d80e4400b55 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 653163803 1250 653162553 653162567
    0x60f01080105060d0509030708180a0915150504080303090102030109061a0405011d03010e06040312060b16030c0f060203010f0e16030e070506070308091b03190c05090903120601 78
    0x207101e43c005410000c6403101c040542110b03811a0700c0d2000c803418500542e17680b8100341c0282c848141c55010380070944e246407405910000081c00310000400c00c0c401c851824401000c0030f4069950950081219603103601c1c496000c81d00103000010a4036240d080080030f0728041d40c000e126610f2a04c0c20a030000c41d40c0d500d08003a105840c646c1d918500d00d0f01c0e02d04001540d1070b5016440d50009032407041c0480020351800c1c05408507060500300984402d01e46807401410a034600b40c1808429450848144106c0890800b218002969a41011000d0400745800c40e907484401c03000070111031140705071008104003a0007640c10303201108030440c2282c0e100c2d244000c0054080702c2d03490320020042400b6168600036400a003004000700c007a6070125032500040394050340034010480014a05208010808200340b001c595003504002588c842140c40a0000f0f642d014418107c0c40401843c402071030404c10101030f0040103000c0a801602e8503e0143c074a9a240e4000d090280c418001c40c2c0001900c961240507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 653165053 1250 653163803 653163809
    0x1d010512030a12060f030809040c020d0f050c21180402070206030105040509100204061d100203040e0903090306040c0e0603060c03010b0706091406070207081c05030910060905060f010801 82
    0xc0114204104480201c9012521070207902c80c9543c2c60b000130031800040c0011901860061403015540c4803480e00344822107269404070030454000c10445100b10340c1c0081014038070342d007901d0000e840e03070040d1400c141031005201c4803040c596046440d6608c95001e900281c040c210795480749603552219a014007041e4071500b100254441010401400f492030140d200541000e0020300700e0342c0c820340604074078040342d00135000b01d40850701030058517014007846d03c406a00a081034500d0505590f4a80c40079640e80924040e1010b00090100022011241007003501ca162200808960840c1058281445802d03494051000603030844000201c060a000580600814600020600d10380ca480d80c0d41e14075410550089905039100d001500104902c0300c0c0e004280c060704000b42c9214246501c002e0700d0103000d0381c400c61131608550181c10070804500f003400b031114040e04007182da965403e8000360401e00300078120081546498400301e945040c40c0d2107079110b0081a0340d204044240c0da80150b0741030100b44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 653166303 1250 653165053 653165089
    0x30c0304060f0906170613020d150f2301050f130b040320010815030f010504151413020d140604050706030b040e0a11010302090916030f2705161d0105 66
    0x407000c90840c1c10810002c84091900704001400c0004038020b07803056814940b140408034050b0345052000f07403900799025004008561000d0050f5533803120242d1400001400c544c10310a022989a00c0c43c00c00c4e10840d43c40c800c0c00701305508483d0b100c510103045d42e040360006807003d4856800743c1c0410302c1c42140c442500c1d00140c4920820f5503074120414141440f103818103800d80510515080c1c174a0090190728007540c41132500704418100203036070404940c0041d214002e01120013003403001220100481c2c04c1c0316601a28918102c55482c204508910201107503e03403107201d12000c000910002040700d20640d01d040d903007448646192401c10094450328100044070390000d0825100198440e40c01c4042e00e20b041c1005405c0c07111200000d850070380b0841d840691840c01010480f00c0300c0d8503204449086003180403c0080503188800103c40030a42000502215643c040a02c240141001000d464a2300074065180e4603032580c0050304000e9110407161686200072002003042d00c1e190b86401080ca00321 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 653167553 1250 653166303 653166347
    0xb040b101d09071802090f09010b0703030b06130608090105150105160c080a0c090e0307080f0a200c0a050306090303040b13020310090516030203070b0c030c0304060f0906 75
    0x410700c0a070125014040c0e0315548a01c0f6030000b048a40202c15200c40800c1c2d04005840d10100418486041d82e950400d070312805003031005000d0540f82600b515141c07a01807400140251520020580354815044419010000c2d000c0001d0081c0d03200508502c2480d102000380442d440e010703011032142005409441c08508288594030518525000d8609000d0141708000003485d582c14945013040c041c000150341c5c994440c001841405924000d10a69a004800542c0ba25005407102c40c1d0703a0044500300784014030b0000f0700c01710f880c0c4241c2284400300340000310071a8801010455555982c03018180300d0003503054005c00120783c030340441c54510458181c0040c1d851655281e5540e515000020100404815842c072100e015031003c00800b203042d045154005010030715810198a00140c92510414000d2a0f090500040c5c5000c5034201c01c88400b000c10036121480c040e42c031429800341c1420494a8440441d0000751980d002d401441150243e4171212212070301ca58049404480d141020f0100c5c20f96 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 653168803 1250 653167553 653167589
    0xb040c080109021324020610080c0d02240c07080708100506150408060106030f090f02090702120f040e0c0f0a260a0b011b0f0f0206160b040b10 63
    0x6250000c00806000c0c103550342046499090700011140e17000d410014001e840039004109540422559800480d48548038084a140060565517205a0002540580030008034501103454182c070380e04c24661114952041340c2e00c0c0340c42c80966074010b484d441d003052003240c038000352002c030214a50041c2c038107400242c412a50002c0000000d400003900254200a00c14941c5054821050180002c5c2c140400500110f502d0311400405513141c010b01420741c54a01540503001504ca50b41c1401142d0341a80c0c030300d40a035a8414260b04215244820700303504240000c9141211030420000c0c800da66032109980280d403030f071003c5409036024009112140d000200081c8900300d000c0e8101d01c1d001a00c940f40710010b04011011008019410b84001c0a450b4a80303400e0910766070441c0c005030f110700e191103044400040301d4580707040352080300c040541380d130707460b04581030940d111101260843e2580b0a82c110030701e010380ca004100070b00112400d07500e00000c00041400340541d54400c0c81116444507000c184060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 653170053 1250 653168803 653168819
    0xb0a0f021002131e030507030b15090601051e04090213051912060b151c0b100c0b180d0206090613020901060318021f14250302070302180a0b040c0801 66
    0x80201c000c074100413001c2d0001002520400141011758841c0ca070824050505c44070401d000c4070802ea074240704080c0c201c00c01c891641c1c040300307039400c3e008290401900b4100e0301040001c039219540042207101d0001032440c040000301142d4a01b119030a55010091110592070400242c805004d80001c0e100350122000220710a90400030990340003c000303030304240304038851482035800a910390051036058181040d4103c200e104035034503004161290103012207081001020385007070160081c1641303044004141020341c0e103600007a0b00340c2a6400c0b1031010000080c081d58401044445188a104060015441d041440d00391403200b58007401e4011b0a07400c050701a0301400c5d03c282400380c000d5200c0001d0016a41e4500702d00e1745103c82d0004280c03282894000140102d491850000390300c80100045980c00e61102d10340c205500450315004100125441c0480c2042c2c040e620207548400d0b10041c503200c200844010b0340c06403401c0c540c01c0040d180703600301340010ba0f1505811100403800071401040119 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 653171303 1250 653170053 653170079
    0xf030c0c01050d0b21060a060503030904020c0708030f22080c0d06020d0906020309120c0d0c0c12030e0918060601231b0606180c070305040b0a0f02100213 68
    0x60f0030040c0032404190043c0810151100419014074036141c4000c01650f002c001c1c403407203801c24031940c0c062204a00b080082640c030303c158850180036680c0050305910a041c2442550060007c1d41d0aa968448101d95209095009040f01a002805050030582030041000d40c0600300d44500c0d002c0c040b501070300c2082080540c0c64041c10380e519502081141042c0d122407240b074901d07510070720700140c0760f08084000c0b91400a03104948012b0b400c2c10021982031000000c0e5681031003d191030088030000061402c650448426030101241e40420b81c40001019041104035400402c2505c00c01d0651303032000d126410921000c1200c50042c0c1000020450951060000164101c1e403000001501c00c1840c0408801d98414000000c02c04c81a0740d00c04501d800600c06a03811500c102c403d96000f502c900892034803400040e1128129960001312901010700031b03801c2e03078000c00085403080c0c1c0310713405075070013500604011143d0390043c09022062866920039100740da1501c0182c840c1c030b440d0346080441c101c45075 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 653172553 1250 653171303 653171317
    0x6140d02090d050703060c050f09130e160e070f050a031d07081011120a0917040e070207360627061220010e030f0a050f030c0c0105 58
    0x99020401400c094441d00701c4100543e00c40c2000342903891560070800201e80c601030790300040140421082c850544080c040d5042820100e4400407031542d86001d540040880d04001146030140038101d0524021940d400380885110104c850b00d00d07610000704441e202243d131201c2d0003044040c0b1585a03c140300764800c03400c1c2180d0805503203410510203049440d00c49a0b42c08280281d00480089240390603131700402850010103811541481100101e102e00002d0040034001300c20755074401c030b605020540d451400f14034048422a95540d40700c0200002c0c0314411902c1d24050302c510000004c154541035581045015030000c0c1d031401d2000010002c0035400c4c00700c0d15516590700e07480045000c4202690000003001c2c8540204800d640414910082e01c059612507020a02092070643c0856500c3d4201980c0c10080102808040d03019801030721000e00103c5415014031400b41c9809000c1d00000390803005138040c2d42100c03840d001c081040d596a1103880c0030500d05401820903209154044d2000c1c001d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 653173803 1250 653172553 653172577
    0xb090406091703010f030c080705030309010f12140a1404030f0e0d0204020c0c010906020a02030d0302090111062a04030218040510050702010221100605160602041d060102070614 78
    0x1202d0301102002e15002a0003a0003051403800081082180700e14000c0c004200000140010501e800f00082d1a4003404038414103025070303101c5c400115480703400441e500c0310070120100f2000801d4149000180000c588075403031071b480c101c0703030004c0500075450162003181d2540e01c40b040c500130744408440c50326501e010a034029081424000c010394a074006070080504101c02851a00b01110005081c60b055070301a0084d9044400c00c1070244c2c0300800d095041041c0341c100582e0718028540101c0701c0c25554140080d070750241030140011740d00c03605a0380310855440f41b4a804880204000e00e1300a21907444000d40c0300039600c00048515000401039076004c0e01030016030700e00340141c45003c010b0f01d0b41101e01100507580024081e0106540c11900140750402091301d0146d071900854034150880140500d0b414800080f40302c00c03080100740c1000070902e5000d901503445694030602c42032084078070200402440d10301000108035510000320b0108895143c2c0c0c904001203e042e541d0141540a00020341e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 653175053 1250 653173803 653173823
    0xc030f181825260901050606121b1b0c1905030303010302100c080d0e100c02030a11010219020321060d060504030c06090809040f0e07060e190303050309100b09040609 73
    0x201d0800205400038a04031880720801c0340b403400c0144c040c02c540c801000d60f84200c4041c0300030342c80100e60580c580d0740501c2c03070140c401403003000d52040201c1e4003d03038020424203803024020005441c00800c500202110581e2002c0c00d2800c4010b1000c4620098094a42c1652050004002520b428044103803141d0380c506001d850119240c807448142d03440001c0f2400c40d50707296204600c1001c000c1020110081d1080010401040b940301c0c02500d0380f1500c1c0c01001042030031100444001420360480f8070414a442d8400c071041703240c40000c1d480741c2055089804030144200f003c505d4015941e01c0d41d106e4900100480120aa581c6e514002400082d109404010403402c1082c00903607148107515880d4020300c111911038010802700300640d00d600e0112142d060605001e9103a076007000980400381d40e01400c040e041000b01102081c0400000412001c64804083d070000a0640060065000310324050588a88404802c003c0d01510301c000c0c1c42d20b03004070f40d65001401241c00782c2c2c130030082d80d0f1003400865 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 653176303 1250 653175053 653175077
    0xc071509060908070c0806061f111b030c060c0a030513051008090c0d021e190b0301031a01080a0f0f0506010303410c030f181825 57
    0x100d0380b21034000c58039540300081d8a41442020310a0500401d40c6400515052a001000c280c0780072104403548012451001c194144c5800b0300c038203c10348507a50084603044a101c8000050f4100c0a000241c0240680300c0d0448450030207604440b031708050100207068614007950100e807150b110715480e40300e40c1440700011484e503641c511071001030329542d0f9a0490074101000842e0914408030811842681502c40313240041c0c40304001e0f01609152020000464a14000400c1d0008135014003102c594031310803404602070140c640914140c030300500c0381d0300d1505411600c24802c00828001d06100d5809a01c03068002051000c04100ca244034071105c52031843c0e5a900c1501d0544d00707810840204e10b2220300d4500c4e00714003240b500d4007000030b07030070240f204030f04051013800703b140540d5a60001c5600003000d9803020410401c80d01c0504040d01100d90703a01c040d002c2242509940400e0600c580301040214020010b000d20080c0100c2c80b000e0100441c140c103039500c00c002407401e40700e80103100b0746003681 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 653177553 1250 653176303 653176313
    0x4030507060e011b0f0b0c09030a02090618101a030912070f02030303041109060a05090f0414071401080109060b180a09060f030c05010507080d090f02060a030f050703050c071509 78
    0x5101614441c03001750401c3d601c14a0003a030500c034002e088100c0d00c03c050100d1515a68005034060b040c3c0d8050740d002c0c81d691600d2000c59901b10700c0402501d4145d10020074090b9400941b9140422522952100c001c0c84100c18000e05191209890202c0035a011b100802505400b990040107864440d40641c0d107980c410b540402e055400071130b01035820700c0440b201181e00d803c0002d105a800041250807080c1c8600f8180010035410000e401c01e00a040c14100080c00c100300e00c180c41d9113000c1c0742400c440d91a80d441400048501c0449070450010309220b0000403440700c140204801d58181c901d01c141000f041d0340841400e900e14070040f0740d000086640010308030711903103c0c2c1000781980c401500780d62410f43c140042c9507100c40e030005041001c00c003c0139021800d28029a40d40e00e0401c400402d4dd1416814200d1003034104190296000400007682c0c02900d8056000048038105110b050040b0358480205800b1140300f20b4071307810904010440400020707224003054100385946080000d501c14152a2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 653178803 1250 653177553 653177597
    0xd120e01020c1305060111030415031a0d150c030614060706140114040b030a0308040221010c080718050a150519030e12210603100f02040f0b04030507060e01 69
    0x4450f00307984c0c0e1000e000707103940c0c01301c64820106c1210005528080c42c0252110760468511707100f50415944248400b41d54018051000400d40000d007920748240f01820051b565a006a0389441c0051800c503080301c50600900418040360b0442c0f0840000b446070805021060b4040350b4212425543c86204445c101c3c800803200d0302814080500c00102c068000602c41260142801181319900c0704e03003403200003984400e5490b4840e1381903621000c41c4000c40c041075018001000c060015508040030703203401580c003240e41841440c0a47c1c0d406444807098540d800203485501405400a0038103501388100300d03212924a8440340286060b43c0703405400c01d1400042e07940c111a0707000080c0c8500d10b282030040f003007050300d0813003011140151610b004050362034101c00110180100c1040b89500040c000d6405106581c500c100c0c01006020319520345003400b00950203401004403411408101280410f4428280d405507a4030000602c1400d0418405445140c0c2030500141004085049072400c1a04041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 653180053 1250 653178803 653178829
    0x30a03020105010602100218040902030f193f2609010c111b0a0503030a0801030605010f060e04020c0f0a0c03030206070804050a030320070503030103110d120e01020c 73
    0x300000380c1c1c0d410a08005c1c200410740300b05103001401401441c1c2000b4038440e50703080402c4121400a229052440440c0c00d201e03912502c2031481c000c943d13403101050780003000031010754480c60300e00c3c150008800d40701101583d401a00c00d0440310328000c088407500002c000c3e001034541c5041c1411000e0032902d4880011403035044084e000c0c64110700b40022410309008038440c400d100d0402c00e604024544200d0707a218408906265212003408120380c49803103000401c07025203001b50990b9590301500e00090181c41e03080c8003c4070f0305c030701d4400001240002603411409407001ca949503141c100300b10f0100000f031b4108800c0c0e50598000c0c055035584071481041b620f152035100d48a02000e441c80c508010303041003030040001090148a0382004009840850b086a000d0783c14180080d000f1001180328a0790541450502040071700001c2c10014040300101a5040303c0c410300703000cad070701040c040305001842e61803013802001c24905015000c602805031a00b000240300610441f80c4104021002654016400c6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 653181303 1250 653180053 653180057
    0xc010f0b10031407050d06090e011b030204081002030a150602160e0417070c17030c0606180609130609080d0b010207032f030d1701090902030604030f020a02030a03 72
    0x94000c8038641018100541c01001078103040110000349000e840c80b401c401440003081001c00610340c400c4145070303031040002d80b00303012080003c860b001142034001c2c4440c603d041c10300003031280b83e08040b500c41c0c002c44054a4008020348030800234400240042d4102901c010103040d00d941030124802e80d41c446c0e4070300034903250b40200752940048246001c90340454012a010030220800c000101c0d1019081c02d0a0108448000b0b0f5104040e061541d011074041d005200301d612250700341221000004060301280d641c1c142511501c1c0c0740d00e0100040030b864005402d400a402100050203071801044440d8170a0b180b04a0209084c8180d95000c210351020328101c400e40300200f01c0407200e050511810340354050a0000704206811921540070344007422620306c10410011040403411568000b0418200802400f1907141070040c01e005400c0b2442480002c14004c029000054814014002d02c02150b8014018054a0f1140c4e1011508001c00c60a803000394400c290080006860400003542e07007038000d13 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 653182553 1250 653181303 653181311
    0x7080304020a090507090b0d091208071404081002070302031603031a04050403020c0f030118080301061e140a09030b13021e010503180f060403020609010c050a05030708040204020c010f 81
    0x40d20401545641c0364003d221007514100c20405000e1b000004e504c25600d0001b50243c0320340100701c8038400340c481008002d00c00d154000d5440340d2550001c0e081409001caa4552142e4981c0b408010540c81c00742e403040030f02560107810300c0b008400300c82d801090703c24020b10549103410340c44207040c19083c000c07080440029a85000044010f00d0504c400001000f0446050100e81440d4400969860f10103068902c1255420404101540c0035400006211501410400f03d200181051038442c0c02c248034001c013207404c451032200c0d04410301c0c840406006e0140c8600c0d003490940344c0b11445a8000035450810312440d07400103c040780740e0003e10b521400d0503ea10198501d00ca20500100d01d00b00c1503094040d42a050b41c80c81070307a030003e040e13a600c079102c02541d545802c01c2e5241c4034036001070004100300d18087d00302804245540422881d01c250074202c0240452555588100c0b0b0790310404165400080052002c103034200e114088164110340018000b41c01e01052100050031507145080c3c0007030f91991 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 653183803 1250 653182553 653182561
    0x306011a21040c0608011202090c0d2a0314070807020c0604090b150913051b031014090709060f1e05070302070f141011030307030e0c090712020915070803 68
    0x500b01c0c484040c01d0103261004c861b502d000c0c121003841e0f0095400900c00c14105001a062010800a0b40e244400e0048240600c401d08002c850b4440503a0703490b0009400c0b01c5d00b80340456030107801540340c0c0b0390141511403920340d034981c0101d442d420041c0400d011401544c05001003030f5103100c09000030300614a00091000c00314400c01541a12340d034140f0301e061740180400e000a54070143c40580300c551404001c903d40e651510070721280e041c00c1116580002c408014481a4410180d41c0402d440c006203401e00421400303400c000d45414100c4030b07140024154001880058410404802d000c1e01a0070000c40c056480c1481c00b02c64958102180c000450204003e403e1503410081d41c0000d1440c4024451100d050202c0000e4855501000501410344404e00710001c5110701e6401c00728195910541c1c2e12810302400c020013801c280240c080b200e01c156500c410f51464008005030180070140c4032000c0902d2001c1081000e904449078a036404039811115a04d03002000008085681c440c00806690b031038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 653185053 1250 653183803 653183813
    0xc0607110915042f0702060c1510060327030c0506010915050a080a060b1810061709070905070e06040803120915040803181c0305150306011a2104 64
    0x100f103001c0f84c1e040302c1c6140d001140104200c0005541c280100c01c5165a14140c0c00840c000d4030480c3c0ba03440e00352080310340c860032110030450f80d40d0241c801c07061141d071941e6903610120155450054100308001003030300340780d00c56180c846414140603c42c1c1840280700b4126100e00b814200240c0c00154507a45a00d00b90345800c42c000103100c0a404201c0300c04007c0f03400d084607030ba990508a08010a4035545804004d12581d030003030000c20200d80d01e030800d4000d28148034218043c0f00188201030202301d583c0340e09032a8940c0859164840d2007914000c105103490504100d01034440a401a414840641944038494641c58002d00203132241c18001c690b1111300a141c0d00029078000c4c00b00e5002e030011514080c605000604035908540c00040e4a0b841c0c1d02e81200e0300c5400503180c1040502e61246100c22200182c00094204111403252020440b03551841f0ba01e40c074001540038040e0307064212a0043c081c2c02c0c3c0d1145141c40741c6c9170050113107007400501200d003d45014200007a40c0000d001c4010482000f07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 653186303 1250 653185053 653185061
    0x2102160203070f0f17120705030c100902010c020f1c1a010608090d051305040609090201030b090603030406030e010b040204120b0901140c0d0e0106060e0108090a02030c060711091504 80
    0x80e2080c4210b418900e0300c82c441e810042c80d400f80b50308400481c1780d441040c09013088400442079014444030b9880c04949803982d62a8080c4102d4092809254160b40703896603503200d0300e4503042e01a11454017032913440d03007040010118120701d83d51000c0c0b4400d04c080400e02e9011000000f0303108114802c000f50442c600000c42000580c4a202000310700c1e020400303040004038100d4042c07460b90038040e0f1aa03040325410f80c103000c4660016a0032500d0480000b94002d1340390890485103000780c8040103190308440134041c03c00c42c11158035815901c100000c000c1030b442035000151140004000203078411490300060103036400f66003d0100c01d07100b42814401d004030138901c1604100448001c01081002d40e5a61901d0103008000381c04001012846c10280a2170750840001080c0c610001c016150311010003400d042c2024409900207581140003580c1003e00040e10700c80316070002c0c028180d50304003504000c09940101022180240340c641003607965241d49090352700903820171041d460660162405d0001311 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 653187553 1250 653186303 653186309
    0x6061e031b140123031e0105150a0507060902090a0207110904200103180b0702060c0c0c12030c0d05130605040e0a0506011413061202030601080403110a051f15080c01210216020307 79
    0x542e50182607202271050240460314558070608140d602c2d0301b21424220010a008a0081c3d0032040510411801c41c0702a03008040103072003a400b1030a52005581484144041104c004051142c00d0b003d41d0400754015a90010305c010524021403c40c6011150f1008141c81078800c030303440c028070000e00040395014008140c5c442c84600659040a4034064641d03503901ca000c00341030040c0c94450005040801c28803c4512461160040301c6a4a200b00d8000385154002e4101900a0f040a000410700d17504c43c03c03c0390101c41c05290640059240c804a0318000c4c600540b0302c50500c40707491500210f80840c0d501038076205420b5064070450601d07000c009440380c01406030504000d0700c10400c1188a81e004a41e190700141c040c07030b1001810b10208210b51900c0d201c490040c2043c07142901c04102c01c4038551300050f402d11144d509016682109082c001d8074074850043e03021681041d80c010301c1c0c1c0e5100d40385020002100196000004a40b40d9101c41240d001c0c178000b003022a0504900b100f5820100410402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 653188803 1250 653187553 653187559
    0x170f061b030c181009080d0f0203181f0207050312030c180114070b0402190303140d06050604081b0a08030901080406061e031b140123031e0105 63
    0x10502640485500c922004024400440300070501141140c540442075840340f030040d245600800500e01d02a00305440c5104581c6580328000507101403038400c21b0603036200807180c0c00450610321440030310a403d41c000d6000ca0380080107440812022548299408000c080c29005861218200002d040c1414400300100300007074803c000303012141151a0844d0301010701089400c903050b41140040707c50f5039036485101ca419802060201c10301044510b40ca000d140700700d03076a001c052030800c00c4c111700e00350b18400580412654200d40f5402c0003d84001c0c5840584034000180da01d480c0c90000d04160495000816039a00070074568840050b43e040d49120a081100c00f100760381d280103d000d589100d20800b00741009000c80200d000c01244e5045000a8044160032810340b404140115038480f401d84130950720003080002113104020818540e200b92805c1680c03c5082c3c000410056844d6941182911a15480601c402444d11200f0020314024821a4441a8070228802003408210f5040e003040c5c0c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 653190053 1250 653188803 653188831
    0xa1d01030b011202070314030a1a030d0c030804031707080601030e072405090d06020703270501050f1b03091e030309190b03160801150e01050c0304170f06 68
    0xd05a0f8105100f62801c60040381d0150b900d18103071804489207141e214414042c0d007004020f0003c005403a4000d0124450001d07809413013412100101640e411883c0004400314058040c0c0301c021038880c4022907401402410404085180546001100c0d80c00700c4200e03000580a0b8144540c540c1d0500401c8401210240140481070410078460394100d43c0c101e8600071300303560b02c8150261130f0003a001c0da010660024032000d10020181040000b0790301c119000c4002805580e1032080104850706680005212002c23070036129410312005451550028480307400920b818002004400c03800040b0307008000d540b0000c0c1d52241d80b4801480b60b016100c61a60070001c1980396182001c5d03c0000991380c200d103003103890fa0503148070004400d03011030107a04448506080002041084d0794a1706140400d081103a031400101ea0307840910050300004029880005500340c0d1000701d49610400c00b40114540c80b2003501d103460b0780ca081c0d1a400303200011041d0030581000c1440403016400b03205856001000114000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 653191303 1250 653190053 653190071
    0x1c050303070203070b060916111009150b0a030503070609030c0501020a0306031211060a09060b03060403020109170906180102010609150f0e060a09020f1201060c14010216060b0d080a1d0103 83
    0x3940c11101601d050b00b0403407085442749504004004405002c901a01e0030010005135007031811000110000806200d42801c50504da20305000500301e044a821001860030100303107a9480c00030f4001c9000580405c8580f8038280c0204500780b000308250503c90700e00285891851034842801d0400c00088000d00c074005c00a51000740001c603d9960103002031000140e400e05a1520360000c05201000a805106a40401040640552015161500a242c100007a039481c91003a081d41c4283c1c102c1e00e8001c603082c4102d162442da400025403120b5414000070607072503180e0038418119581640070b4401c11455050801a100100004402401140a0303555040c078015010071000880d903c1003050007507000130b071100c402482000360342c18500000902c841e40d5035940700c0104194501d1109485040c180c01c0705c1d130320b5198144200c1d5000141540c80b4900c07482603468960007040303e2031013150030070304401300e2a0004840b140104112901d58a8060500941b080748011403240100d0b09414189030621030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 653192553 1250 653191303 653191321
    0x90207150b03030d0e0f071d0108010b06070b07030b1918050403140f0c030d0b03010e010605030601050d0c09020c010e0d090513020307030f06090b0f090c091c050303070203070b0609 80
    0x103410a031803180c0e004c10511038078907440d440c0c401c8100711420240681180405c411030740080507641d442381c0ba2000802d0303980710135450382203410501041e988448104843d50015400c2041558000d049007000601028108080750091217006660a030b0715088607020310402c410422401c80b040205c210401580c68a9640981002e60386407845041c80404940300030702d9001c5c80d0456030380c0100401620784034205c4d80070f0399001d1324000003030030b100b0350a05600c0302030410144181ca0403603c0c021300400039646030000344401d84400780019603200254401c007080e103508900080c0201420040001130f0181d20075402414055204940740c1002030325201080656038a503e01d00080700364481c0146d4903100c8060517002032004207010700030345080100010b038949260b80014003010040e20b41c81140c401d07001c20070081c80c901701c446182e00c0f0002d004d803401c6c0d401d100404c13412010007100d05840340e0500b1b4441d9441c50300115801d100507030000400c0d0b1308004800000a0b00a10305541c07212803414503481d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 653193803 1250 653192553 653192557
    0xa09060609060513300c170a03090501030b01051209030904180302060a110c15060108010b04050a1e0f0f1404090312090519050114090303010b07060b030109060204090207150b0303 79
    0x18400e042a003003c0c0d024092011614a071021000031005c009004c00d03502d891580a06248184015442643e83e42003260700049a1841045d40c0340c0d540b500c034207003010010b50060495080c001c1c1005428040501d49100e0324a50720701a1a450b0015034542c0550380400040e02c49201407008058814040240041d0b00010300c1c640042d5224030104414102011150582c01036400440c440e03c11408881251104103248900071342c0c00313903142900e903070b05c0310400d0506205512481e90854100740b81002070000650484403070104c0b9a044140c1d442d90350b581c1c081c08911030342080041c2070820008001c25038000282c2c080544040d07509110015541d10040c0c00030001c80940aa80e907202d48121082120500c160191314000d2581c11081081d18146180200550140d00c4200e0340c00d24040b882e03102d80001542d040b9a2086410b81c03811001da40c480e00601000c0440542641d21103043c64005050341c005000034250b5004010780342c0340181003030040c004900407c00c00352850023421a0081c0c0380802 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 653195053 1250 653193803 653193809
    0x4061209030e06031303020d0f0c021c170a121811040609020307050a030b120a0f081204080903101a0d03020c03100b0306010807150806030a020a09060609060513 71
    0x1800146514190800340d4240c0c16440c0102d500540000c1085403080f0b9220302c0d800050300903030803651543c100c400180c40b1000b0341e12000c40410701c00b041c020014544948102c9821915450328074016032555250702d4690807000040c2c402e01c4c0007040c05031f046540031602c1d50021144640138000a80300050f81d003044001404080c042104140484000d6100c80d00805d00410700103404650303070329140c03900030125001401c0304000281404501c01091074801078000c1c2c032590075006010060b62a60310244000444c40003101c1d007100038088c0c0c68200c815282211301c1140260040c070b954840366820503040c56085040c119840303180200502c018500400c007080e1030807040c1d920340c1440c066410203a14111012413855030611503018030031020320740d61304a00c44081c01503007180ca00d43d81f00c410268442c802d500426070303814101c10340010201c0c4130303102503030304031001400b41c95003401d95802003a84444980c0000e02c825881d8072040118540c48480080100340514040e8200f50401d408081e600741c440c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 653196303 1250 653195053 653195087
    0x80106080402030a0b07020303010611070b030106050c070312050712080f18070b16050c123a09150201151211060c060604050612151906091b0201020406 67
    0xc001821901c080204040349600b0419034001450130040003540d80d402402400001000c00400071500b4070001b940c402038884841c00c60341181c0c20204102c1b103940100414001034420300c80b00001141c88160200c000e00c0c00c0b41c0d0b420366502006e041440d642030980f040c007000c1007401c1e000c20546000e0044400c1d044000200c42180c0c842c0020642c1d4642101e541000d41c0318000050480d40084080401c0500700d0320030710540307484041105c200402c614100505161a40080302d0709100140455203030f03400300100d03261040310101642c2c20744a00e1185280722002054000c0810711200d0b03401822210104001d10080c0300010390b05019140b480424852000c0039000344986208000750b8180c4409141c10242c0456150f062145481c0d42d41c0b4000d41c2c107203003d1464500440e401c3c0c1841044860503c4c80c0300d0040c428a5501e0000e1003664000400840c502410303000400b40703860722801400c00074400d441c4003048880704a2502c410301d0305080109020741e841084204007842c0c10020240c04a1091 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 653197553 1250 653196303 653196317
    0x1606081501110312060f030607020619180b04060e0f030a11070519140a030c0b07151d011103070c170903101a0d08090d1103061003051903080106 64
    0x3103005980ca1a0002441d24003800b000c00c0f906140c80840740c0c1d051040508440d04501c400340c5405241d00c8141c10b40d40d510058000000194190804420342640303a075000d003000508982d43d1580e190144000c510440d20f0f000640180414403200c0d028100c3c1840140000c2c107104d0a600550b04e42d40d215a0100000f8001211500200c1380d42c144070701c80042c100540610365001d000c1038078034800301c4c89002e02404060700f00c0920307031f1900b001103003401940d500040142c82c0e50f08142c920849508503c0c0116507000515017070902030510790184000c0401c480016141161420500500703689070000d00b160b58840600030000039540c80b43c4083c038566000084030b545218002c142d43e0302d0740f0400840642500c64201e11055000142d84080806007610fa000c0148a8818040081400e4038002c0642407a20600400f03406240c8039a81440d03c9205244241300803402c640800d051403421214104460000348080040c06000d00c800b0300206000a89070640e00c125a0f03000c1c041000600a0300c0405c120 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 653198803 1250 653197553 653197591
    0x3110c0a15031803020601150215130609020301090c1406030606090f030703171c0b1f050717040e0c03040b010e22060b13060806040615030212070503160608 69
    0x107030388801c0d10120f0350501c20124090381d080180d41d40d0720a200300c4e50100040d601181c4002c1c80440c441000c0710b0646141b10f401e032030318024400c0071031704018143c1d0450ba50300407100050b07800b407150300301192084a1440b002e500d030086001c000c0c0d01e40c901d01c1340207080400421401c2c2e5660740494000d04030448085d9042054800400d280600303540004000e40e40c0d18401a51144070800030341514211401981da400b10750708a020709aa20212a103030b00000c0c0c03403042480c003110380d8905040d0800b141c80c160b030403c00903450311450f0003251759181c400d0a0b40000c0030f000808004800c1c65000301c00ba0052441c3d410140c2e03440034001c4052044419007045c40380030400c426140703403080070041c0c00c03070320035407035485803420420002d01910800620541c00780c403032203000840c00c0c051a0700b03ca05250282c0201c2e6039948030f403070103020603500759640300b824400040300580d43c2c0d02c5800701d8040c0150007002105d06050a151074205c500c0c0d0081140c0c02c401c8402c02030326a0041c1003540c0f0100a51001c0b0100c0302c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 653200053 1250 653198803 653198807
    0x30f040f0b010b07021c0b0a050c0d060f08010c0e01080a0e01020409020a110d1b0809060f16051005060d2a1403060a150506221203110c0a15 62
    0x100903000100940128000090109034400180444a0084900644840500c403110740310360207241e4002e0442c003204001030308502856100552101408582500d041c0000320240111a8a0b402590541c1d03860070051080e96001d202d07030704c3c5403c10303800d03c060041c2ea0000003800c1c24000900e04410315450f00310781c03080340700c003034041d00c0040607096015500c0b001e00c90800786c4100c6002000d40790511949030360484862107400100704015250400c2403005100d900c400030964000d40881d900070b10204016071841100c074004090004e4000300a02e0307034610a107855420020000e4031a1103040c1404140b02441d40c0e80008018076641c02124102c09402000021902c50198a6465001004d810b000a540344e2004541c484144084044ea041940c0700400e030021900309d5504080400d41c10401800079040c2a4018034215400312034290010400061440001e8842c7d0400c07109602814090030406070020680382c0e84903142c0d03010b03048000c540c10110747e041400784148140d0514a01f0300c203003d28 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 653201303 1250 653200053 653200073
    0xc03020f0c0a1a070b0c070623130c08070905010e0c0a09051c020d1101090b0708090f03030c03180f011121070602030408040e0916050108190213090b15030f04 70
    0x117a4400c240c90000c0c58200600c0038640c201c00743c1600d04505000860000071901c20030804510308010006249440b0102451440e1031000800c03201c1c08030401d008250000100055030040c003086101040540c1062030251402d40090912204404107001040341103130455003500c107540c07098a20110341c140c0c8070314120345000c0103407020b90130040c1001c403c0c2c18411040c8414140340c03001c1c0c9440c5110307941c4050781c00180c4100940039200d480103100504140c0340c0f11601d5081c600005080700e0405002c3c002290444c0d105440e10b500079444424410840e0070311400d110801d6009003041001061028001915602c1c5000c010741c051755800e040882103011501900c1d43e5580100d02151a4500342c0b409040c5544103000d00300751807001c0c00004020600001e09044888105160403a4162804c0c0056a410502030401c80c4e00665a0101d0507100f07007984083c1410449a10322501e03c01c0c500312000007140c1c805a801401002001220304441d90b0b006d08032a04016924846a000d0340c640c09c2c000545 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 653202553 1250 653201303 653201317
    0xd0509030c0706021908031e0405010b0301061208030c030a021e090a12030203030a0f11070c080127030f030b0d1208010f230a050405010b0a170621011b0c03020f0c0a1a 74
    0x602301010b00042c44030543c000240d80005500802450b5101e002c51071107843d07402c80003401c0450810004050002040245420100b81d900140c03e01500341f500499103040d0310600d030b01d00300001c1201c1e4214a06090040c00078810800007078a22a01c0c1d0b20001c0d240d00c0010a02c0c0c01d83e0b51588020400d6410ba82d2080c000d859182008944440c2e40d441d1011030f0010030b100b100059070070003410310402c440a0307600c0401814029050704101000d581d082c1c0b0002001680e03001850750300d100c1001c1580702c84464040042c81401e4a2044000158000d840d0f4481030304070555000c02c0e0902440b41d03c0c1509121005180211820124407050700c0020710450155044641c109007000c00016401c112030380500f81c4c182c20303a10b5038484424210404a0b01c08021200154841281720603201c1c03000340050b5200c003449a042c00880c1c00030b4141001003001c0440040d8500151440b49207605266042c80150740d0340300260081d01607850300c0c1000800d110422300450300c90030868051100d1561105045480d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 653203803 1250 653202553 653202601
    0x708091e030c010506040e033a02030106030c1706011103070c03060506120a050a06050c0c010507110c0102060907031415010b0415050c0d03020904020d0509030c070602190803 77
    0x201940514025142d4000d00a50302442d0700300b0f00465840d181602400407140000350017581400611511a8811460f60f01000542c0400d80c5101d0000390b142c003521141d04480d441c0c050b940b03515282e4000e0071100a001c0200400c1040e038909000c2c0340c40240599044036017460804500c3d003161222504503c81d03c08001d01415110000004000454100e241b103100104d496094201c81141c0068482c1030000c0c00520a4001d820240d0000d241c2da800181c101d00ea01280c02d0410302c2d100b41c01400c41d44151303412000320300c0c000d0b81d02c200030908001c03503c941002071010f03156500f8060b4041f59983c0e001d0100802c070750110041600081c0c42005846510754040c0701005565945106016240d4054010000c1c0c80c0c48ca25664480c4c113014800300c410311008840200030b45506000201c0084d002400907a038065000c2002c10607a012600542c0d01035400784000e10358076030780d0364501c0e49024840da000d2001d40d00030201e00a002c091807000190002c3c0c00500351036580c0e40d801d05100800c0c03468012141 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 653205053 1250 653203803 653203843
    0x605070b0402150405031507081e190e011e0c090b0706020c0118060606020606090702300a1d030c0d14190f0c0803090f210604030503090c0a030b070809 67
    0x1f0058110b410300034014401d58554003c65100da030200c80351842c50340c03442d022075081140444e503d142d9100c0c209004040d040c20000f5030710383d4080b0140c2500c1e10b01d015901c1c4c04000251001602e50700384074a0f40a01c400d424000a10b0b441d084011046005007580940300940c003144412303130f1110a4001400540300c0c0d1090308015683e6140460060945d070007a10010f20030080020003509220310700c18001c10981d00140161f81e001170145000d45180d0501d2203030040034075140640810500060305140420f621505404a44000c65941d60070201c50324034801e500c054008449038444a44d5455210740200c2c086030003069103a082031501081c2018a4084085080388405001c000071104e16041d225280511060390b582030303020f94038010301c0c9402e58800810300303030321200307183c4a40c0c000602002203c011503005442d205003424104112819404281d0000810014030418030602c04840da040f226a80708a065480c0c104208100405402c188000c1501141c00e0131002c20000c0c04801884c03540703074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 653206303 1250 653205053 653205073
    0x304020604030f050d03050702061e1312030b0f030727020906040b04090b0108040b011512060b0c0f0d020c040b19081b0d02030a02012303070f090605070b040215040503 74
    0xa540e0f071981e07042c008002447c1c540401c0c0340350710100305a805107041c0030004202c91700d1700c00010300b27680c0042d2801c4002c3c90390b4090100050142c0c0d5054039000d0f02c40e1030000721004d10b1003e2001d4040b04060440c4a40c00c1540300380b240140300c0c03915000b1440b088030b11507002c21007210040300910801804651280c4003040008840c8040d0f0001d0043c4d500c041c5040c081040c810300191442502500c008183e8a00c803c014014002044000c500c3c000145c13404015180425002400301c0c0d1498000c070b00c14a50004141e030301c14004029156016106400a02401c2c100000080d15444130300c01c0c1c9485903884040442e401d503504450300c0d50900c50304825441c0c8541d11215999916007865007115040b5042141008a140160205c2c103400d0700a0054800e21103241e004440c0c60002032a5040b241c080c1c000c01d0400704407808040c502c1136596441da1500e580038600f0141610030103521140400030200420340000b4064805c032600540c5c1a55121900010240040b0044c0a1034200c07607010300c6410950 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 653207553 1250 653206303 653206313
    0x8211606200304121103091c0203060115020c010f0915030506150915251505370f1107110a06050a0c0501140f1501030203060d080304020604030f 64
    0x1545600609001c01032501080e041d4450710b00003102c010f020070f918841d8081215015140c400035900160040d2484c040e00f01002903a03203c2e00c08645084410400416011404c00700708050140050441e400744000c00e41d0b500039070701c6007506416810424007260401026000c2c0380f581d00a03100c07c480c07460701c0e02c840c00c500400425041310128400e00780c07950031900070002c820031142c200c0d0000e00040c3e40f44500b041c0c41a099880100010440820a43c0c0d00c030042103a00300c06029188249006081c4200704000c2000355500507008102000da0017000710311030000203055101c100c601c8000a48900035860002c00105020354a82050742d0610125425580500d001015064880c0500c1541045c000b002d00806c070705240030300f03800719408106108200340076585c20000d1900c0b500003c112010a0303c0c00021540c02601d540404641c0c130428040c000201d08681c0e960780d0420300c0e0841c114030f000340000e0b2240082c6030000e041c5036000004074095403210400c40700a19000608422190401c0c505 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 653208803 1250 653207553 653207561
    0x9040f05070320090108040804050411031503190b040611030702070f0b030f0130030e011d0a0504020d06080303131e021e0121050a0b0102060108211606 67
    0x940750001c0d18104581d0864802d440782c003003002040d51441418081141e00550b41110090700030303a880201030100050641d900d0007800071041d41021116241e0078000e814481e4500000d10184c8a03802592980c030000010f454020b84864025a1401e000d40741d13414600020081c1100a11645c8000420000c00301d400260050464089034030f6490354070380d200180e240c9030000369054081d0b0f005200042041900d0703900c0c844c0c031203020000c0d46a034203d0703000841c80d0101c0703001600b18003180d464120b0490b80d68020b001d142c00d114405081001c800d034039900003802c030f45060017114401d0b64003159400c0c59106681c000d10140c120300342226928240001c01444860490008a68039460b04060400c00340c004e10300381c848035901038080c802d40c1441c1b089803c0b14051210020b41002100c0060801003400c003400014401c0c5074000000306820070300e0300d450503945c4107103115040d5445080104030b00302e0001410401c0c2d0181d01c40c2c030401040c503c418004c40d407240003958401160500c20a605210ba00c2c0c2c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 653210053 1250 653208803 653208811
    0xa0b03122b1b0512060607031107090c081f260a0f170c03090d14030d0501050f0103090825050303070f0801061d04090302100204090218030a0b150609040f05 69
    0x5000e82c241d081c00e80112041e11804800c1c000381c000c00b4020035000c0c2000805480c6c0c1e14440c1c1424021048444101c0340350196580c0322204040d16003107083d6440c2d811001441d002410b914110543d80910040401000c0662081249041511050002d01c031094030b610040c40300c036602501d10402c403a0034028940c0c455243d003661003161142e21807003c9400c10702181c0000032100090f5081c40589401c100c03070300c1e04040301903421040070340a0707000668040c401803800c400c01e40d000080e55410241030024007400007000f03a05062400710142c001c1140041a00c408400200800902d0031054009884c95a0340030002002d0b40310201c02d1161141d0044c06442c8685900e580d141b200c1ea030303034002c100c542c01c2c200c00700aa0500380c4c0800c109a07604040e000f031000c0d18002d0046400039800031401d2022a402a8040c04080e580860b100081e040403140503017048500314003e0414106c039071611054108040c1c00460f10141c10341400d10341d501c42000780c4100800040c002c02602c54194030050180100f12 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 653211303 1250 653210053 653210081
    0xf0329220c0203090312040609030b0c07060608010507021006060e1207032f0d030c02060307020724030f06060e120c060a030506010e0a03230a0512120a0b03122b 71
    0x31003181b02c1e0186030080e281241c0282e83e40d505020319544521076103d00203070000540c60010400c00e4041071542c020b003401041d00c5030000a6a10300701c1d4000b0300300812402c807080d81c1c9081000c204217856005030a001741c18011994258076042481d01e40e40b8182d020340c001401269850500e40c1906611200400c28040400c0d20b1342c0701c001d88404001140100c0b040050100f40c40701a800d025091100186500264900440c1c0780300740c1302d11500104501180103000c12425140742d0340c42c6030342e01d402100c9240d81204c409101403401c286019004403008540c003406903c00031070b50902c1b407804101d511959840940055950414017034004c02800701151018003003031080da2106803030300700704c06e401007240e07045021040f400303580c04041c60107114103100c9030400c0c0c45404d03804d0021800a2140341c1f00300c0000700e1820743e0751103c112038150080c00200303da10300500d000034103143c546003c2580101d10840c05500c0b983e48a05503c07402070741508105d644440c030780c2601e800f0141201c55003e404180854 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 653212553 1250 653211303 653211313
    0x11180103060f08010501170309010207060507080904060f06020d030b0303040614070f080706060b09090a02030901063203070f0e0c04170106090b032d0705100f0329220c02030903 78
    0x751f4011a03591141d0b16440d230059000c5c81d000c00001344244091b05000b44a001c83c3c0e890900d98000183c240c07107154001682443c1d007a20f04004003a0104050018011207040501510003040000b03500e9005034884c10050003518040344401c2220042100c000c0e95101034062443c4510f03042c114115042007500b11400c52420030007154244000003a1841140000d04e20316290f0390b801c03a004080c0d0800381c03045d242c1d036403150320106e00d542140b50070310310005400c0b0312002d2405502d1078141c40c0003609260a0b01a4000c0c0205100788918604d000064800c4913107543c5641e210020310b841d2a1007039a10459200c40c0c0350118041000e010b400c040c0864150074014407c11550800f007540342c00b41c03442c2280013240702c1719030340d00303021020140c00c603408071114251808075030b68002098038000d03440d91450019010420309012180c2611500700030001e910710110320070207450396100440ca42503080c10321900b100c3d144101541c900030014031409280c0c0809021001c450700307001e903694201e28505407290103a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 653213803 1250 653212553 653212589
    0x4110a15110706030e061305070f03080306030709060b040b180406090f0509030a0c230a0f050f0a021e0a1a0405240f0a05190806090a11180103060f08010501 69
    0x12034050700d40c5030705030b40018041e2610782d010501c4001f05030700c6048442c0c0c02281000100740e0742074144400258069000541d0b05e00e0907104050a2081580108034070b640b404000b484400c1600d0f060350b0a482008004594803910090f560700c00c0410071213240c1c0e007d42416001f090030f40031038001c107041d00c0380c4000600060722071141c929102d002d240700c100005020618070101203a04032000c0a44c0440c040c121291407102500d1442c24110301d25010340d0004024054002046020050307010b8205418020340318010b202c2c0c2c00a0f11100481c0f00202d103440c45000c584c08a6503641e03410034010100d031042411a25010200e0718070b00e400c64810980700b408030310112049400780550400e0a00760b0b446505d03107403002e8070307409403115000b900c0b400f0100304e4140f0001d00c0e58a07461010141e8000d06480d4412145025800c00990307010090240d096642464002902d504030103058134428060030000c0078000c80c60000403070040102e82d010101310191008001460001917215605a540304070300081d42680c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 653215053 1250 653213803 653213807
    0xe010510030213060b09011d0d080417030304050a0206220305210f040308250803060a090c0e011b240b010203040317030c041e051903050604110a15110706 68
    0xf4845c4504420280e0800c41c190b12988500c3c0c0d6600c8422520440c4480f0074550340c040390020705400707030440d0740780000a024400800030b11145208840c080303005518604c0c1c50b5807181d1310382005810007070140c000032503488003034400005000d03841c08183c0346542c200382d5203090243d500c9559080b400381e101d041000011700c0200b43c0c42102c0c0034080d20b4a860703103010f1641d501d03480c2c158802d01c000c079030754080c501e8001514505418400101401410301c40c0e2603090650410864181760341c000c20240340303885070001106810080060211000f402c105aa00c03050261003c4d400b2003a51009101380d942401081c0c0044922000c54820f1201c01020401070042c08016642d80c4240d00015005030000205000d9081000e401107a2040000340d84a0400d030750344003035410742c200300c1d02012240911740c01c080c451801d1101c2c1460308851001b0080824510b036448580d02d4100240c0040c09039600100010070b81c0d122000500c2c003c1c40035584400c00f42c1c40b00b800c000d0900003011440380b80340c0641e10b00012118 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 653216303 1250 653215053 653215061
    0x204120f1b0303230c10091b12151112040b0702060105130f0908120a0c081627230109230f060a03091a0403140c010e010510030213 58
    0x80d85030f26418944d544101c1c0f52915540003c1c02c88010400801c00c0a140c00024400500902540d010119940050380340130000700758080141040000100c004100c610323000c1941c0304034a03400c1813080c4440740324560080c028101c1c0b40303011901140001800c0a4030b4011b003610910540c02a0424070301910b442c44200e0f1180420300ca81a8048949440140401d04e80c0c0d100f41c00304144c800002a44400c2036640d0784444d080380f01e2440044c528141040002074446c02070100e20035a43c82c1c01c40040c98100610076096003011480070070031071003002000404054100c1002c1e640d1801b840000c1d1035a072074000f0f064440000c01c030548400e017400c6c2c80303c0441d40a0303101c410a54103842101c0700ba4006d42c004030861a001790210542c81845501e815103503860f03000050189441070303a008248031101b428290007190403074116004103243c0104101c0441d034000d0b0180c10000e6a1001a03542d00700d4a2402070142040e04000f030400d518200501500c1c80700d041803d012030b03100740c0305802c0070a2101c04c01400c603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 653217553 1250 653216303 653216309
    0x4030606051c141908070302062503090c05040608030c0d0f091710060905070f050705060601050a0c1202010c0305070e222408070e1909060204120f1b 66
    0x5030b0845141c0b6000100280054400b420700c2c00c040314241454460b001003001c0c0440020b0b9600380c00060101d0501d0b6040c44040d5121030307003400c21800b0307100c1071811060711000c100b690803c041d40c440741c040411018218400003020010414861140c91341661a00c0b684842c00c83e03c01440b07804800014140560035010060b01c23181c031010702c010b1030422080e000c11061603081d002801481c03446a1600300078400c0d40058012424000343e2482d2043c8080c1c201c082c51541003040c0311090050400042c030001d000b13a800304c401e18085031640640a400d80c3e120504041c020311210030060114001c690543c05004404d42c142d8003449070f074484801c160746d0004e0b03d9594039000745800000c5000c0c281d500752480d440c1000c00070001a100030124101202e003089140b14413100c4203017501041240c0381040202c1c05444286500c048600b08002d910006016140074440042e0326010840b0a01c440c55069900410001840013117280b0b0901c0c1c404001008008102d03640c003080401141c0e201e070703882e40350816 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 653218803 1250 653217553 653217589
    0x618010b100e0402030c0403080a0e3f1c0c060b0904050d0e060c0a1b05040c050412050a21080a0e1005040f0203120301060210020a0522030c0b0403060605 68
    0x80b201c00082030001a40c0010030400d0268010080000080d001d5401000300348085e54500c80c21007001c4c0c0802694941d01850342943c107808406a881c145040d00124080301440e03071031010400390520700d550404503030840e1855588908501040700540101003c8602031090717604004446050b401c0041c09401035a02500c0d5600540ea0f100c0d6450050000d40b048a20050071036040101108040d03240c2030000c8011a074414182b4640310000d40100d40900c0605802c481c2400407c903180c500a2a50049106041e00d8840c1c5038111014005c044c00b030042001e80000f104039017540500e550b410103c0c0081e0b400b0002581c08000a51b00200e24407804a030343e17050702c018000394015890164040c190290003a228540d41ca01c0040042e541086186054000000d6203600c80d85040c101904120300740d000309002600410102c82c11070351140c129404242503401c40300210701524864140d0240c5504010445c1071214400702c2c001c01e5050151049901c20380c014400030346c0392024003450110540d25180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 653220053 1250 653218803 653218817
    0x605070804050108090a020603150f031902090403110601240c050606060904021b01050f070306030c0608130b0f060a09061409060d0501092405190c030e0618010b10 72
    0x80b0350b00c22501103400013040c03070885425000b183c0024000341c1c4141c0754034100d0384007000d2081c01414801010150300c54101c000d084841215004014003000300c2d00001e118405500001c8d0401d402183d03080c1c8006600400c44606684400d000c40021081e1619000411070503620303600c82e0b82c800c55013215090340c004090402e030b03190710060120380c3d0005a0207035841390b024085c2034210b90304a000a44214400000403d032414003100c00038000e040641404109410103406002140455080604942c103910b0800703115504c1d0004c0451920440c40024400c003500d10902c01d81c50007501c05103018150444445030300e590307644500c0781202c071030344100c584103040da00b0328140d83d01d0070700100359015070060081d50f2501c0d23190343e5442c01c603204c000007162041762130b82d060031500344100880300380f071003c006c400c00050034030000305c0e21418002c030b08007010f03182c075640710900b103502ca50000c030b07403842030241114402d04281c1080c0c441f02d0400071987c9010f6181a441402520300a62003240c0084a91500a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 653221303 1250 653220053 653220059
    0x1407091506140306031f0b151e04030b04120c060e0f060105010c171b0d0527210106080a080c0d0906090303050d0605060d0209150301060e1c0f03090f0605070804 71
    0x2c1b1018900e005c40207105e59076451503040a07100c5601e25a40400017480113540d5070301c2d4450341010f0214041898103072105c1440b0030310018030301c55162504650407004d070076081700c280b2000f201d4004148000a295030706050301d28a0034070002450400c0c0c2c0003183c0a464141e0307224001160040c902150241040c00c003218030400782c4844d07000400c0d9070051142d01c00152010803607450b1800a45400b8400003803070004540040401d04003020061440300180189441d6440d00090a1040314400d516640f0044072000b10940c4000d40c000d4009000d841c1c03d982510305a802c01c800036130407880c141c820b24096952101e210314070503403030101038642ea034983c06107480c21524101d90581000304004d0724165030b4003000ca41903035418041c0c071226040b248007580e00c1d0b20b40b40500440341c0e40b2032a03840100206000500c080d81d00031807940c44601040d07505890300c1d001082400124201000041c0c001000c2d62400c02c10b069114004206a45c00c1803c02c0c08110780c0d450701200d1a118552000d045070009010038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 653222553 1250 653221303 653221333
    0x12010209010e04180609020d140d0306090b010c03030c17153a260c0f0a030801091a040c03240501120c0203130f080708031303140709150614030603 65
    0x24840f06c1d80058030b0b03042c40c2416599002c0c03c0364068404220780380d11a4100364040d40d40f502071361000e4118844103000d0402541c0001e0000f4605002c001d042c1a1584d9080e002c003486000c0304201092480c0c00c54026003008407600d000860180b005600030302e40c0300c001e610000403194020069203194a084481c0c00d02d4451500b28103080c4000403162505411002a80ea0551040118107a000c490300326170b6840e0040d4440e0306c0c3c104001081e030002d0b0040c01c554004a0307088070313116044800c03000c0b011a80382c96074180d18112400c29907003541c6c8580b801100003d25540340d4006d00081d441844168004c042c03140e00e180c0a0240da11496000a0b40c10360000700d01034484e0412401408940103d906000605100012a0b40b068200e400c01d0180d0940410402c1c4042201400406a5030080c42c90310315918600c8008a19030f0001070701010138100d5806110408000d401f00500c40711008000d40d00b112494802044d4080c89a07000240c1100c00511410701031404030780c01500d000340102246054041a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 653223803 1250 653222553 653222561
    0x60406020a110106061e0f0e091e010803071a04080a0c030e0405130c170703140a080301090f230a05061f03050a0507020601050307060e060912010209010e041806 71
    0x8070300400160901044100d4800d0080402070300c1103803244903200b091208041100da02d411415810001c441e08108980d9402c840018100c541c1590506000e6854041040c4010142510000e41e00c83c8400002030110010000d448040e228900c0c1c04440e41e9081d041144104051300c01803e05c2804006095026000d42c000d100582d102c2c0c1000b50524450381d00041c00c0300d508a580b043c2d441a0042e101d0704000c41d051006000c0c104540d24804d00388060b800c2180c3d1640e542c00020060f00200015120820702005801491a400303545244e40350b841e0038220000e02489490081e00a080c8200f4820003161000d000c203001101a0007900300d03640315402c0744040d000c06003d2941002048150b40922105c1ea5401114000d0703175140840c1c41e083c46c50b010310499900810110864020000503c01a900807030392800f207074500c3ca880300381032070010005207140c0306100006502140041d0710319519103041d000341114181c2603c03070320900741d514402d000a80c2c0660302d580149000f40105400000d0441d40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 653225053 1250 653223803 653223817
    0x8100b070b2502032b0e0d0f022802031612110402040302010c110d080c151b07031d0a09231911120a02120106050f1b0a150b0102010b090906040602 65
    0x180e40781d4545c003445a02d0301110200b02040d581c1e030300318003407105001e50400d00c1281c0080580c03001309801000c0034140410110380040c3c0460f041a183c03491002d560301041202d554850501580da0440d07655080c40480e64146030b404c5441c0c204540c00642c00d40303014425901201d4060f1038060207500d02d6991504008049070071540d00c246072130b5000000c512184007030a00441501e0041c1404901c1e030100440c203100007810204030881000d44900890307080029203d40c0c40d40f40c01c0440100a09221001000c1c5c0c0b621103480e001410301d0790018140b440c5400069414069507217442c034a4881901c00d50031030900300d502d0614030510710619a4450741c1e9038495007030140d40a21150510f08500a8842014400d4400300c40040e000b0035500519484221624010091070410a141c034031007400303c198900402c45060404050825080800201488210400e035441282c40e200110002094401040c2569640340198a0728440c00d84509007450400e0040c404200200903d82d91a6070364400fa41c80b4403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 653226303 1250 653225053 653225107
    0x10090c0e06010203120925050d0b0c0415181d0103080d09050a0c0503010c0c0f1b0b07050a14070602100e030f070507081014040308100b070b250203 65
    0x120705d00c0a070780c8013000c85c5c1c000c0b8042c0380038104442462039010048140c0d44200d408010360b41004206580c1d0b4440441d20a076031240c0c1500e00c0b035580303500000c05030060340d200005108010000b0345d02140d1090354400207425210f0340e07215490300e41d940d4148011074400410b203440004001030001c504954007400c04100c0d000700220740010707103956503820b0450308001102d041024034421701c03140c6820701501e0003600103483d03c2c0200e00000e44030000b00c0325101001515940c401000481d08048521210000d000c209159075940c12007450400d0352540281c40c00d03100340d5a800d070031040c012004151442200c2c0c180c2d000f0406020b58004040003051021164803c520080003469a200c074600040d084e5280140301400c0603e161003203641c2031614004565590301d00d40101c0040a0142c00030447c0c00907010726103880b083d603404100c00a150030580000c0c03803e49010882c10100001e40300d069109030081d504c1c1c443c08681802021840302140008100942c01c103000443c482400021380e002811412 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 653227553 1250 653226303 653226307
    0xa0f1506180608030309120904020d0504030c050106080705060a120f05131202010507050f0d0605040f1a0603070206041401090c0e0a230a0b0d0203060a09030210090c0e06010203 78
    0x80051a41121000c0d842a111a0100c1012042401007403207403400912165024510b14a00b03c03440300d880d080d118074010300d01c40c0702041d0482e4644031681a00c079083c5a1440402003414a41409494400121000c4a04d90308004021410400100b100011990080c102c1c5003000418101658410318042d5140840b5543d00441481904180a01c03401224900c059402a0000e030900c03501c45141d8034049010743e8100014850400e03800000c03517105c400480344160f211840700c0e001401403d070707550002d03501904110600844d91010360000444c003140b12140c1500c540c0b40c00070b00003180800ca0b0284050b030030190015003c04c5c0c000c03000c10490015103000149154103595481c000e6000c941001d02000206420805011928494102d0300c2c0c4040c2100313048007803603922170000f1090040c00078000c1a1900341041c20764440c10700002a055005003614481d2400c10f4540d0f00910481d20140c0041c403900e40340c0d5222075060702c900728500e42c001100302142414001c89100d140c5000c0c055034114801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 653228803 1250 653227553 653227583
    0xa1d0907050618030f0a0311060106140304080913050406061d0411090915040f120201020c0a1101180905061f02061f121a33060f0408010605210a0f 65
    0x6d002c2c541d00c080c840d448002070003144c807600034500301c0141c0000081c4401440c40081e40050301058030b40c01340d8000e4144da9036000140100d11038400c2d996a0141071410a410301013080b0f49900108107a03210404940d01400d00d040a04840c80300a031000b0700b080c10b90142e0107003d03060060403554411240401c5039403850312503070301440d10030741220b00b5903020803021400000c00104503010807290003540300942c1806409058241c98020244005242a6005c0c088486590040e0035130740000701a450500109035443c80c1e104058071080350f1041c4134022030b903c030340001c4030032120799501c10151360f00800d00340c0e55592060169801c1c05000380422410100000743b512082c50840ca105e500c586034a410300a0f034504c01501c02400a0080c0c1c10040300803002160f03103801c0c103880221240503501826080e11107000420480d214500807001030720400240450041d0b41508104206c5d101960200c8400d1111030030940340e00e2001200048a400122004000c01c000c03000b1a8541c030700a18a11120042c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 653230053 1250 653228803 653228833
    0x50d0620030a0506010c02031009061104060c06060602010519050c07020913030201200a030f0209101d0105090a060503060f031b0109081b1507020a1d090705061803 72
    0x50a8038080646400000c10803100114040d50307400c280c00b803d090f14200c0c40c2e5070000b03407034a540080c18280940e0360015402400300581004a00d0141c080140d5070751a12000c1c0100008500c80058078054249480080c2c03203841481102d00ca028025005030404441490348009440041c000d603505280c248404070142e680c4084290040303070494110300c0b444102d446c010703013920841c981401100c84000c1041c41c0410a00007101d00c081421320340021359050003e072a9000f409614000e54205801521107001d043c1c20844904107180514503007420190720b1401120188140c41d941508051814030070050280504061500001e000b40300c0005003c110300441d1800d15400b115010028200d155103145507048005480a04000d4010b012035202c0034248540501071008468000c0d8100b514609040c1e245009840f41c0946c0100036401c0142c0d100101c50343c50444000782c121500340600444d140d00d07000643d9404442c0d000c1e12803410804070007030b051902c0480e000794680601403101803042604d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 653231303 1250 653230053 653230091
    0x100e011e09060608010e090c030c06090301090f030f020f060118052e06140309190c09060803040f1409370203010303080c070309120c030614010602010c18050d06 71
    0x82c02c1d980380ea01075131406d42100b20035070024012029a400505c240c00392620f0100d0074203c89036007555440e1361010841c0100c0d0042403c0400a4094024514a0010141e20240340701400c181c41d42100d080202e002c42d0a034850000f8440c104400340700030051440b980d0300d904180d52013040440c01581c80b800244000d154414022a0540801c080b1a801d2000681101c20303002c0016890605a055140080131150b8a40f149005100f0040c504401d00d020440c840d02c1c180042d02c068041481040c0e0780d048802e035203802c2030240c441c411801c102c0110756000d001140885c0140300520000041e1035032004031200c03c40300d03c2c031100e03100d010000c1d055821340e0207000000004420040143d5035851414020402d450140038408241010003034840860350052469040c0d0f1034015003000000500d1510750f40e41c0010344e000412450905054910a1581d24a981d0481c0d20940080c0305040d03488000700c5007584400122206222012014001030070650400e00550b44102170001c6d19198200030a403800e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 653232553 1250 653231303 653231309
    0x50c0d05090a0510020f120402041805070504050f0942060414041a091c0c0b070201022719081627050403120e070e100e011e0906 57
    0x703944000803540400004014035404450010411400c00020009903009803190100c51404441d061022030195581c69120314403444000c0e107403034003181c410b28003152203284d00d200d040c2c8500d285c80300050814040007c540d110f1460341c0c0c00744c00e01c42c102040501403100031503000080303801d00c1c0d200d4074402d44600d44203910340940c18001c510585445c60070001a01c49403803a0071414122003050000140d88407600c03062a4110801c0d6900507512911258a403c1d4142035150403680184590f0f88445e801c00007a030740a600910302140581c2c0d616400b64242d1040300c5441507800c4120203001120882224a010203460040441d2010050f0b01103000d041e081c07075000b66405800110914122106c1100d61034002d286801c80c1c0c6c50056180110f8401c10803040c802600d00c16101d10010b420035204000c0607203c2c4050100401010065078460b0350798640e14003408004155180120342c403012102510021210340354441e20a41e030812401512030010700c940304209114060000c90700207a90b005040c06 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 653233803 1250 653232553 653232571
    0x90c0c0c300106030c03260d0506040b03120301090911120304060207061701060e0d0c0314120304050c0d0804032a050402091018051e0f031f050c0d05 66
    0x401070066504030031041c074048101980c03425400700b002882803041841101d0304009104143ca0009134403d508406a40b65560f04020000360031020b852030b5031010780181020360f000c00886103c1400e042d60f40200c1e0420380103410040c40104000301c0b8581204282c1441130341c584030140d11500109007020300184940c0700b6034001140900042d030381044080d00a160b180791140ca00034040c000310f4420101801003c0801c411001c480502c0e032100101141c000354003219602e015039a0b418800310030081340c61085000e0080200c110400303684901940c0c003558000010741445480384007008504422044100c40085040c403000000c100d6004000740320441c1508080c21b20032410414481d030076015017186100d0b03803040c044d83c025602c03240700ea60000c00b01810104040c22188a000300080c012b81d00140d801500c0e03030703000320a0910007600b031801080290b42c40121511480101a200c0381558507c46405580d5840901d10303044a400c4990040032920106180c5010015140c00703803402291007001d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 653235053 1250 653233803 653233849
    0x30501020313110d030504092a0810121a130b01151e0806100e03010c121107031202030408070609080c10060602100209040e010204030b0f01050a05090c0c0c 69
    0x10522003d8018121800c0d4200d0b1141c0c080200d50754050000e0145000c0d906110303136244041c0142d0f40161084030400e83c07102079840111604e0a5000b0080f110440700400b1004400c0c5000540c51401c2c1c4081486541c00151201061211b20159240c440001d00020082c00d07508844000306103551a510701802110103c07014004a10070f001d0201c17808000c81640300c1c61200250501f69502c01801904050211040c04c140407075248100c81c0703008802e00300c80c0d16500c0c0c00000e0b542103801518121341e40054084c2400050359500100704075005010b8040c0214005c03120540c0e9200e0568000e55000e80b00e120540d0503c966074131031a04a6400b141c040b070705024002403091071000d003000420081c0401d402c00707000300350030098001d454a21568092405030b80100360740c41c0175561900421400b88215008640301c80e603d0401c0c4030070b01d40a071040c90955a64100214440c2480102c0200b41d4402415050803901c0308070500250380e00030a4251414000c01c041c0d902d0556983c4440d1190030640d503030f030003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 653236303 1250 653235053 653235091
    0x50c0406020c0102030304120305060111013e031b0408070f03030206061e0f011214061813030e0f0907050a09051903081c05040f0b01080c0d14070305010203 69
    0x1a141060b080a200e055505c00d104210020320342e202c03d40e40344200f503d070103d035507220000180c1c0c481480e024004495420300c0d403400c4c05080c2045003200714210000038520756801480550070042444075141c60454410030010b00c441070b0390610602d20f002d609244601c0c0c60340c1c0f28030440c105665a04501d0050f1a103650400074190b04005882e0488002c98840061a00c440340c50b5640e42c0c2840a003a014560000c0000d0590380a1008011300c009101801c1c00031007010405811790b02812100584200300c00c503804c040c3c45403905074132446070442c600303014042175194030141d803021001245c0c543d000d444417926036002d4540750381480c06800c0369100e0035160040b10038082d20002c2c540e040240a81c171244803604c0020b04010094040ba50071610b501da54075501010078118150b00e1508280c1c10b4205014407042102c14409001c42e54059500492a80d0300c4008031a210140f8807003290788076001c104508003103400740d104c058440c1240e03401c482070981e595803480d003640c03c2121a03400d5100c000d8812 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 653237410 1107 653236303 653236307
    0x3092a090f01060207080a0809090a1d07030209090c0f1c2306070906020d0f0318060912140f0c0109021302070c05030609030405120709050c0406 64
    0x190036080c41c09041d1110948001e200711001072180f2500040d07208404200c009013a50700520003803070300e40800100b10b03007080050020346840e41d480301c01501011031103040c00c042c81035482c05070540c1450342c01040341070b00d0010310803801500068100c21080e6183d0340011242c00046441c60300b80b81e0310141181235680c121400034507403200c112040c0550310385500d10b00090f9402c0000c41e42c690341d49070400c540b41c1c5c0c1548503c10260307020020503003003c0e000e402c6002c0810000d140c009010602c8992410720440221810703075090782c0d40d091510030300c1203075103012645280c1401c1200d601000d81000d0310b03a5101d11181d0302001c04022801c006100000e400140c0d0301500200048003109103040c1340402544108421075030111600d80003d010700303010038810701c11000328014606041c940001d001ca03402086040c442c09000303a10300415010700d184076040c02002590080c0303484501308200 = true := by decide +kernel

theorem cover : BRFrame.Cov 653057553 653237410 := by
  have h0 := BRFrame.cov_init 653057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 653057553 ≤ n) (h2 : n < 653237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
