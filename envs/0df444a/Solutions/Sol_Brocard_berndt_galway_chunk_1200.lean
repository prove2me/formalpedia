-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1200
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:43:54.92118+00:00
-- url     : https://prove2.me/submissions/b17e7868-f809-4f6b-b1f1-9babb1616102

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 215647482 ≤ n < 215827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 215648732 1250 215647482 215647489
    0x10c030909020309011b020d082d0a24031a19090c05060408030409151d040c030b041119080c1203091c050f03120c0a020a050a050105091b 61
    0x1818014403107aa6404004244800000d60044100000b0300348000d018006410000c0d555105040160b40055103c00001f03100961020720586d01d041c4640ba12340348003210905602d060342c1700402005499aa450424001019030501711820381d002950034801e0f24114140054003900d042003c0000708005000c0c000301241c0031140000465001e00002411038942c640b1203960101580250342c0241c010601140341000030009000725501e0344010407000c2014621401c001015205413a40e1141401841e4100720410240540c0148240c95480c8000c0d22a6101203c40c0c1064805580804214a5071110790400301000b4403441c44a0882c2a200b038074004001e95958801e0014a005855801d03c3c4c0500e2502001912440080241a501c85403440c5000009a4520400a69040c8101110303503030740750300101c202c1d8000d00200018001556501c04411025404a001501148291104d65010401c01e21040c2d05040c440c900108060511101c0c00c0d1505000d45a12a1680b40f06030140e0b0142d41c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 215649982 1250 215648732 215648747
    0xf035a090604120f1a1f030b0601180e0108070612140117070305011a0f0109030305040909110607051e07050108010e0a0e0304080f101404020904082101050f010c03 72
    0x9500f806034031010140c900e0034040c1a013080c807000740f0000f00108014041100c18940b18031644105030285240004085402c002000038800905000000b00224a00d54410ba20300340303a01c11055100c2d001d09030f89062441c0c0c0d17500b0036401901542c001c604107000c001e80c0b001c443c010340d00104105100c45212008003007020803040c481c0002c80030000d04c0512000c6418003850f0300035a0001c00030060341c2c02c0c0030121218040c5010b00140700700021541400f0a60044842c0e209407605581e0701400d01d030902120340e0007456074000607503019000c00c0076910143e656400402110340724002420110207100403160310080d400005508540110005100c1641d2001c01e860440350340f60302c40c50041c0c487d10100c0c3c0003800d1200302148240000a004102c95a0000343c00008030343d540121083e03098003007100c0c400c03505d5101c071000f0ba52900c200824003616007200c0301c80d003242c01040001d00d00507030808400c2e08a180504000780041e00340e00100401e290080c0e0000c500344003800d0600112180750f40007441003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 215651232 1250 215649982 215649989
    0xc011106070c02040b030307030201090b011e060e040216030c020a050901061d060408120406090b090d080c011122091404030c050a080f0d0e0f035a090604 68
    0x44000640c0c0c00955803139410180303030034a01505032669411103040003800f801c64900169081c00c1048000581640e003606280c601c0100b2620034589541052412142c41a90041c1c15074040d80a00080303800e00303030105c02840002c1c4079407226070103030b08180b040c84a814510b0303110a10a440b04401040603940000101c8011841d418544000e07103030b41000a07442d4069a0000141e40c41403c1c0b0b0b2480c6982160014003d40e001e54030744120540c1d0311120618039110b54000341d50081442c00d13003200000c400c0c00203050820038400007c16841c84075070300c0c03403860340100c06010314103038034010036040925000404c9409800245410b0000c82008143d90710050006400141004009112182407041c1404503110ba5035205082c03607614003050300208016000b919001080c1880e00d080c15482c480300288400c02d050b90140030b1803c15400000d508507030a81d13026211200d50304120084074070480040044e4a06198001c07401c486000741c5c00c918490300f610340b80030b0007900080201c3d400e81c1c4d64113800d030343c01c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 215652482 1250 215651232 215651237
    0xf06090613030803070509131b11100e0d030e07080c010c080705070306020304060515030c060c1615030506030607081506090603131209050a170a050a03030c020c01110607 75
    0x80360807070380c1500c1c8401c0035a0b00c0034000c0100403050011741c5510034014003807454202d03880202ca2203440f446004540e08628591070041c80689480056801500c010800d0404001507a200c014004215400e844c1c528002e80e442d40c01041ca2101181c1d010b220704c0013a042c5140051062030700f0b00c00c00701d64844079482014140a007401440d400c0121b5401110705c1d0ba80c0c42019103007100d542e40f401101075002924101c540e5820040003c55254880c030341c00310a030030000c0090031245950b1052043c00d50050704a000c840c02600e44180e41c071107050226200034042580d2042d1041052a0001c00300c0d01c01505d1503110740c0144050089455000701c1d4207400c0000d040c0581410f1001c03000190382c0f44941ea10864001c40040101f2031002c025801980d142c501410a08030749540d100ca0488200c0242d004640d4401e0002d10240004440c14101e0342c4042040000c4403002e1060351540c0389024100c603030440000380c07200260815103a042c040840d68000a081132540255000c0315036441c0d210041c1090f08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 215653732 1250 215652482 215652487
    0x4030c090513020a0810051e06010c05031603050304020a0602031207050c100c030515091e040501090b010b0c010f0b01120b010c020a0801140c09010c0f110303180405060f060906 78
    0xb90703414000c201c28407960007022090104d039500d401c980c485403050007204c922031800c0e0004903186080d078400300784141c0c1058448520b581d84001510b0b0340480c10f0007600d80b807000303100c0403440c081890203600d4113500984407a9242d02d06807040100007080c2d504040110740040c410b00c501200300c4001c1d6900300740d031030401d2070b190580a4203403803402d0340991180480c241020985850305405a01a90080360003007201c1d9440807440052091505082d00c449040080300d11030140d103180d0084078242c02a01c1a4004681d001d0717240c684445421083e0040c8182e01c07030002d043c000400d024868003420b01c1461a052010860400029102c003600380100780c40c2c20b403661605245a881100c400400590092110070b50548a180040c02000010040721401041c0400b08000701c64503000d407800c0d000141c1d21002407031250740e00d4085e124981441152400801e020310049940d050011305a624032042d540420650310a013004156000506468010030782400300d00191b465490440d000f40400351103440e0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 215654982 1250 215653732 215653741
    0x705031612230d090510090501080c09041803020d021504030906030207050c0a030c05031b0a030f02060408060c070303060e04390b030f0c1216140a081006030204030c0905 75
    0x14a90200a4002c414021401e000c1a010b400c03540d01810350784251251040c9401000e07003902c0b0605240101800300c2c036401d0006d40c24104a000500240c00081d10205d0a00b00840582c82c03a21010318007240940c0295a8840090b9030400413681e01881c1c01080075032908040d10b0140c580001800f5000c10150001007040600c4010002054060300180800322101c1d600e04107180076800d6802124840e000b00032030700340042070340e42c10780350140f50040080c42c0d22451a56642e00d0b101440b0307012a0006024800065044410320090344984094260b1070740d01c2d19280340041c11502e490b000f1511501c110014000841c100110503514410420a40d15644401d640d04034811561200050003582045501142031070a40024500a802c8100350440f243c0b2040080c14032800380c11001d603c6e400c450b000040c081000540940c29408040c00c0001032895000c541c0d44981e0300c90800240132811020a1000b40708088010790b00070401850304508140c2503a03036142c1449214441e0390300703140d201c80209 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 215656232 1250 215654982 215655023
    0x7050427030f03140f100630060803130312080124021c02070305010b0616080f07020d0501090b0108030901051602030f0f100b0109060c020910030b07020705031612 72
    0x1000040a800300252242c81d100300400c05e100e0084a20030049101c3c0c40300041c1c6a40149000c0800390001c840080006400d11036030440e900110001002e06034440000241086062009041885a22442c5641d450641c100140400e1565a00078100b1212100401c2a03001881d980b2000c4031a804803042d0f03103040450203c1c94050702c1003113011600c00c0c10003c403658613000141c04040700c3c0306e44000d000700c8071010100146405048a88003003070410303110350350000d001c1a00600c03640043d405402d050001719004a0441c0700c840c10100c0365070303650b00c110702e050140c10051980140803400095103815542400244103000380b0650038102c0124100c01c404654003481503c40d098010000c40d409003000e04292642ea0703a101015403401490714041014075403040160030141d840742e803204185041e1aa0a200095500901011500c10700c10360110028154866243c01000698010b004e42800c0004160602c01c65038400c0500c0075080384200300040341d001905840350b400c4013900c0020403000c81c92 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 215657482 1250 215656232 215656241
    0x81f05090f010c050d05160c021219030504050906090403210204030210020a0215090108161b0501060612090b01050103181505010e0705030f0c0f0c010e07050427030f03 74
    0x110072195003800d440108442e07116000d054003102e808414410b80d254030482d503032440308002c032110000d480513034078101504020400d0340640b15404100c80142d000104041001811448103c0004100180410861401c0e1406036005103040307401c3c031003504083e5006054030722503000a04250f4060085101d83c000c80358113403001036802610408003a0000f0310000e442d0442d5039000c911901c00712070310314503c40b5402d040c0e0702c0700081030310703018016141c007004200c43e404180031040c00c120280e2010324000d804101c503a0b901c04c5c8100004680e030f6040c030101a0a09040b2401c0310340451800000a020405034800c1c241120001c0c02d0000d10000303941d5000624000e402c0001c0c102c03281d080c041c2041140c1d107a0043e812030701050402e00c3d40f501d40510850b500d01c03081c0c0300291406042c0d40403130a800418001007800d500002c106902c0c1014440d546402d6401181410040e9002101c0800c0942014015480400b48002c80c1030407a81068941c500b10301c0003902c02404100381e5040420780240241e11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 215658732 1250 215657482 215657503
    0x71107090c12140a111602040f06080a0f05070b0c070b090105040f0e0603100203060d061a042a03090804091a09010305010507032405060d021b0f07081f0509 69
    0x2c24008030050b031943c1d807641c41060390f1010b021850182807484103c001d00948105100c40349403490015680c1c5c00700000341c0314000002c2c0310700c1e85d02e0078001001030082062030540c6100345643c1510035954101581014195440902441000c000c007200310a030100e0b0802c25500070383c980540710010000109c2d00e6000b11b8203c03180a0304003190104070745800c8050b103485400128225801c0c0f03503820840b2000c0c2c0c0416a00c82c0d4000380c1885c41000003689507000920f01c140d0200b610000d03029003400050a03940482080c8000c00b00181000d0305c5c110b21485a000c0c100c4d40303410b081c000ca000e03981c3d030303802c05201d0782c851480c069546483c60b0020109141c0d804100c6040200317171940319612070400c0341c02020240d0749031340441e00c0c1840d00b0413240f0214000c802c8421604402d07010451800007030003241d52005d4000b102c0264208211000d1080d445012035030300400c500105580d40340029141d00d00f52035608501c0d9a035000401c40103080305442c413031013011104414085400e403180c988003464201c01c084d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 215659982 1250 215658732 215658767
    0x160e01210c08010914160f0302060d090605070c020306060604051807030f0f020a030b0109140d030e1e0a0b030108060c1803010509010b0f0a18110706050f010e071107090c 75
    0xb42107209110169a40c504910403110603610941012500f034106c5100910078120840b20041c410405490303c00c019001c821034116003c1950042e41d554103089420884400010401c8210643d007581010000541e210754156032185c0b805040100240c69008801e4124550488100000d4600d070f1203a0001210500d03091414052020100e46000c0a500030012100000385810b03485100c0d580b0402c0c1e29022941100c409040446640062101c4180d02c10015010301c0541592042262100d8000454000e40c0b9502d20b003420f507c1000b0001082d401c0c1c0e0002d48041c0c0244010301107250045207098002902c90400c903500c5c00c84892a006041c02d111180307a25502c1d19082050500e419040000002821600c90800500480070800210460b014401c41e034520100040030a4040340d01001d406100111880d0800110303075034210990717104881420303840348204010488200f100017682c0e00605076080c50030b8603022202c075060340c1d030500c1d10030b0a0a194684071030740a403e00613642e00e25215401c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 215661232 1250 215659982 215659991
    0xa0803090102040e0a0218190f090f0b060a050301062a12030b0301020a080103021302090d050102090102010b0a030203061501121a0310090314030606130305160e01210c0801 76
    0x940c46038000d4200f407113007000b030001400010702942d802d44201ca9810401c081203030100b0720307208240421f6854180c84101000b90039100412120b5403807002000401c0c681401281c1c2d83c50b0360104100760741045811500030002800520400c98100041c0d81c190356180c94100c40f020407601801640500c00503a4070f02c0360780c80d5004d4506200d018000a0243c901c180c60610580d0000300515080b4455201640b0014655000500061a200c20f003419140056480941030000340350018400f2a4096403c41c1ca0341c1d0b00042d0300c0038031b580a00400f202c07420100c45020f0114a150003203031b2501d100400c5040580c0030020747c12980c7c0e004650390308440f48003030010003450180c5c07001401044081c460341407291050000c5500740c4090b0303000e090740c407a5256850380c074103001120021086070000340050354441e4043c07094010860341c000c0010015809000201644021a60503980c50041c1d60089803a018020005000000607044110118840030719232a0034208035091040350414190400c040c0f80d42170 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 215662482 1250 215661232 215661241
    0x5030f0f120106020705030304030605060d390e0c0c1203090d0212131203031b0c02041a0108070c0c030204091a090106081c18030b09010b0102070e15030a0803 70
    0x285006404541402941c81007166211001a60780b80d00c1c41c030a090b8103500400003400001c10a030030440d04900042e1165183c00b000c1d581302c89000800500310240519100140c0c00c00c01c10140140c800e5100c004004888035042c0036800d0b03502c42001f800c041c2c1082000814058400d4100410041036150401d241d4881c00c04041c0c070354407191008440700051050034031040001425504842c0c1030300c0e510180c0354002c5d19210361085000d010840503824150345031042c50385843c10a002c21503a000703540d0741440541d01441000300711040b83d80c0003000c0082c01540c12400d640c01558854000f1483d060684032082d0502d80001c494071207802c000d41090914a00e0f004201d42c030701d00d1500c8404920030407080ca03540e052030207088454a2003030340020b40c000d0921041218201c0a071100100051030510480d46200c1c200c001c07940107590040300d42001c6c000070028162000e11645816520034806420802c0c509680c40380c0f13000e80645030009144c5101d03110b030404e07901000080302c003035401015540c49140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 215663732 1250 215662482 215662507
    0x30e0418020d0c0504110f03070806060d09030302190c02091f030804030f03021c0206010509070c060513050106060306050102070e090f06010b0d0605010804020607061a04020c070504110405091305030f 88
    0x3148103071809a400c0c0713081d4540c0540d40d0004d030355264a50607c0107003155680710080b030b0404e0000e015203821a0041103100240d680343e008003c54280251005640c0d0300744200802404101f107944501084403010300c26005950704100c4c030790000282c1a001c0440c0d000824004051440b680c0002c1c29071200107400010055090142c00c2003034000d4090310205030720384041c034640c20341211030100140c02c0b040c011f101ca850108840b030f42000d050701e003860500980d641c808045420541e0601c00602c503c0030300404000c070900643e40940361034503007032102c91701e0040043c2d540c240902032041c08122000009141d60000c01c0750321105100b80d0304031002560f43d07007203c09140d440000d0901080d81003c0340840d10307500070000c8034003070b640c041d00c0286498120b17103d00c0020301207142040060745804c0c01c000d040d030b555400502050b6a206000d0008249030000700012990007841c00c01c0c207460244410003065880c2c04920b5403007121028182c1020010f468442e05501c65050000004100030071100052003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 215664982 1250 215663732 215663753
    0x1020d0c0e0f010801080607030504080706180b060301060f09020706112209051e070207030606080f0f01060b09011b201002120a0f20011e0504030e0418020d 69
    0x1c0c15100b03600400700c1c0e2001100c080409011305681c550046002c152000e1280e4441540b0038028120b15081c441c2590702d8105607010004601000f041c92504c2c0f00901409041c100e0304080c0484c001c000c11854040090240c94113481070716001c9074045480400d224a6401507240301110300706141d0344120401c0322890108801180da010845c00440100f2080b14a1080b20b0080354406a440d0800102c032100c032066a000800c1c010840c00f544034004001100f03405003078040c3c04500090680642e400c41c2c52403500340c00020b42251a81012002c000b181458001c803043c0d840d003840d2440001c0c0c07505c0b0303114200c500403120040005001807a00590402d8416001000781c1e0129030588516403c440200d0381c8261a500850010760704020444840d0300a8102c0010303194942010101d0182e014911200d681648449214694444450ba5028000c0501c54140c0c524004d00800141c105514000c01100350410000e015950b14940180c2813480c2507001000d00354010285400d4000501d04410000e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 215666232 1250 215664982 215665007
    0x190902040f0b0405060304060902040b030609060a0c030203040f0b04020a150e0a0e0f190609050108011b02150106080403052701020105010503010c05070f0c0e04030e031209030a030e0301020d0c 85
    0x103a00c1810003080020b5100704640c101c502c020f00345821500d0381e8980000510200344200d80c060b0b0b98034000e4819031014024184100c1044e405041a071800d03500841c01d403050003903058105841041000000380c91000d10108003600b0804108650360b072440800c4c5040c2e00390300701c40180c0318035446101e1100d500000c0f8198454040d2100341c011903482108070402c00c801c0c0c4880002040c0702c0005001c074008181188004034800d500030440c0c503501c0704c100f82215403e8000c007506035140d0103d8002e403410607040004585443c401402100160182c2e042c0d022410700035a820080100003180605200b407007500c06155030b112050010240343c1203030070b4100412201c1d240c059400c081c00010f00d840e0611400800c40042e40707469190808650741c0c0c408440a54200711750710b00900102088081074500000d220310300c60348609010143c10010540b80a008a0040354a48010480256140c90100d0f8500000c0d0b80760504408600001d0000b9000e4000d911b0281242817a04c0f42c0c2d5032040d9404680c04545 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 215667482 1250 215666232 215666249
    0x1090c03060e0c10020c040b040612050109060b0907080c090a05040c020c04050a1a0634060e0307020f0d0c0305300316080c07020612090f0a021c0219090204 69
    0x26075074010604ca080d100c192004400768000c10382048480c106600417181d07000f0300810000c1c10b5074480078025450012170005030742580d035400300b81c000c00071140b003111481e02c41100d103413071103191034203004000d80c00c0140f0151900308045000207040c3c9500c454032000e000c00500510a02104800003941e40300e09841f124440c078108004600c50700090f205004012524a40003100701d088a0305210440d8404003407400030300c1b896020014001036480607031021200c512a800f00030140c80c20802c0c182c50466428208582007007100c40010f0b5103403680d8845800059644000540d1035040602c0c2e80810740d84080c015000700c2c110f0b038900640034100c8001000401403a01141440d40701803c2c0103000c00c69840380c08400450075000c01a002d0308070b090788105400360f144d281c034030795501140164000c0d618800800d5099400d0098030201482240806e100010041105006a80000d158441145103001001e6080c84a64017035440e00d0140f80d9000409000d4010310590321103000000394098490602c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 215668732 1250 215667482 215667493
    0xb03280b040308161e0f17090303040210020f0703020d0807020a080d170c071b09061202090c03070e0f240403120504080d08060a12060e0c01030b06120901090c03060e 73
    0x82a80503d42031104410140d01c05e0407030410011003510f000c841005840240900d0b00704040085d03041c5440c00b442200c80318003441d16810a4418030200c501201c407124190740090f045800c07030042c0002c50f5400c903038040b500c4010681080c02d100d00c440c803400c4030103074000001d1540820b072030b400003c48004503009990740d01d41d544003911107005608030980358001d403035030100302401c003241000883d85040b454680303800e50495524003009007110070503402400004611480b0200b5403a00c080344aa00c41201c02c0f081d0310318901248001e21004000304402c1c4503111011903424162604680c040d042107135600b601c0f4800c0035083d00503100d504988002c440b404080241003e40b00c1c491000d880803950960010140c0c003452090683d48001c004001d15084101c0c1c210000d8054084030440c02914003a04d0009034246101c14258180f1505040c0035042c142040c6079100d058a0392030072a060310401c6055620a61070b21402c0a014209030380c4e000d4407400c0c560034003000740f10301540420745801c00c4508498 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 215669982 1250 215668732 215668771
    0x121a0705160309080303040f17160b06040e1b01080109110d1e14090601050609130c170c03150108100302090604021e18040b06030a050405120318070503010b03280b040308 75
    0x89ca1441650b008450007541e2030b4040c3c0003c5e0480c1513180d084080180b001c03030307a1044044d00d01c2c43d0642809086402a030381c0394a402d01940c10401c0a805050220010307c101060001760701c030f80c0e00c5400c079134441c001d6540079a18007694035403030891500410100140f2140040110b0b02c04504003c2e80c2d103c0090244400000740c5161800c11600c544030050b1081521203403c0803e04002d203a644e0080d0f0038400d24065220000701020a898424800500155103030304100b00450360405d50884064103000050090110032040c00c54420216941103c0080c0d0320787d21000450301074014241d0300c10000d910345035180c0f4001004000f510a5106a949441c0d0210a44040000340d4544414142d001103041001c50503011203600441d074170600134822038070f20580e10f80c40714680e40d008642c1b0001d0b50507002c0d5907007420704080c010380000b4541140207010110f034040009840340700140340240d00b9070301404084004110101c501001a4003e0403080f09480e040c240606075000c120707000840c882d400000c2c00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 215671232 1250 215669982 215670023
    0x903030b040b01080f100306021204030f0305270f0703032105040305190c050a08130b03060a1401090b070303090b0a05190216020a121a0705160309080303040f 70
    0x500c2e2440c140e403002003035102d03c0c008503403a07100a010b4071a01c50baa41c82c04000301d0040c0c00200180b84512041c01102d10385418018020300c0003800441c105401d120500c0706245804c2603010311410a49450b12000d134a482c2280c1c54400340300500d00740d0380184a0700005040d00309a070b224092031108544c03619404040100004c0368000c0320300401154050100480f200c02c2e031851b0701c0e1a06c03190304043d03028140c180c840c02e16003104c00408640044000402408941c44607020300001d00318140c80c107045040c40d600088001d4031074041c0c0d0080241481c0807505903880f41c0006001042c10a80c05555483c190500401404100800f038525000c3c0201041c2402c01e80c1c81082d12400e0500ca188a10403c081c000c94040d5022840081c040d10300800c4620150351001d203408001c000c440450541c5d0201494074191001c000d1140c8001503100324108081c1744d0b000412a0f00d5410890152490aa4030b413405a030902d000b600415411b201c04001c100410a004518450b05030040c06440440440280007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 215672482 1250 215671232 215671241
    0x1a0c030f0103030f0905030318030c031f0c090b030a020706151202091f0e010e0901151a040f090c02011d0d030504080405030a0f032c06031e0106030903030b04 70
    0x4000d40d6420140100040303485040224440b42e103d16104401d295504002451500a207044081240b6440060b140c28075041140c44480e100a6024240c01e03928804400c0300e41e1507000c01018400d49981825003020300c5032400d48041c2401d1603240d526820001201030080d081035408440c2c42d85840800c5c5011006d0540c1c407000c0f112030111540c1614002e90910100f400c018000c061240b83c03400d40301c52031041002001d80030704094018060b0b2036242c445111041040030304069003c0e450030013582c1c10403854015400944040c29a4941c10502d0340c1c40940862203680e11001071580848804254071403903421649914201d94004d000fa2034101074090511940004002201c4d07100e005214489c9000e50421540035000e815428100750341e03080841e04081880d103007140e6000081c80d18500301074000c0d40c07042e41601c01441010316410300340340a1004502d50346169201d040044001050312102020032940c5c030900206040580d60b50f080e02401614980204401080c00c1000005143c1824440d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 215673732 1250 215672482 215672491
    0x2040b19030f05040c0b0c010b03010513061a010503160c0618060b01080f01090c140a0c030f090b0d090204090203012906180405042118090b030d08100e041a0c03 71
    0x10707a1760740342c210010541e6001d42400b00c002e54032100d00c41c1203640d00f840b45900c100ca2420401d00007030134900d010005c4400368507104103403882144241302c40307903403140c103803944052220072250100300d50786000c0d501c2060104004202c2424519858844800e0610000100d44105801d11082c8503000054501510446a007140300324907100403c47c240c06500a000300540b14140b86c50000c1c0a0f51080c0b00036032140c80070380c0c003140072030740c80310100340d8814100702c1c1503040d82c9403031003000e41015921000b51255400d400d5810351500a04001d55803964416522907900074020042c402003803c6c00c100d01d0400038240710045c19001128142400c05404903211402c20781410200c0c0b000220410009120103442511205040f4061081c00700244081c21001c09050700c0c0c0300b000c000400050040050720f5000301ca04d25060014100c8662000500c81d1101c9035641445100380d83c4055121201107881c0c0c1c0704540700c1c2c600406220600c03800c450514440b0114021100c0503030340e0b1103034100700d5110958 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 215674982 1250 215673732 215673743
    0xc0302070f0b1b03010807063b040f140603070501111e0c03030706020c0607050a0f0c08090d0b18010501030b04030f02070e0c03160806030c0d0602040b19030f0504 72
    0x70850300082d101e02c62055009298008051403800c0280c0c2d014000d030000d030403074044c951100000780880c6401c07403444c01c41c4032048080611503003081c012aa0650316851a102e08a0102c0c87e40030409590301d0708078440403050340c0e0702042200f10309011940b4070541620444c0c06801007110101d83c07944030700c4a813800320017007000805104040c05029061140e040a61f00e0050042911842ca1a60b0900c01008002d00403030026881c1c0b07218400080c10868003402840c2401410000da0340c00075000300d07401000380518244010800e8283c1420306e801e10a100400343d0060550700041d0801550900d031170f02403056080b13420016003500c0704039800c0b62000c0c00080c100515040016001a00c19290f890040c03c042c41510412a5a042a8241e115065a000000e1980441007042d508050040f003c1d08a40b03524220301c650400c14042030b15618010725817170041d41ca5001c08800d001c000e8048a0003840400c00381550f6083e42840f10824461a45c2c0c13100000741809220850345005010751402a500074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 215676232 1250 215674982 215675003
    0x417010209040c08131403120403080a0b0118210503040609090b09060303040e180102180319210302120f0403090e0103020f0f0d0c0e06040f02030108121b010504060f0c030207 77
    0x1510340a90400c07546c4140503251200308400e11003154081c81c0039010301d01c00d8486030383c142403498001d070a40d00588455030405c105510001c600c5000403502c403040b21402a43d802ca5402e01c803c0c204030050300a0800340491200041c0041d145520045001c11204c080f1000c01c005000a0700b0400428416034680307515a000f0300c0240700d52068294141e400c060030070121010804081d400c00e0030ba80000e4034844800343d05456040c1242414055030158400b048003c2010740400e0b0364441c00300c0c40c0b6503c107a40c1415860880070846010798111003401903c2c15000d00341d4507010b0100103070301504a80c100d00046600400003104550050340034141c80d401404130710465a0f810078483d40602c402340780c580c030402e034680b8130002c184910062000b418098a41614074501030052006032480880c0a140041c070401c010080b41e03001007181c40084006103241590f402c1a140141c200310300d86c510005403940303440180800c100a550000c100c143e03001205004d500c11210382036040380141c1401a00c0c15000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 215677482 1250 215676232 215676271
    0x702070f05031c0c060e0303071d09010915030506101707030f0b0c040b0316030507090e060f03210d150503030702091b0c0a061d070b0d020417010209040c08 69
    0x2c0000f08a05500c0c914213400b000c045a11074030103842d40f02c40406510740000051212060740b001c6602e0442d50a2888094511068008569860070500c25200c140e503460b050629406e03c0400403100464000c0c0481d01c00d800d00e904144210002403283c016816204541d0031045a40400c514003107a03003010250340001030584440c14002002004458400310800c400704010b9000b030302031030190945006455406030b01c074034080c00b10741000d4802014031210a0f0300b00310441c20350b0651548807c003610300d0072a081c080404245000c00c516015801c5041200d080d82086e628807000c0c2403d24101601403141034001078800038622481e0280980680003000a81c01604203694900e4104070002c540c034071344181604959078107030441041d0320303940c1e000401003105001742c2d8081c0d40c6000715040c1c8135440f241401c1a03200c1e0344075440d10480c14004800304140c141110954141c800a04818852010381c40034500103034000d42c002008184660301d480120440d041c441c116040c840c10100013400c03c00c962 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 215678732 1250 215677482 215677513
    0xe060712110d0c03020309012427050f0907060306061403060d05030a030204030212010b0f0121060608091b03031c0906020d0203010e0a0b061204030c0f08030702070f0503 75
    0x20090301c491411181080841c9120200d4415155500560381c0c0040e11b905010000c6402d41e08036080000c40070700a607100c000001d00e00c2c2d248a0449440b8451460f4030300c2241310000355608000c8004070306600d8a001c102e0001d00340003100d8030898900040e2201151960700c10340c121215801024001152598100c159280003c019600640001c08420040c0320580d181807455004920b410002500801d081086003820180400000c110704000e200035544000030484403108400d81c20f04004840502c003034041c0001400302c088514180d0309100300340e103800c006080b032641914000d899214440f00c8600c403011724004c880e80c10718018091854500d60201d1001d141c403c0403190b8080a9440141c0c00c00921103200802814070a2440035859600d8068241c00303444000701040303005401c18030030004640d0b800080700c4500151384d03407421041d115402c080b13542c0350034100c0c010701402c52a200c0c9001c2c031011307001451103440c980e03088505050f202e10101000810303620a440e0550300210f40c0b440d01c2c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 215679982 1250 215678732 215678741
    0x60a02120f04020d050109050102090f03070528150207150203190809030c011d010b09040309060c0c23040c17060d06140a0f1104061d04021e0405040e060712 69
    0x24001001d011350031a190301d031903003101c8603640200c030a80e50010f05800c1a00b414000c8411401d0124041d150082c07070310000c11040d9405000b41d419044403c0318540105d000020514054420b13522000c1007241881e00c042e55075000e80c042c20300780103640c415410103d0710000840f0400e49480d80020041001900d00340c030306801c0900b080c10a80814054405906001d200d4440840c51445038080300e50751070004c071800c6650404c0a940100e243d2030401012039002003001c8200d0340c86207400f1007181d1036400d180c00e00003d44c4e00f00106551940e441ea00b81014944188071101e041142d0801c00352007518130640c0e54111a110300060050203c001441602d850780b45c0c0251540112004a800143c0c03c10303660b4540011504040c0007540e41c0c02c4041d444540b481266081c181c1251030034542400c0c00e80103000c20014604400541360680b0500c8110f8030b8980542d910b4021040c201c0000d9040100c002c040d0360000d00401d40618909000460741107000501c0e14010041500c0e1402030752a076030000e6000c5d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 215681232 1250 215679982 215679991
    0x14030307140f0a0e03010b0d060911010215010b1e0a02010b01120e0c1c020901060909050c1204021c05070b090f0301061437090c030c0e04090201030b12030c060a02120f 74
    0x5550f5981f540300ba035180d0061000010b44514030001e104030140c5021256103c80407207042c110360280b002c0000c01d00d0f074008510305550220350025200e18009000480d4101c00000d1400000cac0089511501a031b0150802c0b40400026200c188401c62503000c40805c46441e00d100c2c00156209200081903402c04905000902c0301c035180c080301240040d0081445a20300780c0c8000000b0301c1c8210100712144283c0300302a00410005505803600c001642010789030003018001a1007081c1407550441f0039001032681c0040d040d401002c2da65000c0d0759a550280d19040300000c42d0003600c000402018601d01845507205881a010300fa80404800000b0711081501c00000c4503501c40343d000d000320500c20180c2c19400240c00325103404e200b2a04100c1d403e0140d40884400d9010301d420001013140c19a045101008541c000341c4000489191500040b0003070509403407031a82040103100c240d11043d00100080820091400440380300d0344406206408901c203070100f5407450500500800c600130705030030016810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 215682482 1250 215681232 215681239
    0x10918120509010323040b09010e06010b09060c06011511010203040807111504090b0f01030c0e06030a1503050a050d1b0809010c02061308060112050601150c14030307140f0a0e 77
    0xa0b90749008602c0d001c0480c0a5000d0000b000310002c000400c6147c140443d4000c2c6000300901c52082c81c0c4015990725101070085124010010070071206640b00d080540b1b514512030021660300356920a0440554032008440000141000c2c1289030382002c14021640100c2d0b1040842d40341440315151513100240351880c031907020f01c40001d441494540746000d00094100c1090020342c100300c001c1000070420081e1800c3d03050505002d1003010441e0011030083e25840160342035a6070390740f014100b2006100410300b130707030090400f40408402d0141c0000c45038102d501c21000ca03000c105032140155030f810080781c80601505400700e49a0000340a1001500700741e20181000710100e413469002a80e150040d01080e041c0c09410740c400c01031400100322141c014144035503210420002d5840e610b48480d0140521402d00d00364017800d1030a07520914211020982000300c1203004151406019100c0e441510b0b040000340800b545001480c4a410880d140308071a148440e1900511407000d40f9000921044a9070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 215683732 1250 215682482 215682491
    0xc03030c0c040e03120a06050405130506040308090708010c1707140a050c03090604060309051b0d0212070803030c040e0f10050409050114010803070201020106080610030f1e0b0109181205090103 85
    0x58030380c6602001d8006c0c2400384002c504141084184001c85800a0121041034013581c03034000400d002141c0c1e140c0164251510aa46550380341c0801c1c64510b5950200b481586007100f0209010391010b81002000340d002c1c1210034039280c5440844070302000c10081403c400b400c02c4001d0450307000340c0003005002c60360000c0d030f814880b032200040d4036a040f0b0360041c004a5244c001400c01c1000501c64114125101d8044071504407541000c06c0110555001c02401200d21301601c10000000308041401000741c07004076566031400410240b1550414850303810382030050400720b80d82c440b00035a2507100c0d40e1900d40c810704903403900f030402014207115007003602c0d555600d404181030000180d00a5005e030403003000a555070800c501c0020b0840350f041c2e10080e81ca400407003c1c480e0000403070410b8001c590300910b00c4c80d001e03034090038030f0040700c40034200340740903141a00002800c1140c0d404680e81290020344c1c0801030035142c00c0c00301914400540000300000607141900031001e0013903026200030f00040c9000035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 215684982 1250 215683732 215683747
    0x20702210f0d1e020d020c0d1704061809050106020a06021b070902040f0503030f040b0a050f0a180e04050607030c03060f030c030c061403160c080d0e0c03030c0c040e03 74
    0x90408001c0d8042000060010880705004008082c3c02c07500040244010705840d80d545400030340b50114846040d1190b0310702021241800010907080b00c42c507085000c195681c2e0307920100580000c00258000b03518054000000030301401d54441d1301c0c121500c64002c0c1c01854190b61b125802503020b101c24001d44a001c000d8400745040070084040580414200180d4a50a0010228a0b1802d40d80040c1c840d078400c000f038941e42035201c0b0559007124111440d082c0c552405d40401e0721580142c00b88600501ca020409515142d07101e02045555448504007080e4241c5444070701d40f4420045034064000d80c03240011030040c5100e80d0052802c80c449180c002155600c0320044115402e0348d61080c0c40b025406401482404030700700b564001095141401c1d81c2c0651201e009402e10300004020040703001800724813036542409003000b04819a40f0428903aa42c540030005c4100410341c10187e01c0c403d1180c81d030a82e010341000000c84801445220082a000171244104409018140406042c5000502810 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 215686232 1250 215684982 215685013
    0x120b01152609060903042312030f0d0b010507080316200102030916080a0602030a0204030807080d0509030f1e0409050108060708090a03050307030f1d0102091302070221 74
    0x500304441508001c2480c184280da803840c0150140c82032109030401c010810143c4d140c40c650744801340401d580c0c5088039625100050b0500116035043c030490000040c40c0001c5880b80d0000c050056207204100100c100040c01110719008002c0c00800d4920200040f4081134240340f502c204011451a00d68822204003420a00c0c039841c100d00c1c24402d80d0081b00f4048880c0c03090100c41401d44c0320172000301c0030b1454094450b5035a425001c015282c82d41c00008190251280c1d01294003551300b1003006540c65842d07180c15151030703001c0c0c602d0511203860800403038413060012040368030407114240100d007407410050100d062030000c186c0304600e2510420000071094a00d0207400d00a0110b00301401d01440c26407005059220f0042c0b2151464000d200d258000a401a0580e600904140f500045400c00c0158140042c400e0350010114404030b96652884448150010604d40c2429070310200514020080c0000740c0c0102a4000c0d442007900710003c1001006203401c6107020303082401c41710340c0c0388854103c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 215687482 1250 215686232 215686277
    0x201050c010b04390c0219050301020f0a1205060609130e0f0706140a080a022a0c0406060305060906040b010c0804060f080c1305090601110102030f060109120b0115 72
    0x1030288000e41210844c40c0300e12180f00340049080740749030409000c0404a00200501c64920f0300030b220300202c0402c800c034044a44000c0001c1c202c0500210340c0c9041c0620b01ca019034200750380341d1002034122003400e64802200e0081d0343c056000505141d01300641d104c10446103818010550380210750b64001385620f02c82c108005001040640094680141049801000c41507181c0c00d4106001d01045040d6045a0003c8a254424201100145c541014484540e0f000542c09100d071a1282c0710140d00b80b056601141c2420f500a084601300042940c3c0d20040d0309417441110f1a0f03501030140d00009a141c18940c00c00c06441c0390516110f40d4940c115134950542e60800d42080c0300045000c1186072819800400300e43d000b4080b18203642c102807002d5462030079840d8600030240160484400301d100c6074040d01c86149c0490501c3c00a54aa10f0041203e10700e03402e04461080c00107004880c0001d44040369131541c440250481c85c0311400c0d07802d0680050720340240c80900e600708030b440c22000000d0341d0160784 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 215688732 1250 215687482 215687501
    0xe0402030f0f06120a0323070302060109050702010e07181104080d0f0c020d1106040b040306020c010f0903050f032d06040e010506031e0307081201090c0810030201050c010b04 77
    0x1d80c200785050002d20440ca058008195600a00d000200c440e0a01320002e6110283c2d076042c0b4141c0340a00c0624070510810104003484200d003a8042000da08050f00440c00505a40c00c500042046a483ca8422401c2c3c0362082801405c5810202c0e0034003103100c10312241452031481110101e2200500c4420110f20350059000c8082604000203030300c41c10b640001460140c52041c609034014580b00d8002401c1c54602603001080c2c15000003011015807515400d40d801840743d0f41841c0c4d15180d5a0406001a502071a041d150329441c020121040c40340a1007450740190b0181e403403600b04040e40c641c0e44011750015011030624540240c540d00c41e4a1401850100c2000da104c404005052443c1400306a03805004503a5440e410641000a01e0701c0c00584400d0306240c45891a00368070101710313040c0c1035211350f000c040c140b00c500041b60748010740110710181c1200c103105000c100c01c000c614802c44181d14155017401c0820203045003000558424001b030410002c0c628000104d0010107400901182c40d00343c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 215689982 1250 215688732 215688751
    0x8090a1203090b12240405070203040e100609031b080316050d030917090d050601140108131115160c0f27020f0d111b0c0a05100e040203 60
    0x4403650201640411007000900c0d480210f41e04201d01c0491301000000001c000c0b0b045c0300404c50600300c079080805064070010201400030002401d001000035100d0303000f400f4040c240b40840b00480c00e1240d00c2407514040310015511a40c800b81103603508002d20032942c05420760071825440110b42280300340020540442841040d00c0350055528000d81014900c800400905241980c2c01c8080b40b8410880380740341d01c51408650303641480c600040c107100750b40c030809041885540c00225010046010b4154010340c00d889803c0c0c81c1c1d440388150951a80302c00c00040801c180b004050b01d55080185517000354001e5104454101800c50324a84c41004903030006071054400358004020b501d410124880192104900c41480c1d1100c480e5a140340c8401221030f001c6140c2d0000d021440400c20700c0c1519a0701050b900d00b40b002c401500900b00640e004440725002c0790350701111010702034000040400d403644003c0c11011000b1700c0c10082040b0a20a1480002848100340800d001969144001c40c850440c4a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 215691232 1250 215689982 215690009
    0x602120a08042604142d030718050108010506060f04050910080303090709060b0705150a02040f14090a0506030a030e01090b0d05040c05042903120304030309050f07060905010c08090a 80
    0x28180d8a403020240e400300d00450f01c1010046c0351545008051086041440c13000074803000a0004c00d241c80030990140702d1061400e24180c0c038400082d008a41202c11010003444135440c0c880400c506c41c41001440c103283d8008100c10480e0b410144d2045511038980c05522031001c0d610b40c101425076204a50000842d00103003006c0c0162002440303160040c05404807441d040001aa850640d078081c0540140100c0d021000054400e003920340448015210007100614160b42d03842005401494140125220308161800101c4003141e83c480e4034800c0768020002e04241c8407946056a203183c1811100c0c2c100010f051010480208100c000d1850301c883c0d2a0010740751800e03013485030905e21280c210912490070324640f0403512020a0002c441c2c07070200007690b5052070700d02e40001e00d000000c00343d025201a000c4200000c0c1605580000c0807240610b003580c10000d8040745050300d4013103602807540401e051610a201d95407088140e19010f51084dd14246861900c030002001e60070316a2102c105030040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 215692482 1250 215691232 215691239
    0xf07091802030612211803150406050f040b0703020702031204060e09011a0418090b01060503220201090b090109120c03050d02030a0516080d05010e100602120a08042604 74
    0x1902d201882e000c4000060190501d00c044507502c4041e500d00e85c002008004611070305040d1010303c2060b100780380201107d200b542000c1c0e03000c20140003128160741092401c000140a1100c40942c1d1f032007140e000649070541d03600d0a40a07402908101c00580c0c01d4070410035603005030480c003c020001b42c400c40d101d44d00380e00c2110003044900e0038160001c0203a0100320b03002d841a48440c6d0107031000e0380c0c41d500800c5000313800030781641e008121030600900740491300000051115085001540242c0081e418a074524231802c81e0007038a0034a401d4000d00141840c2000c10446000e080540310006051602c00b001c1c56a9005011407959040d000b07076000100f44c5410130800404004640035850b203800a1401c01e150705101030503602420072040d42e80c2704442001c3e01045010320488a40c1140000100b100c0e50b1100c020401d00d1404075850421021500c401250030381c000070300003c1203100c1f074440030300d01010590212a408000b400448000c1c548900d400210413840a41c50401c5020024540c0c0710f514 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 215693732 1250 215692482 215692489
    0x11b060603061b031a010f050c06100e060d03020d0e010c0f0b070e0924270103020a050d08090d020f03060118050a0509150903160c031203060b030f070918020306 71
    0x1100f1010906251403c2d48001001400d2000094001006d007020a060841c1c69402c1e075040c0301c0ca91512840e40294020801035120554060003650b44c4c0c00c0d00700317400356218402d0108030f80007020054050b03485900220440c501c0b0b00694102c104040c544107103464070340c0c1d0b128101481441000c440d800160300070444565031104042c03115000032101d0014038200b4a030f0b512120021400fa003540d108038000300035074036211620008115000d001041c600401301d084121990402030008034130071154410300060900d40480050070070f0341c05c194894a00503a8804000c4600b01e007a030100d80085c0341340204401a5001d0000b207000f0200e040c10000401c0200c1401401c0354001040d071403034180b400d0203000c401d620009180c844c41105082441082d220702c48200d107140140202004d41e5002c800d403403410000d580c16400c00b181e1007100141c81c2845a05810340c02d0321014051030140180500005202c0510035091580040960400342c00032038861741803240c5021880000c4c0d101c590008280801d0f401c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 215694982 1250 215693732 215693771
    0x60a1e0e0703051b060f030601050f07110906010201060810020d0e070e1801090b060d0204060302032d0705092404020304030309051501081e0c03030706060303110d020c011b06060306 80
    0x2844c0c403002c0504030090f40000d0307041c0030358100c41d1041d400100000e01c959000b802242c024400030041503803114410f00d004800040c850b403080e800b030703117029000c00c0a03035005006031000da0301500068592036008601d140029040b4030790b4040c005864040200032003100380445c074003400b52460f5584207881c00c1199107038141e490170b40306840303685407003150340c01310380c1d1405130540020040f501e0310044002400028003802d003580010b03505000b2010081c000c0900d81c3c901c0128074a0042c089501c00300c10701c0c021078031400c03148500e41e04550803000090310725403ea0700503007850122800c141d075100240340201e404c98108a0701100403d44e26407000d0103210041003490b41d10030007414007010960400c1906c0da21043c80410081c52480625000020300b141840480005400501201d84444041c1000809451240700a0f40030440d003d102060100340411201e001402c44c3e00205030183c90200119100b20034580510142002c1d1a840f20001c0c02c24010350000b035000f00b20105a08045510040009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 215696232 1250 215694982 215695003
    0x7030b01020d0e0612070c0c0f05030f010515010c030203070c060c0611130306020306060f0706050609160c0f061404050a0506060102030405090f0601090302030a03121a03060a1e0e070305 82
    0x110300c400542600d951060100e800080380c5c0f1404200c1c684840500b5904500e101900512032204170401050725010761444604880048048074029036108002d5070803100141c81100d64600788154407205d5501558040300110301c80d10450345810059214901c601c100c6800c1600002c003009256410b000a03400303010200c0c08a041c00c0752030304802ca5421040740c10148402080250013200003035441e0789007401e4070010503002c10055940c0750b00785443c0c00204012039600f8030441501e00801c951400801c4110b09041e800d4481c1c1e240000c1544510708910416501216256180d0582601d00001410b02e50300640c4a00c00402d060496440d001303080047c0100340504662080c030003002a0703a202c4802a40003140110241c40b00e450345d1004841003403c41d00041d40500c070341c4144808240e4409000131008098003810005280c00001c1c6001e5a081000c0c81a810b5001c0e101241070091035078008a0170202400208104149107204401501d04035450607610b07030481e480400031b00c07030284042c1198 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 215697482 1250 215696232 215696237
    0x50109060302210604020c011107020a0e0408040308070204060f120b0c09030d120e010915050114010503041e02121e0303011203050c1513020127060309020307050907030b01020d 78
    0x502010316900c0e00c82e04810301a00c00801030035408180c65072291b9040300c111a0f4004000d00c080791904410459a0344090001c0b40110a00e1100081c502110604903004550100c022480c20345551a1014140c00204040c1d074010380d03030500098080b13002400d000c018803500014442820181c101680c404000800c028503558042106120650300400d10404e030700300c0342c28040081e202990b5080c00900d205c2c503240d5103075840c00003410f0a1028410b12000f00c8441c402e02405213a8036228201d66601760f01070501c2c0428020b102240014000090400700741380e43c04a40091a00d803134000458003d41d50701c412017241c10048211002180603001c3c40660300c040030085255524010340c00380710164008014040020100e0b201300f0000b000c1c04212950161000c040d655800c2c0190003201144860070128042009105172002c082c1d0342500070089480e0350003c11815508e481e005402070800408200d80c140682c00d00410190b5030281c9a900911070f90340c0c00210740c81c1c41000a880d003503460341701c5d006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 215698732 1250 215697482 215697487
    0x12050103031e0c0503040e10121203020c03131511070b031b040b0c03040608010e0f041101020c1201090b1b030a110403140f0706050c031605030c100501050109060302 73
    0x201c0d40090064a8040150400120340607040a0499079440c0d030410041c140c3c040060000740c109a101d00d101c1c010020210807104c22660b8119000c28008142c03002007241c4090340039904040e009a02410b411070401c82500e21340040e152041120a60f550840c0d808003890200220a060380401c0c0300c20b407000000010001c007400e03c2454003881c00010501c032001c034908545000c0391202d840959000b0945c11400741c0d1590052000c0720b07202c1c2c0142c0640000690908000103004180010740d901413151034490007466204c41e244d107a20b142060300c00c0e90541c0320711f2a03c14400d40307a6a0704124460450000010b24540350325206900d00e50203410f00074408030404190080044010481e41c01880d601c07400100c110301311001c10050b024030361000c1c0950100441441c45540d000c201407640c0c03862130b0140c9000540f6104141e03220b00815822490351b03401844814005444880e40429043c040d0080702d04109854108a00e00407542c2c422007503507511400100841d50b04031440034040c101d03a080650 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 215699982 1250 215698732 215698739
    0x910050c070f2a0b040509070914010e0105040f030b22020303030a050601090e07020610050105040620010603060203011e0b090d120e270c07020a0e040303061e06120501 74
    0x2000c4070901c82c0900700c00c03a12800081582151203021500000c0718421600305542d4070014070032a000f03441014000c0410900107101d441c0721707029040a0325491200328051042505c01120a011a0000c882c103101040101080c2014a486001e00441c46856004040c0c40d0010a5082ea105000800304024800100500041c1c6c0e003c0103507a40032286100004445d95001c0c012a030140d02e9911202468460070188941c1c0340d40450180d2040c021508184001603459004454520a5109480c00502c8140c0c0d4801161741100361440140b030700b030001003040c1e0b4690329000c08991007a8000035441020b0070884c5c00010204450790018600910311a080c40b0690b00403030501c0c180010700a0408140240b90300d0302c80c0c051110a501040054420a03043d41c4504510082100d50848510803607911000103c5480b0b044085901c42c95018025043c0985400e1f4010700e010400352045090507211100464520440400103644825074403480c4116442d006010740400030302008014503904080050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 215701232 1250 215699982 215699993
    0xb040b0303040506071502040e0a050403021c20011506210207030c02040e0312100f0f030f03080c07050f0601050405060d0b040b1302060d0e0d020d0219080904050910050c07 76
    0x2100c500740c20881b01142c4280c0c040c00d8200034480e07034100c0002c0000600a11480c3c49056001910032480380d0201c442c2844c01010a040740c44071020000c2c0041c55400f54804041100840604000b580400209440c00203a070101480c1c0d14030303044200062072104600c11040c030392100b041c0b03a98000400131860700d0740d241c034000e00c030856000c00071b0300071521010b1000038600d040085404032141e030402c509040c00d10318000c800f102054818005c55080c007401c0442d41280035402d440440764010150a2240950744d41503811041c000d10000a51710306110000210f4828055954106200c00c060315066040c58100400c0f5580600114040c200c0880d80000086004054a40290700100b0026680c1d544410710701103038202c008000c0d081789000c141c4010700195a042014400c4504041d100c040700022401ca82e20480e0501d90310040e0f10951501c144101b050400000b850b0050020741e1408001340d0100b0191201514101031035403181c3d0141504868510455802803d098038491a1a0302c0351a203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 215702482 1250 215701232 215701237
    0x1e1407020a110a15030902040b01030b030303130309030f03050421020f010c0501060b070c050418050304031b050901060f030509010209030a0219030209190c02010219080603150a0b040b0303040506 86
    0x1d20726260124061899500d000e0f180004050742d110401c03105044d001e00402500141101702c0c0030740d003030038040090b941c000e0081c40000c0101038015810342c1d40c0c0e081c070441c404c200248180c0a016040302c020010840e4841c4034040036020741c481a50740d40c0b03011100c41e0130103812014a50062209019040181d035004480d4545000034a400412510306042c054010b0102e680a007510110000e83c110070042400030362012100300311410409101c01281490901070302e800004c20329001000306100080035a00524900ca0004460341074044e11003004c5520003030280c202d02c001c50403081c040c0038160382c136014003075000003014020350500c0150004241d0760504800000d12034014181c41d0103010342c01740e090303c005540050580c10700e82003c07040d02c011814500100c00c030444c1406130070151b040c014002c455030850103080c00e100050160400703c0d21440060b08042d40341c0500a50844000000303140706003d06d1204a0016600792040300304412218141c2c02d0340d009070000d10040120740d450105 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 215703732 1250 215702482 215702503
    0xc0206191a090702070905090d0e060405010804080d09060207080c1c02070b0a031b0906120e03090f010e100e0a05090c030c0705070801050103081e030603071403101e140702 76
    0xb003540580c0c9800409a040c0807840d009100c181c0d10b44810044085030020303140d51b042107640c0b504004003a07003005001035445103000340c0e400b00310408013040002c0c40c0500244800003c0c1c00c1e00150320031040c0d80d441c081e80d001e2417095134501d0010a032524100002c0c0814003501d80e1034028552410040c04001c1d4440c0a54403400000380d201081d203442d80c9010780c1040c08001e40307541e8120104801c00b040035015066901039607000074801d161088c0c00d16030034810040b10b0048040210708090f0104200415440ca007484141040705800881072140c0300c1c6101e00503088429103800ca20301c9004010300c1514030481e8800e900c03c0003031009201ca035003004001c40c7e4000d05c221020954032442414420318002e1580e014441c69840d200000040c82070070409040210001a150344499444c034030703096a41e00003a5010765041e0440c0a007080b130f41c0d8400583e40c410081c0a810707261400e01d01d200c010101e400c1a149012801e1000d5004514480c881c800c2700221290b801c0c40c18410705141d03900030354076030742640c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 215704982 1250 215703732 215703739
    0x712081306052a010905032109070b070b0705070b04050a0209070507080d09051515030607030615030c1e020c03010b010206010303020a08220602031308030415050702060d0c0206191a 80
    0x42000c0403503084d0004071459400004071f9039660501c40c90118890005102032548d03111040c04a641e1104c0460010200d0340100044ca0801c40c03d038071b441582101c041c0842c1c050250400c0000000740c0540c945a10650282e0041c054140e52030041c0003a5500090255040003c20080c80001541200036140145500e000005020425290151401716065002000d1030560303070030850f91180c3d840010b801408180c007030b60050307100c01c0025415a40030303000340132501110001001c0341c41e10076400000704000ea0b25118600040300318450b880b0b0316800c8809401078001301c903080324a0409019400704a50300784010440d9614607180207460b10050071008003c4240011100940300c0e0002c00d50300145003100303490819a640301c0001e0769aa03c0052200c0d419412440300103020b60000c000c0c0e904846104040041c1c045500b801200c856100c00c204990000081c03001b51507241092090100b014031940052007141041c1c4111540c400f01802821080c030308100e02742540080302c8182544c11107094 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 215706232 1250 215704982 215705047
    0x70f090e040c12050610050d020d11150c010b0102012405010f110303360d05070606121b0b04080d1409030f0303100b030f0402010c0203071208130605 66
    0x602d002240070010b90712521000301c000580005102c0045201c0e0301600d5030114034010142d48a05000107005040c03406036104903504081004510409004210041d0081c002111860a4a0818640d03000074004038030340da40d500c86c0031110f540c091142841e006404980c2100c1c400320003001d0340d01580b1600030941040704200342c10001724000d0484100301c0d801340c420780b900c0c0d19000e05420300e01e01460401114082c49901e00d8001205000018030b401d180003400303050000e40c03a500c243c4135680320820880b8641c3e502c4800061004002c0492500103100b802c0142050081c041c0c90202c00c4038a401902c3e4045042104101030f2900085c028070101c0346007005911440983d0f4000c101d4098a00040e03018000c094080c5414280031000398458170705a240100703250389804008440380011030f000008a0b0001c1c020502545c0074142d800c8051f0320090071103100d030b40c0301c0d1320018824400700300840d407034200881c045001002c0d5041000140c040b61800500381207114203603058080d49145444481f000701e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 215707482 1250 215706232 215706241
    0x5130209030709090614060d050703020f01050c070305061602070b0909190f05010e0c212a190806060313140f240103030206010e1509040809010305070f090e 69
    0x40c440b02000340800a001c00011341d0314200030001d0403804010010441c05640094007030314080c0c41404000c2c0d001030050000c1130555082c050400001041c1e02c1c1808024042c0c2c0300e500780100480d0025600c142c02505480c2042c108000346000b0160010040d508804814081c52500c07d0a0302d0300084111b40380e0405840c0c400044540c403000f489185940c1e03040080c4424070300220f40195040360a21421084184c0e07440000c10401e0281ca520740041d40920305104210800d903819458010a24034040100303540711300c4402041500301d01c08011710f54008110944009600c0f46c2c00581c41d1010f003408240b40c075000700000e00e184002404001240d10319040482070181c4642d07050401c0c5914401c66846d00c400c0004199648064221150740b01076459403144040950010141229455001801039074200b6004400c8854010b003088030014450840000c0c503920001818081c0c1d019000041d529482040010181c40009002e2405e00103c205140c000a51000104041390800c1720009640d440c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 215708732 1250 215707482 215707489
    0x6180703051b07030804020118080d03050901020f0301120b0a020f12131209090506030109020f100302090a1203200705060705030c030f0c07080a050c0f01020a1202010c11060105130209 81
    0xc015105081d150350200f181400c06400c440303801d0185000340c03105e803405141f1154035412014580035283c0c0d15080065503484683c001d07084a6000300340380e40054244800644404080d030000d070300c10000074602e9200c210501c640b034500c5039005100e4410942c40d2060104c00b505640c400c41311101d49003020300c0b0010307100042c075102044030141d005107041703286200c220700204108030360b0040710391051601d03001c0366181c94140304085030241e020b0010a0a4120300341082111400e0340306800a0580801441c45165071b0402c0c0134000e400940203405c034842050400a1014a945042d10a8040305000000301c00d00000307291340172078108452166a41c10a4a0103d0031805030181c40ba48500c4081030030b03075201c51440040e18400030314200703e410055844061a0b034810034803038054510f82001c5c103c68102d08000c0f54110351260103004035907102500380d55898181d44034907800350050f551a4440d05501d64000f00400b602c08200e00242425414500010340b1219035004099540c1c1d400601e20003280c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 215709982 1250 215708732 215708761
    0x3040804052b050304051c0507050d0f050111190f0c1101051c020a030b0d110105070f02090f041b050114070321090b06060708161502210618070305 65
    0x30001c002070b01c140119250150750390b005401114031542d0421042188281444e4030f840c201500000200300a526020910082001144050b11850780405001c400319200340213205451001c0c11807641d0b261740e0f80007520050303842e840c2071904100c040310401340c2c81c41d4881d00448038560000c140388441c1141000681d101e116448948017a4014003449800c0480541c0c007501101b007982d01c00b0700004104000b0030a1040d004c1c80010b2801c0490401034015522441c0a041220b21880300100f40c84025000036014641c11503540c1c00c4015030900b04020404d03030148a5020036141110812424103120010300480c07081c0b101c5104020001c101c4100740340c0b0515081c0c9d18851418624152064010300d14400360042c03c4060b62212098070203d0201e081020031501590307009a81a821b21000f0f2002040075801c0e610203465801e00340012050006c15803000304590510603600c0f044800460303554415a0000624203071040208013244408000b08907445a80022076107000945a40c5518111341c054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 215711232 1250 215709982 215710039
    0x40806070923010e120c12030a080708070e060f03060a230910090504050609010e0606010503060f0406090f0e010b040204080a12031104060903031205010b0a0c1a0411150304080405 79
    0x51401c900301280c240380465810302c1c407507050364843c400362581c0747c51640e01c1c4544001900000c1d51503000410640c490313031003240c201c5864607290500c034405100154081d00055500f076018031000040c41400c1ca00390360100d00410300c01c0950f4000800a01b0025007259698139000c1c05040c42600080c06814003240c01400f4085e450020007140c00d00c1c0c10440c0c4d844508940001083d80303004400010f628000480501c500c00c140d449514564804c07042c000700c204581400c0b6001911205c1c0456011018054224064850103002550320305d0003030f907a07003510104141c1500552041100780135186000c00c24401540c0c100603d10381c0f002c1172800403401050002a41d05041401180c045159940045050308036800f07643d03407031140340407111824201c42080c400c0c1903000e941008003050b40e034040c40000d00d82c00d005846c10709094a050b00d541d4038082044400311403040c099045010a0715002c04056094800c00d500c0301c0c00d6140c165100000da22540c0580c5115901d0800446c024200d1404820810f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 215712482 1250 215711232 215711239
    0x303030a020304200a05010f02010e10020a0314060603060d0c18090605180a0b0711160807122406150f0f050906040902030604110a05040806070923010e 67
    0x12480c14a018a00940040d03a080716410044d982c1840080390b640c03164921007400811001705c0500c2d010040d40d00c0400201258190354943c3d05514240509110038081c0c80050840540e43d0407a0410082c102c03040d04604220504940050041948406040c0c07607203c0f100b5500100500300c50f0804000003510341c0e100744d4007042074941c1c275200540ca07600201c4151380705050a009035101d50100640008242ca4030640551002c03013000c0c04034503110f040d81c0c0c108650741800c0842c003081e0400740cad04140501c031510041c40b0444508005034441001000010994004501c00e60032495072404218004500311001c40c8000345094840486030b64880001092212030001881d07408034806001c3c81c01000d1018041510100744421a0b4041c0049454200300201010310306810400640007d4201a01c0982c00c103580750780c00f944101004000f019a403a043d2640c5890700d01c1e1103c81c6180142c003c1412041102c01c0c441000080302030310f030341c0030390b012601d100201440c3c0c0d00d00101d422043c3c180700c0a50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 215713732 1250 215712482 215712487
    0x180e04060213060e18090309010c0311150610030606050313020a09090b150a1409041704030b150f0a0b3105010e04090203060615071505010501030b030705011202070c050303 76
    0x94240e001344006040040680d80c145d0b0346080310407403c1c0c6040003258008070f540c01c00c01c0070a84a40c400c03110905c80f07510905101d60800d200040c0980b40200254100e51100700900900640b80390601c040003081e0000e1030144207442c113013840100903000c054105407110790b42e001540119560000700c5006000c840d00c007000890b035030b42841000004c05540d42c07203909006034480c41440c1040035a07481515524503032081c1d90b660401c103010454600600585010007980d5540e604d2510000040000303500800c103e1170242000c0c00c1200300c030f45090740301c203114a0901d2508400780d00c8507010740c41210111070a143d250341020034984010100e120403666030a0002110080c00903401c6699020782e82d0a85c2c94140c0790407910203000489100c04800b80d4198440000900d1380e141c04c0d0000b030000c80024080da420320f07030789586000c2c500000f01e2901310100c0d1107400521165034140320b15441c94404038010a50b1619000002c0d24281442065000345500090740809000055202c000100000f9040302d6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 215714982 1250 215713732 215713739
    0x513061a041428140c220303090612180305070515040c030b04061b021b010305150d0f120c03030506060310061b080c01090c0b040b03060f150c0a02010807180e04060213 74
    0x740d503a00c2244841891b206541c0b070140c05080c2c01154909586e07050721401c055904002040c1c03030142d900c140748606030303032200c0300100d80b4008007400082551190312400d84949252070003900380305415640c200c01c030852401304004a0641c2040e07004680c1c201c0155603103500d0f5410907001a00300869401712b0003420071940e003051540054040c101c446040c41501f51000d00c2401102651802d441d10170700d8500051440314285001069109450300c02c200a01da41030040d501eaa14040c0305030040008200c200d0b0f07480040c19050b000b1254001e034119000c61840c03a169105d255001c01ea80a84c0301004058510254608652702d02c007290182c00c0400380d900d4010070b40c007450207401480c000312006040e0100026544458038191000e4501004800703007140e44420501281303810000345594000c032000c00880300c0d11410001007140310103520140c80c1c44611400003411020025041108004030071410100100340d00902006545d50ba0410440e20389590501c1c20103801001c0161460085010000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 215716232 1250 215714982 215715001
    0xb030f061f030b131b0513022107050304050114220204060b0c06100603051e071205090a1703070c060e0a0c0609080106060c020901090513061a04142814 67
    0x61140d648544001c098030300b174010508841c2c0b203041c031500360888080b44015084078202e40203440b070b14403101080e400a42c2e582c00040b000600940e0100701142c0004188018040280a104051000e0909010b00750814001c41805008c40d2441c0392403d50500328003004558441c0c115900421002e214907447d401d0302a4050f4a070380040e60104541c8010001c0061114042d0103864400c0e60884500c110341420241e01d400202d500400d0359080190b20518a035841041f0b1082c07a015a00010003080300341d5043c42d0841004003940201ca01c2e0002c140300b0000e50326403190750710307118560090300400c3c0b03104619000b91500d03980b088010080c0c108460b01003030040c0e00940c400201c4d1040c00c001d20800d99214402d03544c0012030300d4082c2d0805040302c014002e00e085074101c13681020110010400d40c5045071586e8040b9100c3c0701400c042d220324042070300c48c0340c5401d000d00c0441c64071909000703a043c10680c0c2244580c55071450f4952001003071020401c120030445e8050940c107149200ea92711039282011a2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 215717482 1250 215716232 215716261
    0x8030109410105030d082d0112110a051f02070e04060b0102060708010f0e130203070305010e0106090204050d240e07050a080a050d030e0a1703010303030b030f061f030b 74
    0x142140e00d00c059000042c035140000d40507175214030310f481d0364400d510f0303038138609901120030500c2407003105000703c04000086c840c00f50036008003841e81c1340840d03100c510701d8a0740c0c80400c5106c0b0a03208554a0800384050359a1042503140c01581e4026411034446018050782010016440010307103641d01801c00040c86a150000301d901002642983d15070341c3c1d004415a4094401e000c0d031002016404070078403070340d03801c84070140c0c202482c0d50780c51080c044035034000703403070b0410a80084580d651104140252441c0c00d009440140044000a50505040c6804074940c3d0340d02000291454001443c1c84ca648814040103140c4d40345101410300c1084102071401e682e540300b601c0f0f000d0140c0200700c0000f40085010401c3c040456000300171b00210b240b15042280540312009000803207014020007035000500003054040f5030794000035119100d6155050290445504c0b04038240207403c01982c181e2440f0b0302050701c90380308040d010460281030045441e00000307880d039000184190030746001d101000f0a070601 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 215718732 1250 215717482 215717591
    0x30d0e15040b120c0403080f1b0d11060601090815040f15060303080c030c0304030f050910081b040303140a05120106020a0512092b0b0c0403060c03020708030109 71
    0x443c040e66494036482c0d1805441107100241c40310308140010600c0401320343c000c1104102c841c04007102d0480c01c8100c03504003211000c0010203c0c52207000e80b4003101c0c062101551083d02400c01001c001d14148074551030b00c00c0a5400c0507441c00341d20006042144503e50404200c0c1c00441402e10039480c515164001d20b0325003c1580880e4607040090088514039044074820f4a82805090440d100e0350f42c2652020340e21002c8506000040c01500c111b07448200b203041517a40d0b43d80d02c44880e4104602c1140b51480d4081c2540c0c4c0036101008203001003508105500412450440600d40c0c1d000e02c2d410071502d60003030b440103500c200714040002882550000355010402e000340b00781c6201e28210484c0740154442c600308250000010b207604002800790180000d6080c00681d50072024000540e40c91000507400c41d4005680c2c0c0d00440c081c01030014501c00c81c400083d4038101180307408040d407140c1103036000500c01c25604940340c00010181e2075159a51f08071540003401004a50140e615904149248505 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 215719982 1250 215718732 215718757
    0x230a0501050604200703020a06050903130b030408040303050c070503070f060f0314010504090201050c250f08060a0218040c050a0e030102040f03110a121209090b030d0e15040b 77
    0x1c00708500e803810388500d4100c124030b0b01454a982c1d03268282c800d120b4024200540030750280d03020a001161160181c10b1007501404003443c0d88502400010a041c0005d070001b2004120078420000010202011501944c0d05424501d031038004020783c29260004903042181c0501524100041c21504814101c0c00e0714101e8540c551103c615010840403035000d01c045075003d08426004121900705640400f801a0040c13500504e000500c04242c2d2500720942d02501101c21010341c40c10002011940030400b03080c80b102540899490020b155070350b04000381c42603240682c0080c1d814030102d07550345d40120360200a082406481400c4c080506260413407050180841e412a1642d4620310707040c422902585c80c40c0c0420119103003541c0714440c0c1d070003c0500c10b681100701003601081c400052241600503900ca10400707134100c16910001820546960701104106040402031080c5a6000c50080404206440c00c0316805101d840050b0014101c2c0c0c000404d0180d0014000c6039800b51800100b00b850b4084 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 215721232 1250 215719982 215719991
    0x70308090109020a0e0c040e0103050f06010e100324090507051908060f070e06030406050601170403170a060b0c03030412050705100f02090909060603010e010506100c230a0501 77
    0xe6400340c00c2ea81e0840c402503000184c0f203424849408500030407900002c401c1c280c141069252900020707286001c0e00107070b030140d000c071003a54220745081001e2030140402c4a4814950b0038506140c80764400301e808020721807000c0580c103030b40d182d9142050f03240d4030103c0e20040c021100e15050141d150006802103501407610b582001c001f041c010312030102101d05220007031055136144040d20281070310180c40d407010013601d07228400f043e43e1000041c2d405503014400015003801c100b40050050710f0201511083c0005140c00c00000c242c121044a100c091401c40100b940d0f82c3d0354031724500401641e0003c0b81a84004103a40c0010100040918440c6104071401c402c664182c55064401d070084007801001030380f0622030b01b102400301d07421103100080c1c0d002e8090705102c02040040d942c21b6085505401c2a88003104001007840c09004100703000410200030082030074401e0104580b12180780320b590501c0b0031101c8210821481e40c6e8036040000c1500050700c0c0c48948602065182e001c145015a076542c00c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 215722482 1250 215721232 215721241
    0x40e0c0d02280e03031309270c06180302060a0507020f030709061e1a0c010f022b09030503010510052701080f13020d05150a050a180203030d050619030503070308 71
    0x490f1070070369601000f590203500d00031080b009040c4000000b0030140d0101c048c032090302140890034810310b200d141c508603007604110000b07003146011403e0801d00d101c0b001042000d84c0b00d40c0c045070351034040343c40d15590342c0c855400800c0581142801c181e400d842990350018400c50290301140070340b044000341516006010301b2009140303d89000b00443c0da001258841c6145601d08010615a00c0000c0041560000e00000c5401c0b40c0002811040c1d601c1e200120001800e062002c6510401491004014083d00b94800a1a42c0814024a07018010b0110355003480b03401841515103600b25a00c0b401a00c0c0803101076003600b80c46115040b4081031000c000300e106509001912441100401d03080120901e2075020001c0000e00c13000309442c01e0007a0081228a505150141445452010780101b0607081c11903028049a804e0058203604000640c0b4010050781e01000f124440d62242c480818251140400900010000d8011407004519070000008200c008400391102501a40301d1391000d558 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 215723732 1250 215722482 215722489
    0x503031b0c151b0403051b06181c0b010914060306071e0903060c08160302130e04020f030f0607020d0c1e14030a020a020301060b040e0c0d02280e 64
    0x100440307000715402c4240384540c580680c1d88043c0d0f00c0200e00d8102c0703a2080702014181520b9005030016107850300610f4925400182c140d030390080905080d2407840c900b210a040305902c05122080d142c1c880d01c0b92000c3c0094204880715068032482e040304c0c01000f1540d4500c00d03e80142020300004141c0f644000c0040c03400d10340031906501c640c246480300c02ca00c0018540c50400156032010040c1480404440800442d98070301c198030040e0302c0c50303c86403800d00b0055031018a42c5050350401081500402049911441920344101180c1d0181c8000f9141d807164800078600c030040c4036450b078143c031402c20021010100011918012040c640964424401c1c0c40c0c0c1c00c50b50354042c1c41002d010b29001070305038401c07a6200f080400200340104036552640d881e07102c00900710340c04403028400503404948100c043d40703000e00c5150014201e9040c1d6524191030400040801d0000402c0d200c0c0b64040440c2130f000d2204c4640450364800c584c002600c016a0002c42c0400d041c00001c050100060141e8460060509 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 215724982 1250 215723732 215723737
    0x80c0a050604090e031204030e1212040611010f05070503040b0a060b0f03040c0f080f150603061305030403060606080f150f120a02060f07051c050711010314040503031b 74
    0x5030040d16241c0752a0614142101030015940c0c030b002548030070426160102404803003a030103184259143d0708294003042c10000d00004a2001d46807541000c3d06a400008044080320100c4220342030500b419901c0240403401003090903e5200a982090100a04030703a0000c011881140715488050345a25811800411030b41c09004030000241c08001d4110409000c101540d4000c1c4103400f000010b81c3c139003928016a075002d900c1000242d03c89403640002c2d200600c00a0000d11451050240c40c0c43d00d040040d5461a01800081d25030007812203200500100340104d40c084c50700a1340038810f01d5074400d40207140050480f00b000d0403160460200c1c3e4800360501821036468002000b0402000c070f6501088048021040d00b0305081c80359604610058490402030940142c170010704e00d0b142e90f903e090060511800300540042142c031040117a0341181c1040030398420700d070050b20805841001500590040400003400030031000c90340b040104100d000002144103514448010b610032034026044001c60 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 215726232 1250 215724982 215724989
    0xd02030901090603050c0c070305060703240b070c0f0e060406170c01050906040f0b0327121e0705010605040f0b010e090402041806051f0b07060e030d060f080c0a 71
    0x1d03150700c108100280c840c5c0c210781e811650300c0403c5454141844207542c0741c500103a01c03c865076040802041156909441461148010404400500032401c00500d00e400304a0103030340400880072441009200542e0b001c0d0300544130203945a103200740c8919011400d00c6041f11401d01c0307282420404a011111011000302c11201389000300113420f0b2140066a807904050100c0e45c10032002d0000103a88000045035000820700440c0907903036410201490b40d294041010991600d0038401c003080042d480008001102842d5404800d03200d048130845c0701450648006003040404e0041045c2c1d0a10906500003821180121020402c0006203074007081540c03110740003030340401c5c00c5404d00002070400d10206a801840100002201c04448071000b500240c11039066031116a60030420959041c074000007007158042c06240b00c0c9140c9460001c03051882140d9004210359107500c101c04070400b080056a410300030100043c441d0795100c0d080601029114414001280b05400d480e204604000c110b07407059 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 215727482 1250 215726232 215726237
    0x30506130c021504020f04020a09140a060807030228051b070515090a030f0b0a0f020301050609010507050a05030a0c050606120a02120703170405011d090106030c0c0209180d02030901 80
    0xc14070000340351001e0383c80040c8140c1e0003503174440e960051a41da500c01080c00128507240d0000083c205030740e45508030007408071b10b40030300c0242c8005d015a0303070001580c0f40e00814910b4003598070264580701c4240c1c000440c05040310000200f00154200d40c02601404400e00d00000014481c019030403c250394041c07034441c4582024030003480d000400880f40040050705c1e405004071003040d9036607442c070600201d503a00a80e18080c0390014031414082e1030041112002044ae0154115414100014420300c50031561905004001990358100035051010302410380c0c1181c250fa40721901c07408058462150540121f4803409000d0014a42d440c218407144800401036000b011080070590a2000802c141c260560702d600c620b080c000300240f0b03a100c51400900b1842c0c80720b0345540c5441d0006d00f8203150020302c1e00900100072680c080c02e440e400c0403141120070510b03001c5a204540641a1103290b0751800203504150b2440070841652040381e0182c8401c898041266060381d003910381243c5900403890701600 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 215728732 1250 215727482 215727493
    0x50c0414060f030307050708011b05040312050c01140a0c020c120a03110f030301060302090f0d0f0204020904020715020309150112120e0d05070510050c0a021201090203060403030506130c02 83
    0x14102400410b20030b90303026040f02d15115441e21345030315000d19540547c055079120414199000c240a140d40100c0c0485c0c1410f600341030455440308c15031401109601c0401c007000c252032508000075000302d005209100000300391424681d03110005000d00103141800b42c0b20300d503080d8a041c200141c06400c051401409400c0703030720056a0407180780c2d03c484130f40e001c80e02c02c2c00310300d0040b41c1c2c05000442c020981ca80303006a65a10042c144044c92082c100000d01c2031623501100c5012407a030b0314000c84481c0d411180141c1d00c00d44100003034004c0c000d10710003600c8884582000c2001c050325500450140641600312030003500c101c0011070712248240140081d549603a0005c400280742d5040b0000071060904064880305d03024004038001e8460b405c01a5081d42c0301800030006402d00e40c1e01152a03510070300d04980b03407260000000e030340c49503203410082c0a107080803030b4050034540c01e600140c02c2d107600606aa4443c10300341401009448242c070424031030385e00209a100da0300c89501c25007000e00300b543c01901 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 215729982 1250 215728732 215728741
    0x3060f12020f01091a0703030501090209330a091a09060a0f0c0b0a1a04020a02030406211113050f0d0209060310020c0f060108010c140d0f09060207050c0414 69
    0x303400001c98905100e500c500c049009121503210800035031710300f80340300c2e111210790900805640060f40700390050740c41003100f00e00ca9211817800c9a0722008124018842c07003d0742d00020707410240d0180b1a03000d07880109032280180e81c440b02d01c104441c80421003880302c20702c040c80012907114010603154001c1007048081c0e0954004c45500f80d00407174a04040c1c03c8070030705454840700214112241d4a07000d580d806105000305541a40e03640e80c10040c1d600714202820b100c4007079a00c3c411800b661052202d020303040468409903100094403400c80341d1040c00707090b00301100d00f0b01035040317a0304821609041010101e02c50410b60410600444028240000c1c519103809101c1400c41c05401290036000e07151100381008400d0000302101440b2000800e030600594000c00e06101060f0070002c0540d0508080304039165015043c1c05090300715480c690381c0e030400e080c00300300104088540d0017801c0d03042100b14824011a80d029040980c00b6000303070b4800f001400c04200403600281b50203d80f500d020760118 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 215731232 1250 215729982 215729989
    0x1e010e0d0504050112140f090f01060b1614032d0906040b07060e0109051605010503010506030f100f03050d0f0e090411010c060f0507020c090910050705040509090d03060f1202 77
    0x510b14070881000104007075514078060003850200d0307e400c0c80c0780038034052080f507000800c441d801801e804002000f445040024803040340c0300b1001001c4504240000400901900301140d8009194000c00c49564044101241840841381c9040a698031903800c8040550f600704c0c4110b415203c0000c1ca50b610309070078001d140c011508110006d0b601c55603a0301304080100c000b40b003101c010b240144000c200001c0c407152031104680161b00b0007410840103000400054030382c0c100740d03900103034200195201c0d80e0340c000610040228550128003030211108001042c41030110341026942e0207039a4400a60191a42c19242e50340c1b03502940e500a042c200008000ca0403001e5100244007051614007400d019039201c6c00280c410900703210055030794510500c228590100040080103500380c80c182c207a4a0010a03954594802141001007a41c03074400103528a4400e1003110003400005180360010f0a0044c42d140e80d86401c400000c002ca46003510105141480a1001040700d10480c00746100300015402d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 215732482 1250 215731232 215731247
    0x901080d081b1e0702031f050106091409070c0c2403180b061c0501020c0105010603111207090306050c030f06030f03071506030503032518120f051e010e0d05040501 72
    0x1100f2210103200c038000580d0103000041c2c0c14083d50b80c070350140b42c00b0600841308940d4182d100d282405080c8008120041e20440c290358800b0701147c2c0c80140e0b5481c140260b800b00054840201042100709020a048200f04002d04690b80386c101080e20041c0c10b000244c0440701288a80315080c664a018600003d0070440708540c0004007900d5100e0003e680d00f8402502c00003103c003280c1c140d4011500d900c46140c02d110700c600400309450705000541c240b0000740780c24811100c100e141011030a0002d404c00c0c0c0502e841070011079100390100010300d05880050600d0b0401e48441c10300215000200e4000d1074005000094089908040d6140541560b02c103a01d00103e0051f0040c40c1d9191000000400d10910241d0700c907412048140da0f031050021011401001205000c03000e000404100e00d14010070801264180c400c2481c0c0c03030090310761500b480d02c02c0c511100d00052640c031070054044001e00c0700c8400040c03465841300c000d101c0c540c41c211945444444413211000001c006200c104150340c070407080c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 215733732 1250 215732482 215732527
    0x1020c06040e0a1e0605010809060103081207030b06031014030c1f030e0706170705070b07120216060c020f011a0405060a17160e0601080f090c0901080d081b 69
    0x2546201803200c61240b8000d111140b80c0080e61760100f0000d950308010080e42c800e24020281c4400e60440d6a211241d010f441c3e0b140c02240500c80004180034069840b1601d0b205000303004c1ca80380d2401c00c040d252110740300d000c1c00c03a940c002c1458201c03050070002140d21800000401341d40341b180610a10301c0d103040310a4840810180c5445219250090611008010340380e02c1e9154103000183d1160440203400103001c1d10f04200c820421030b0040b803a810b0300309030410750314a0411000110040342102038040c4034505010040b000c2416820821164440184022503800785c1d41034140c0e615400c0e08841c0c018884a41790308407a5100c0c2428070b003d502c80d561200d4003e00d07030070201e03450f08200c4400724101480d81200360b00c6040c61744800340310308040c88020704c010112012589480700000b032400d840a442500c90340500808142058400c0c000314160346405400c648041d030b56401410358890034030421078081040c403404940c903041e50410098001c00c00440d40c0749044901141a88809040340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 215734982 1250 215733732 215733751
    0x6150a06050a021e0c06031821040b07060935090f1c0804031104112508091005030a050a09120c02060d0e0109110a0609050f192301020c06040e 63
    0x5d41412140d907410300594042c004250b500854001c82100080c03034004c3c0c940302c400001800c2014910705030300d445e003128180d508442c6101d40750351852804402810001c1030041110003401c0368107000e103040a448034448507021002000f1300c0030200c0401c440b0320503800080c0c0c00c603072409100441410140f40c0c00da102e48140050701c18485007915009003030b402680040314004503800042c070140c41c1c14000d1003600d04803075429500e00540c0c1c817120001c90810f800c0312000d04d0030b503443d01c6050000d641d05544000801803d402c0d120156024014029030044030100c82141c0351030045105460f403440b410202d1036001802c40c0c04c48242c82c02c00c0d101400342e03010483c0e0201c001c2028140912072402801d010700c06002c0042a1054146082c0c4081c549101c0114003806a0503410044150312014071002c030342d01034826000316040d52001c070702c00c1c4201e00c0003501070300351755280080c0203801c0d0070f640603d00c00703990f60a2045611b010b00491b01ea5008a40c140d0f800582030005110203044041ca02e9081540d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 215736232 1250 215734982 215734993
    0x60f0501322e0801050f010c110f0a06030903020601090e06041e2009070c12030b0a0902030f01030b090307030c02040f0906090302060106020d092102030a0506150a06050a021e 77
    0x1403454640e250880d82080c40072803030102c501c2c0616007100034107000d0001110a0200c0a011a0008014400740320010300703c01c82c078043c4121140c860212000b81c8010142c500c1038030136103d1001501901805404500510600000040a801a105402c1702d5003c08024100c142c641d51107140d6000c860300e900c0d60824002c50540d40001d41140900d55640c02500302943e254094442040140b0300c00420039030600003181c0354003001071800c802468540c21181800110031845401003540c4038010b0304030703005041c03000051207264414040014101c82c46000c0d00101a035580170f09984901400c200180490641510b142c01480c01ea040b202110036140c00c0010900166200d501c1556503414040d00542c0150780140602035040c00b00f07e90340000c909042007120324160702949481940030f11240c1c505030100b200c4046603800d00410304411340110032504942007103410705422481e010001d03480340c81c100720002021340c014410f8841442c2550080c103a103000c08288501140b1030380309054040e0040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 215737482 1250 215736232 215736259
    0x182103061a130e16030b030109020a06110a060f02030906011a0301060c0f0206070309180b0307030b060402040b030a0f0b012105060f040f0b04050601080c0d0c02120304060f050132 79
    0xf80b40d0301e82c3c8241d8221404802c001d12507a009030440f91500d110f00c1c040d904000e081009a01e8190070401100c81d10b1414003a2103983d01869802d044542c80000c010ba42801603e034214425a0050b600580c4210203503011079907030740c1c03003200c0000a04081205c8160140010400e4038010110345030740c207001e40c80c0c1e040300410941c0080c40541c40070b0310450225860410500408000e90081c25078034200c21010056800b0001c00039994051078480101408000030010704c2a88458054070300500740b5241c03035522820940b0044000e00b5001c006142045d141640c0300720f0303030342c85209003060640510304118444407441085038042c4c0030051640340c000780d050a4169441e1124410305241109001e000503044680208000542d0405800c4c3c0b410415040d0070b011400304264201c800005c0300d1003000035804084031050307003020390500c24030707031400b00200030001840302d541c01c110742e1b40d450300b0801c1040f61b0301d5040186c0f6009074002600d50b2440009810b680005910218040011004041c0c41c800c2c00c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 215738732 1250 215737482 215737499
    0x11060c0c160308030f0601050c0a02120102070204090c080d081605070c03080a030f05060a08030f220608090114070203030105040e030c07060c0c0602010e060f0a182103061a13 77
    0x109500c1103c80c0c1c0d0001007000000602c9005440e042102413900b180b52030750322040d4554a5100c4c0c42c010b0300c1303000c440c001b801100c8402d504132074800d54081c10034804490f41b030802201c540d03414482d5140500030784800040462040e280c0a10515001104042040200c681190150040b19007191001983c40020000c2644031001e0070030740103a558045485460000680c050712006048240559000c0009001c191004802d44441d1520489002d445e140403001107605410f8150007803a01205000300490312503030268541e8864582c80c4007e00c001e540c820480300049904941d01d0005800a0005109510f4642c2042214180700382c12030b8101407800e44560309008042d4449800700300d08280c0c2400700030780074100200902d105c4c002007051440048031039444600040c4032000e000711000008441500c60b901c0b03100380a20405401641e043e29107410301c5101c0207403106001c0e07440c04c480038100007442030041a00303841c40b1070701c1d048280e070210305180130035000107a600005d0b18500501085901 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 215739982 1250 215738732 215738773
    0xd09030e040906020405040b0a0e010e06061204060501090e0a0f03081f090902011b051b0a030506070f02061f090f2d0c0e0117061203070309030c0611060c0c 69
    0x600560300103a1759443d050801080318550a1a1030056070624030401100022241c3d403411540e0f031010381c034516550340000030227622034110a03e030440780042c103100a02c061584428141c070b0400a0800242807002011070f920315110100030030700303803070300400d1400284191805908400c0c0c0394070084241c4141a1048055986604803810305ca81d00c0481b4029907900107440e000c2c80d88814145820700002c0d40350b454030307003401c1d529940c42c02c885081040402d0716003101c20380003140c0040545125013403550006019108811681d001440f40c24041444003090401d9003c0c01e50b048100080b6035032800b0352000180600c60b0189014541d40c044401c410301080a07171b40c698a001c00c1140c00b8501619100000311030260305044104070112900c6c0c80b40366000a24050003003c805540101e41ea0f54000203052040f09102d1104070307000c085990403c0540050f00300c400c3e603104407030401056441d0402200d2055044003c01c015030b021201041c090120039000341480c2d00c0580944041e100300e00012401038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 215741232 1250 215739982 215740001
    0x20c0106031113020a051b100203280b010f0e06091909050901060e01030212102301080d0c0f1a0130080406030b030c130516020d050d09030e04 63
    0x81000c0c4400c070400e207445040e81e020310683c0c803411030070070380154801040c90117184014203c50018000070781c200903041003d680300001000c020f641da0300d44000c4281f0f5032401d14401c440c2c00d001545030085081102e0203280503440069450000d25810600b04684005180c044990401001c0140303007442c1e140d03848943c1d002001c141203903501a00e040e603150202d6400421405060345071000034850300e101f10442504483d011200031000720383c058015801c2440400d291414149048401c0071210340c80b20a2084002003070000003420f03a41c42d04480d4642907001da41c3c40c00154404508400a20003062038200346005040d00340541c1c80a204480d0341010a0f08404d440c90342c0c000d05000784510610340d95901c502401a100d10903482c0f41d86510640c05680a94014151151005039264030100420050703101c00501e242d040c140300c0362145004240c01c1da0061031060300100e40984c003500000d40c480016009503600c40c90414400c0c807000c0200305100c022400c201c452010386100760b43e02d00660520 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 215742482 1250 215741232 215741243
    0x120c090f090b030d02010603050c060f0d151802040308040605131d10082e0e030304060b010305160507020603070306090c110d020c0303030a0c09050d1b05010e09160201020c010603 79
    0x1442c0000109464004074214001c1168100117041c8006140402d03281e40d0241c05923500c139203d0403490f401c05003601807140320110062030001c000c4108280c13081900c0807070b600d400c1c02d540214081503502c1c0076403090b0301002c0d005420400003045454440d00042800302c0400b002c071602d59456010300410003d24446210761182c0c82400c1c00f8a10b40010403d6008000b40c900801d1034030f40000c0c1c0b1120302903c00c0010b08030740c0d00880002c0c4071094075800150940c00200c083e06c0d9a0300e01482e0510081640a1489000900d4040024545c89501c180380700000a6901c8042c00e0414039420010a940020440c030201921001c0020700c4c103640c0e00524242c0e04484d1940c1c07030704885000000707151000c0c0e40ba0380c00442d808010801c240752404400c40e43c2003806200b000c03e600c202c0c0e050503102c00200c1d42c400d940200002d0040014495007005000c081000007030b031102d01a98410044803040a412200d03a48000340b500400c0e50401e400851202a034814000582010500301c900303800c40b05a94010f0b0364 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 215743732 1250 215742482 215742491
    0x304081501030b01090209010f030509030d09030c0b100807090902031009141506010507020103090501090206070510150b0901110a0204050c0a1202070b0105091308190816120c090f09 80
    0x8224400f0307001e5000d00744a86003103081c58006000209040c04062040b014507980314086101c04030b0a00885540c4089080c1c10701c06190b892400030180b019900341903c1440007000442c0c807042c607804212003220390300f1000303000c550b05102c413030780003480000400c81e030620034400d00007070807692402440d80340c2d80545104c0040c17034402038085081c40003013000c040302d54003458104407440e0707085001e07038203d55028a400982c400b0107281c100d004080c002d00113544408045502d0b410841c001480c03200c00290004c0612100c04143c013541c800610078010503442c5001030103501c4c1254031652500c15099030a9080341d15102c025004181242d10540e45122840d81c0061103c803206d4014050b20641008040210301e00901a110f2050084041c02914400c41e404408501e03036240f0410b030010342640003030b44140c0e14550545803401380a807103150240400e000100207121105000ca80403040a0a912540103800d40320807403c005090580c1ea0f001840500040411010324031720340c00000e007080302c20004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 215744982 1250 215743732 215743739
    0x903050601060819060b0a211b09090501080c0d030e0405070f090b04030209040f080c0d032007120e121902092530060f05010c1a090304081501 63
    0x4800e1051540c8614545c1c01c00b2010003010700d0340002c803000c913612464803810380c151042c000010b08002c024030580450400d49003080b03d03400075861030800321140d281d0400d1340d0f6880c103035001503480c240300e24001c94010030303020180e07803c2c00003504091610a00d444110070510600003011150242c0e5900c002441c000000c40342c50b5040401d84c40600240b5141c14180791a5a001556030b000080c001401c640e0b125003003c00304480034041d1035a0001d00003c4e160390003203024008005081c15140e24a4240f0010345e5511000a40700407907500e42c0c0c00c42400b0000d0407403038000f42c420000245102e40c1160408400d000d1340300044c04080080c0300c842e0815002c000060042000a010290040303514422180f044001c002c81c013001e5128001075030030705010401d500c07118200102650000c03c1d41d8005104203840c0c050f2240d9000c101a50a0080e403203100d1906c40380110395132510450018500d40800c443e4004849042140c01c0d44011940f044070b18090310381c82410300340b03078003065400300280d040740052 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 215746232 1250 215744982 215745001
    0x905010f020f0a560f070f0219140106090203071e0905090c0c0120070308040f0c0806070305070c0c090203060a0512030703110a0c0e0709030506010608 67
    0x4502260041c802400d80c640ea2000241e1500721900005190303002d500d1882800080d89581c504840400e0007044c1c130401501c04281c00c49202d5080c11542c4501c40842c520071154003e01c9032405140c03185002c40d415660001c0c240e07050b08040800c40c0070b51196020318480b41c8200382c1243c164503c50300e0345880168001c1d0155082d00d040d5044040740b076005104218034241d00075038101e145a900d041e8540031441915050310300500c56003103a80c000211100304039014410000030300300900d420000300320310502120881040c420101d040d40d0b014204115910109100b241400e80050180c402901d500a4950740c00c040b81c9151760083c0520382103041003040803234040c0b00e2a503200145080070f2040c40140d94886481c158507011320a030156011011030504e80700c0008540c0174201c0602490418400380075555074030381118a0490019511a2040781d801101142103500240d1001c01115110301b018419509004010710400c02c0104c81c031000004980d0820299000b030800c1e444c1e410a50801c85040c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 215747482 1250 215746232 215746247
    0x7020a0209060f090f07050408122107050d0c05040503030703080103030914010f03021602040c0513050406030209060907021c0e1c03020705040b130e01050604050907180f020403060c090501 83
    0x50910501c140358000c00300381c131440c108590046008900b480c039555844070039566801180c10100305403064812402e510f44c0d0102c014606040100380000c0c09a403510030b240d890401c115070200018030103004a200008903500145402c440c24149140ad003616840800d146030800a01a0001100d2400400a15400090b103001501c041a04005100300d4100081c01901c10000c00760304240e40044c0c4401d0301d48042015094081d0b0041c400c2c0014203a01600800940114401d0b05032036152601c001410718203032081b801101e501416408042d0340314020411040001000e030010340c0100c450601c000c10b5520407031400c1c00c2440c0c441c5810300100c0d00c10701c04901407504500002040c12007008012a4002035404d0861b001158017041c018040d002058020204041d441012030a04540112a1a064100900c100c170140c03410041651032440d03c5a4407040780c0f040035a04038641e80680300042c1c098000201040201c2000b52505d69669034181c102c85010075010002603c10b04c05011315a402440c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 215748732 1250 215747482 215747491
    0x40606080403020606010f0e120601030309050d03021f09020a030804150302180d0305130603050f09011e0c05090907050a030e01020336030301060903050c01090b1b0a05030307020a0209 81
    0x90508041c542540c02960b1240c000c1c0130f09050081c01940720b60b200d4420f90007404211070181c40c04c041038506c4c1840e17654138502030004030b000c1880424007040d5070801c0c01071842d0140d0194001c0000d55812020f04840045d00342c0b10702001c503165080c10b00940c9070b12103901c0041d0300c40c98940750703260721300080400f074021a4401c0c1001c041c010052005802c5d440881100000411544030201d4101751800355014031481800c0c5115210021000903001d40660185106104099803d1070998652941c81e00b03c80b28040740380c205040908400c500078446500c25145011181440b902e0905480005804c06204807210b2002820000f0059502035140c000c505080c48190001e5041d4149100d05141411841009681e00c1c1200c041489182d021700380c00b00882e840c25004c2c2e03692940c44443c02402c0810500050f202482014804901035100780c4c00c2000b00c807500180359003080f00100c60700c040c105001c04041c42d079102d102c0035080454001e0000310b028a4240c0c000744003484562060140c100d90040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 215749982 1250 215748732 215748737
    0x151e0509010b0604050628180b0a0c17070606030b04050d080c0f07060902040e0f160f090504031808011d01050f06060702030a0501060303021e0d0e060d060506031302040606 76
    0x42d41c91041c0e126041980d0035a41d08989a98859200706030301010301150035914107250000d43e0001265070713003014a60341480c101081c0c60403000e8a488090082c4d10807802e080e4009500a4032190200742e41e0b03441c03002ca90b12000300681c5000095200e102c1994010740040d130b05a5050350921003000810001c4400300348070303030822190500c0c001c442601540a102c42d2020240e000095110401c002613004401c250303030041042289001c00c080389a0743d4100501c500000c0c1c8181070f0030200c1104485003074011585000465a205810480d807240034140207801203091110641c50312012400d10f01019002d0810000000359510148802c1030032003505440400e4680d141005202c82403040901ea1944003c0980d40c10750b030b5205a201103442c041c42020060b00719407078140044201980807900710718200c42d0204a0900341089026242c407100d10700c0722400800c081447e000140c0c1014406804003036428900000d100745c0d2200810302c107a10032620741411141c00c000b04011443d041c8540d50180c400340c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 215751232 1250 215749982 215749991
    0x60708090a0b330a090b030106050901090b030f120a1b0209040b0604050106030614060318030403030225210303020c030f131509063e011407050a0c151e050901 70
    0x250301184000c641400f48500750768607081c0c90b814070b1f182508910020310000c0c10041f034940c0c2d288503000c001d200340276100d0302c01e000300c201c04522154001450130422406c807428501d012a03841d0152a200d844207912210100068481409a0b486420803842180078254003031013480c00c0006c00086603c16001442414a0a10140481111100c1e00491000c060f03401035940d4440c0c0015403502d203802c50020000340b100250220405501043c8115441070302041c240100500f0f040c40c011419480c09004c1002c49508032261045001c0301c0c800d01c00341e009040c0180b070208a0b80420341181d002410207020118005420b03601400602881401040d0404031500707440003c00004114001601c900010096864801178441120b0017002d0800e40000c1803500f402121444a44042c5a92408100132946000c20910720310a5006c501841010741e0764071103140014181040d18000c0a81e00142da00b50810445480014039600c244a40205080da45c456004d2440400d0400d4a0008000f0710007641403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 215752482 1250 215751232 215751331
    0x1020909060909071e050a0602100b04060312120e0303150306060d03050306010f02010209370311012006010b0309100b03030a11011404060e1e060708090a0b 69
    0x4144c00083d140c1c0300400280ca441114103103802030000f038021036404001c4000c00541c0d01d4000030408440340c401c01091000b400410100710440745039220141c81c001512039001a0584140da0020366000700b43e0b80020004056450149941c10031160300c80c0030040105008004e140c20020305a000340121200c21040501740e400420500018040f5818483c0c0e60000c1c80300c039070003034041c0d80038160f024190580c481e100b00070f000450000d24010182c9a4003155035490404440044202525000024200b1030b1600400464409103800c0d420207410200c0100340d40340082c2070201500038130b0b0b62142b05480c1d0a10503d0113003040c003211201070001d40780480007202500d010041e00c8003200f160510320703035085941c0d01070f074050414142c50303c0c0c100c017420303040004000f1254400c01300d0603581800c4948441103e810480450840c004070122580804006403103584100d0129500c0003104050700c4841c0e5041e030741c5024080c001da41404184003450f800301c038030709a0405086102d2041c0b5940c00154400c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 215753732 1250 215752482 215752501
    0x12141e04050a0222090309050907050a141c060f05010809070e0708060a080d020618010b0108041506080304240e091305010e070f051507020a17120705010209090609 72
    0x94a48000b07001c0c0613042c2030138030401c0300420100d003400a100014440c000a61400800070300c0c183c0030301c61180101c000480d04407446082130311b5080c0f400b511103403051040d000c103907256034115894441c48041c451952124110480c0102c0d80104013501d0102000c90a000001d401c00000030300c44107095006c04000c101d444101100581c0000341400c0122003516903102140324510301c1d8001418030310900c140e20120540c00200513114018154400e00b00200f001c400a00340c445995030f15000980500204006c55044809545050b2038034400241844e81e8500c05400c42e00305500c4800d80e56a512014001c10035220500030f222021442c10b6200c5000940019040310005400c2c004104203400098080000952000c0005108042111041951200c010107030520700c0c019036028407642c0c007070703c103d0303e505505641081d68010301d810589800c110118038940d106120341602c61107016442c07080180054020300e10503003d5800941d40d440c21380244007a852000d40341600030001c0300204504400b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 215754982 1250 215753732 215753743
    0xd020d0f051e0613051501020c061e1308060403080a05091f02030921040906090b03120a180f15080601021c0c0c06050301030b0108070614070312141e0405 68
    0x4070701440d07101050300d584002c50386004d04c0a001c01c1ca0f562504084c420003444d00344001d0340b0000268200c4040c07003c25402d1040c076020b000006411215806654034180c101800030b081c3c001c03589011060500d03034981119207850350555003a030100e010401800310500043c0101540308030071700018214010007401301d03c19213030703121320081d507080e40480401d0000d1b00900841c4001c42e80c80070b40c18580d44030440705150320f91161042c43c100314502400050840c8042c001c1e1000608010003030007061443c100010b240340c1c09000f091040102c0c1029a011605421b02040c01812400203100d4440d818102c80703903400c0300454041340901c41d280f01045040e0381c1c0000c1c41c8810f035030b1021004001143c910400d98000400c140c00400d0442000d20124840c0e0740f0201441c100d80c0994a452102d9036180b00b46502cde416240155000182404070542218510b0300c02880801c0c0b20b4a401d20441e40640303200f20444144000118403510b44000f030210600000300b200c0304184200d042d400131418207070784159442c0d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 215756232 1250 215754982 215755021
    0x110f070b03070e0d06050a0209041a030c0904080d060801050a0f021318020f03040819080408070b18030c0106060f1b061109090a0c09140102030a03050c0f0d020d0f05 73
    0x40540d210540303600c0704c2d54000c141300d41c04613043c40b4500b01242c01801a411550107140103500c3c165441d10100c11303c400c1c540c440c85014000c0c0c205075030950b0610010502c010020390300130404211550500c900d600c259001800c075840005900c1c01d14401c0441a01d09c42150070f516140184100ac00808000841504440f110807582d101610f42e42404406805644d42c1d21500754008410401405680c000420121040b001002c00c40d001c880400e03101c100d01520042e016001c14085140019213024a680d00705c05407528811822400c04c8134a465a0301061080c2001d94403071000b0410f550704044091f41407400ca05050600c649130200442007002618009441a600c030ba100c24442921401258030602c000381c46043c02d843c0116100307000c1c0542d04194400290490b0001070403900040912040c144168043c1d0b00d02110f42c0c40440c0a060080d240c040761003002c0060a009910440003088071640c0e00b2400350315407004415100844103081000c51409041c1001c1207050a02541404043c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 215757482 1250 215756232 215756237
    0x616051207030b032a030d090909050a0f110103110f0906090d0c0b03041e020d03121401120c090b0604050904030e09010b0304060c0e01051e0910110f070b0307 70
    0x441d03440c2002207018010034107249030540510f440401c1c000940303030fa2a81d03c440708160f40d841c02c0101c403810300d030740c40035090305000001d05030f40001e000b0b180c400d0304224034803070050044035280c1c18103403100201d194480e0411215508542010145560035024801c010308082d0304240c181711894101c0030482c815a5002446203200040d034032020b070b50742d04d0880c0601c0d8124903542daa08d51502c0021040d5071050354141d414424801a52a85040131060040280d501800c10781100c00300c0d0380c040e03d280302050030140750140c407003c0705114545041c403480e008241751002c1405040c01400d15031600e0070103402454030142030803683c08898881c40120ba00b291403d8035a0030320340c1c2e16418212004140f04101550020240000241c00d50900c0041d501840c09030004124031202c88c0d0044c1c440500d03411103036012a41c1030001070a16100080f590001c8650343c1d044a141c06101d00008031a00030400c000000324240744030600c0c407484108a41d80c0741c100300f0030041403014180411141c02c0d00000b000c0208 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 215758732 1250 215757482 215757517
    0x90103020108181018020a0e0c090f210c0a060206060d03050c030f19080901150e090307021c06180503040b2a07091a1e0d050a0c08061605 61
    0xb14910402c001d880041c03050750100459045c00080410042d910329007070348100116a4081f46443d55004041d002c0c07000c844400345010246c006201c20780300112401da07400012034080302c0040d1013a207410402d51980001030114110798030200103030800f50b600240110740c48030040182a4035103124a8a02641604026449003450200340340b070741c81014404692054081b850010018079402c494802c0c155176100c450b003030343e510f00d81d0030300701c801604000f000b2041d03019042003d8680311081c0c64110a5000680f0b103480d0040d0045110b0061001c4020103a07403540440100b88045846008210400c41100306012602500c41030b689000d02c0c01204014400028042800ba001489503182e480d1307210f400c0c02d1220580340340e01b501c0300d400e40710f0a04194180f2554401140c280c002028035980020316440920200803060369062034414122500f0200c49a416404508100070040316580702d035400c04010390a0850759414242d01500881900c080c0e400210b01d4035030400c0c21342d1005114217a000b103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 215759982 1250 215758732 215758771
    0x1205220602032502071a0a02060402010f030608150405101e020a0306050d05100e0304050109090213050a030c0602070e040201050d0504050a02060c1e070f05101412090c090103020108 80
    0x2075840314074000800c91040c15020070f140300c0c2d07004181d0504641550345001508001000d20a000e8825403030400e005070002300000e4010340c09401388140084040c50009409525081401c0c07405e4134030840c81c00c00e489190204801c022041000c2000d07070300c054800344100b01042281502c2506900b20103a403031900030507184101d5201c0c2d80410010040101030340c8100c6c0c1d160030240d0700c4600252000c1049801c1c02980c82c2c902c0c000008a0f801c48078180d40d403e21243c60105090002d42220f560303260741e6121130100213255900c5148041c0554024005242803514110010385801c1040d8055014421401c04201c00360380c110f070554451a8110310085080d0b6614601700b4189608075000952182300490f501ca221000044c01c140880c4a09206404100031002c1440c3e9418140c0305140500000c1c450034001803c0503001c094641c016030500310b0400f8005103038004213400c00b040074281d03013045004204070032a041140f54842c5800781c540302c1141d41103400080c00884028200780001e07034410b10b4103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 215761232 1250 215759982 215760001
    0xf030c0105071505010308090405090606091b040f0f0e1b030606071a04030302090312090307060e06270f0607020a05090c0f03011203020c0108010b04051e0907120522060203 76
    0x35104684003d0304014075030b124509007040d03400644201c1d002d645040c00268081e0741c0054481d020303c0005007841c00341d03654800400c038940240704048189003001e00c0b00161160340365039400d01420300414142d00c01410301c0c5040700b034020f00414494500c07401b0f0708100c00540d881c000b1240c10190690750541d41c1c03c020f0420403000f46140c00c1d020007142c00c41c0f04010605506034082c101c004412020303650440341900065089002c5c0d600c6031030b030507000100200259402000f820001c010080e00c007500b40210340350b2030325404001072249840410611155919460080c80d840d282800c22102c0c14245030080c0c000c102c6104c400c2c000c0c0c5010b4948003022030160515641074aa8020540c07524503a20340e10785418030f810136a031040440c054442c03040e45000702c0d805401c0d1a0f06940d615540e550800b0314103010040130100440c02311201015070604005962100c001440c89521a43c99149009501d20580c50032108000d0102c1101c014130041e11260000f2078820030310b4142c0104005d42c807a1680b5409 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 215762482 1250 215761232 215761253
    0x8070606081e100c0e04090302070308070c0806180a0f15090501060f081c0c21080601020f010b0303071104110703080103030f0906170a0608030310140f030c010507 72
    0x2001e44075160400e00400c40003403401d41101030b9481690030003100c000c00841035903400420240440da44500d070700c1190070154069100140248100c0d070086650f0b890b291501c4c5d100c44815251081d40c65030034072140d24100a2903400c104818032041e0410400741c1c025883d241d4200c0014940c900c0000e241c024080d40703032186110340400d10000c0254024916240e0b00078149031103880c29402d500c100c00110118081102801c500c2c03581c204440010709240d048441e03c0d5451011a011007a00c411208004201040046500303203a4480c00080d0616400180c075140d6540d54000c41603040c10240c035010b0b100402690507450b07101c21400401c0c0007070800a00035080c3c0c400880e40c1a94049059400d041c5d02130b8404d4101ca0207515814944210100100e070442001d000304e0021030340102031070706188844004a41c7c4071400601c001a06900c9441b0030f800c55000f0b4424400b02d5400380800d10003003219102c03101024604490100480caa5040070903224015801294103020020803400144500e8000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 215763732 1250 215762482 215762489
    0x1805090f0c03190501171009170f0d150914061509010905060a0f081b03130201120504050d090503011b111002030c0301060e0904050a02060307091205030a030c02160308070606 77
    0x3801d00c00380d03840702103491046e01400c1c4040f080707100350007842c00c500450380f040d00656900300c900d60942c155880603014555000300d40c07000b64411b040100294034455849606168103010072000f103400e15229160007691110b15804030f07502c0c14001441055070340c1142c04040c1294200181d901c0301c521100503075076500142e0182d80c1003030001551400c100d40c030002c80c131441c5200d80ca070130600ea214661144a0003540c40d02034540d02c101040070804d40025070380130368402841450f0104400000b906105d00f6580705580849181c1d0009654150043e000b03203281c13014020981c001c100740614041481c20301c1b21460080d205110140c04902884901880207642072071051005540c0d9040450355080c01e41d20912416001525060340c08030103141c0704400340e018640003001072617894400c4e0208a0541c1c8040e014034180b1103c180000748a44104069019050040000c4c607215000c0c074102a013a18084042c00d0110f4001c203001e82200102040088252a0000100303500c540c060720b404e500803c201d40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 215764982 1250 215763732 215763781
    0x16020907020114010e1b0a0e010804080702060c1b06120f04050309180a1803020c150c0a03030207050d0810030809030a06060e0421020309060904090609031805090f0c03 74
    0x3c00442c140d28803140302e07801083d4040395050090f146001e441083e00030407030b003440020840b4006001540c40f170340307403540c006000d02101441c092861340000c0c9039a2160103d400310f9041032604d4540380c03580c136103803400d503910544105140c6600038101e54183c4000900158044c0503d90110742804000c0003594035150010300603608125509841444101e0100c80c0e0110483c05c1800c608041d1a101c2d07540c0e0b492961540060849280000c2008401c244100741170907a00c1d0140159451000104003c2200c14029140103030f0b82d031700a0928500340250094030800344201da205114507030070310184071002c894100305929282c0d000000000d061404105018120f6810502c002c118400c10300ea190780114859002448407465446050b161525020380c03c10240c0c0051007154a01e00b030101c000c0a9513a07009000140f643e165584000448400060550000e00c104d0000e18901c9035a500b417001425044802c071000b440c22555402d081800244440c0d50000044007056440504400c240c14211800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 215766232 1250 215764982 215765021
    0x1206020c0f03130905071b080a020f030f12010e0c04060f0e040903091815060509040e01020f07031d0a09020f0c070816090209100c05030d140604060506160209070201 73
    0x28440882c00c8400fa001d1181c0207840d007800300b8105801401e8a00c004120001100030612041c0c80e043e52507008411000c045d40501c0260440c1500203000a10300c0f0045a107075143c588a1420001c9641007050308500901d4002d0401e211010700e1800070b480c01c5031064a002d020316850840b00300c800c03074031280c00c3c0b54100303050009900c10140c1142c880c1c02030b511011030710610214100382d0031041c0e038002169844132054580c000c1c02803510500040001c120058004223450b040b52400f1802caa1004007000304004000c10002e0405501000c02964000c0c007403e610008603000d000580c140c0110311600d2980c503400107080e842414100e0607260307460320002c284d07900c1c143e60b62503c41d29022001c0c071a449580c031210005c6680b1405100340d42070540058a001c642c7c540c0b07800300303460180528500b9100313840b043c40720110718030300c1d40a100e42d0204c50f42d00907400c1303050403000d010039204580c00851203050103118400384030707a001c08180c1609404a0340c8a44540b6405000d030b0041c140074211000b540f0b0172 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 215767482 1250 215766232 215766247
    0xa0f030606150f0e09090f120c010c0c0b01090b040603050d0e030f030a020601050f040615020313090207030c02040902060c0102040b030402130c02031c02130303020d0e09011206020c0f03 82
    0x1258012000c4031821818200d034108035600c03c984000c8a10201c902107080a008004903003051050550302940b44070450f84401d05880c10741c0d00d000002c034007480003080c00142c4105803620a0168201c2e8081c242084948501c02e1764990f007231800c05000d03140d0034640e1f80080502650301d41d0040d40c000d40c0c02c8410340307440040c0b11030028440c500e05040300e4023a1060420f50203a0103400000c880c5031000d550b01a250350b90900b0100a0212481d40301283d00a407a5400410350010041580f90003018a400644d912543c3e202c115615805c030b5406281d070b82e8414010140800c1d00000610441c40c4d04980c002a000d08500c0050124004c50540502940c401f02740803401c0b0b4040401180520b00850301d00c840000d4a544081c1036940c84002900181c0007404003801e07141c411001d400c10307144505405410700e8805861000c18108542c0103500580c488422850b8958120782e5001d207400e005d80d60150300d0343c100720b0780e01c1c0283d004400c000d1103142e000841e0b08428000344218580c0d5032045c0c06403981c030b041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 215768732 1250 215767482 215767493
    0xf18123009070b1e0a0513061b0201030b1206010807060908060708060409170d0209040f06050d0f0521030601030f0c0e010e0a0e0403080f1015110a02090c03090c01090f03020f0a0f03 80
    0x7c110140c0341c003c0b0000c0c021807202c0c060350822040340082c039001003040d00241d00440140242c15140c1c0e800041c1101c1d1803103038078014000346002c1d02d5600014540c40c2d1230114010042c05043e0702100d210f800850510100c1382c1c0c040c00c074541c00f035000d5901145540540c42c0c026142c8408c003080503503100c40881c00c10124051a0003c0610314800c80d81484000f6040d055902140d81038420958008001c860841c0012000c0f40329454003070059054468015080c5828040d01000b00392901c241100082048421343e00340c410411f00d1400d4280c10000900c3c1184068042d80444081e03505010120030000001d50300c0d40c096001500380000031200b10b040625001d402c1c004281c8041004950354070004010745034402c4a041191380d90001118610101c1b1002d481c5400d00c89841ca0890050010f09000750302c65010f81802a10708421f03550b0349107002000c0500701101c08540350704110688401b0403070001c90304070700800c1d03a40490342d090745070074400002150800b050f8801c131200d40036840000300340321 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 215769982 1250 215768732 215768737
    0x4030c020a0e09070b0f03040f080d050901020d0c0806091521100e0f060708041104050f0907120803061201140103030507030f080f18123009070b1e0a05 67
    0x40040c00310f42100751181714101840c0030f00c294801c0b50744024000280414100990b4000c0140601181e030300c0d01008001d0102580d004582e92045a0f400083c804142d52580c481c80d000f082480c541a500c80c18000c0010304013a0004d810000e121410307440303210450756607030a90f01c0303a01045484914111070b0780d00c0058031000c513001155240b03072601c0c543d48295103002c66607401c041039402c05482e080d40c0c1e40c20195050034000e0010786400351484500e00d00c03900c95102d03503030049200010070840b5203041036501d860021580c11103103820306d500e0700480025040d48241c0303803c14401c0303034298010300070740010071b00404800e68405c095010241c000014103800030000e2043c0c40c021364500444409001d8203503a20081a98211031031000700f000030320a940082c0d650703008410758501b0b4499060948206003a103402010050010590700e2840f48090f490450f02c1000b81300b00700300c03c0d4440303103419022140c07a204148101d03001d00c240059200140140c40941e09031480d10303080b031141c4403610150000c0003034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 215771232 1250 215769982 215769991
    0x242104110d080d050a110304060b190612021804090b010e071404060c03110303070e041506020c060a0c170a030509010b0a05150d0f0516030203040308070804030c020a0e 74
    0xc8404661a20080c2801850701035841c0d0403403201482c000c0c6941090004010003440c0c81c1e105c0760380c2d08900310f4984500009600450044c040494029030300000c00c110300c0d068000542e001000c00d0010000c594018007041814042080010b03258080d450303101c043c581212040562086c980395100c41008050312455060741d80c0141400026079404d0010754603a0303030403130b1403414515013170100b0082c840c815100304282c50b110380303030014280b120540414070319002522500c0100f510514001c101c0d05142c0f047d24071803441c4080490401d498804041d407541080303100107000c1c610028850b60700e82e020b01d000010706540f126206403e1440041800c20a401c2090947d00180c00c201c007054072101d050141000070311004109081241c5000104078400c12021100e4543c1c18003401295500e2400f449180400d802e41c402c04203ca14062203030031171010b10144004140352040c0203010200380d201440702d51000f000d04284200e80c90300d050941d4800300780b560080d401080180046448071032060b006004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 215772482 1250 215771232 215771243
    0xc1e062a0403060504120507020108182b181202040504081c0c030507020c010f12110d0b0f09010b040506030a1113030204050c0c03122203030501030b07080105242104 73
    0x40b0b6842c146c0c115164413410801a00285c85540443c945c4402c0d4074100085400c850100c4159020701a8901850081c42d8018401081c40364400c20f11250010031107009000404e140200f01810a680140c1000701e40344040d02850355040060200981401200c91913002c404001184844005840c809081e842c00d2920009040c82c01090b4803500000314104031080503101c25955403244003003142e00000c26018910520303203a0300e00e8403482043c40000e0081c440b04900100d00a14414180000d00704401c150074083e10141c0700403c2660b00072804d50b010b880e000ca440340d541e44c507401c5107840540303007501c1e15803080000050303c414180fa00e018514203c0e40300380d07030030320841d510b0b1100b00c0b84078051800d05864640042001c5552117044c0c060081e40103008c0c1c03010003d914a050000c0e20b2141001ca0103c3c0402d50711030040c402d1100c03c0880c15030050316460030a80c20b42c18000894207001c1c1414446003410580c902c4031140d03200400960b003034140c0c041c2005010101107003030a076280c1c405480a540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 215773732 1250 215772482 215772503
    0x6010305060114090412030504060213030c0302040e0304050102100b191d0105030d0e011214010608040606080102030c0421020603130201090905151c02150c1e062a0403060504 77
    0xf1800e140320840c0c41141c0203225904002d5609000b5009402c0082c0b0480d5a60340c00c2015a280100d0110121301031406160b40c4030181c0d01b5803040c0b2003150340306044002c40740d0003440700304181e0781c0c0080d5006100003014008261500d400002c03426803543c65a2661907444191800310f031030b413084699401a00c039814444000759a807007090640720516003840038000749440313804200c154012907480c10210701c1a0000101c10f000f450030669107460a03006000041da41c103051009004041c01140302500c42c1e80002c526500b040c02203425984a14801c40300e01411070358100e03a80201344c00d001d2707180d55005001d5070b80c2d902d0040fa4513019640640317002c9010900c0000b02041903c410701c142c134415200c180f0000c1c0f01e00e0400081020601c0e0201c00400c020000d010311400607181e40654261454488a80340e8075511075801c03103808d0200d06120b22034280f44031402c2d4121f0190014841e600061750206007080c14820750004030000700d0035134403003003090000207002040144550082d407195006030714010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 215774982 1250 215773732 215773769
    0x1270506030601090228081006140403060c110d1e080c0f160611031e0906041704080a080306010201110c060103290702010c020f012a090503060103050601 68
    0x10845a094610580582c00440140880c00e85513000340340050600c51701c000241e07010b40c40c8040821050030300000080107042880605800011420054509810806c0c040d10443c44102c00740e01491201a00103500d491420801c18042d1098070303507084104040d01c1d00700c0403161340030f0145400c0301401444e403001001503d207401d20980700743d40500d1210002e54500400d901030542e885d0480070b84811031000c2c0d005948000750f11845040f0704501d0038003e2b0354a928120001c00c003003201c800e081d05105004042000314110010600983c401d501130918207180030700e40c0001e0254020713504064040d120f88507100c1e0070300444801443c8508800d0f4000d100461102d14201001e0098204032020f90340810014000200c1c250b149443c40c541c01522170168885e00c07045c0740004c000c00c0d01c2080c0585d64524070041078540c1840200762a03284d000003840700150706070303803000b00d0414604002e01ca481640c04484080740706a1f82107005080c000c0403520196100c2c00c00b00d80328502031080c1c2c004142545140d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 215776232 1250 215774982 215775059
    0x30c0801060f090b1503010e060307090c02192a1505190815040911031209010e010806120a03200a03050a05070c09021b060c07050606060a1701 63
    0x60303410301c0c44101e580300d02c0d00c0c15241c00390861302841980103202209000c90605118003450080507004681c5450742825000d044c1013051035017190540d10300745020442e0ba00d4000600100109240703010f51710114040c10310840d85401c1e26600250510b910a8440d017800000d900c103400e03030300c0058855007084000601035400f849524540c00001c4054a4580407440c01620300c1da03030040c00201407806140076074001808580c01c280044501701250302c604601e5040412800d28000034025030f070382c0f0781b058000018200380000170f400e03410080c2a2000a445844400d000c0d0481080b0f0ce04940d030000c2180340140498207940b4208200008418148640303090020b603040d145501919000e1401000120446461f0f000c0c3d40d040d581040c08100014243d0858401042d0b4401d01d411070088070100351030164107050f00500801a41e240034801400410390108500350003600841303009a0340e44c50003070144c0e12004030400a1000341045400000d42c0072100441100301a103042c400e8003407080c0d40001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 215777482 1250 215776232 215776241
    0x14060117011b02060115210903030f06031104020d0e0a14150402010c1101030b031209131e090f14011401170706030e0f010516080c0c060c0703050919030c0801 70
    0x4100040e4080c4004006041000c00944c0031b403d451301d003024008075000449401030400e00030b5031210a584180e00001d044d4144221443e20b5084070b8140720603440c1d034541d1808008513200240c0710701d031300190105001d2400e50140b808400c1003001c6d2034a419141c145010010007516000d151070040e039010911180000414a11455050f101c001c24004a91100c5100c7c607402c5410a040c155100c801284981d810820040000b044694003591810003c06020755a404024942002404d02d4400035145240060b03151100c0315116001485030a0741c10302c44c2135040795490144c525034484443c48140701043d0403c941c0103950004964403a40d0324000e900c0c2d2000c0724885508140c110680c28051588240c00030590600207100700d5800a002d500e100d42101ca0588410202c0b1020b4600e01ca442c5802c0200c4075404044e6180460401290102258a4000003030407900750b600002203241c01c141c001c40c1a84d01d40c03000a0400c81074200b02c840c00180011140c081a00d1000080328001030b5114140503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 215778732 1250 215777482 215777531
    0xe030f1b04050105010908060708040201111c0e010207060914150c010209010813050a26040b090f01090302010c0b0601090308030a0902090a0b010c0212010e060903040f0617010506071406011701 85
    0x705040e55600349c04650070040500220304110610061a046100802000000e1181c2074400480103c064038094284007020407120f06540010008018842e049404034044480151400d03a035041c1007000905000145c030740d030b07501c11031011414103034508056002c0c06c49050280c8a5403030944450400704100317104c445000b05644e10180401001130f900b400014403440e501c400b003000c00b12403002003501c180c0241e009000419030100e980c4442c1d207481280d5810010088c240031000d40d00f590002405000610005058806c1031808224542d02c220301d110025a0000780c0103480742080c14118000c4c00901d50103038071400d206408910b44803800e10414130746400c161102200c070480c541c00e109a5600c000d214dd405956683c0e0b81d40402c1030b091010310f114509200203190707258208070389034100030340701d8003c001000000445502043d01104087e03064600c1100e215407140e00601d00380104203421030340000e49018031000028500d001e040c02c0032060a001c0005d110480e5191501d0220300755101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 215779982 1250 215778732 215778749
    0xc031c050c07020d020109032004060f0b0a0807021212010509061e1c0b16020609010606020c01050f13030c1703090904121106010305030a1d100e030f1b040501050109 73
    0x40c94010f01d46800c1c0d0304e02d80ca1060411540d220703641d449100d0068144000410740086002c007142d01c41c5460300c03507440589142c0b8281083da60904c0c0055419001e20040740052180010118610600070420840c0b140c2e0090049986c136110004034851081c800c0c42054002c140c03600110381c441c508110482800c51041c11900e0003221110100554400c0c0411140f40902d040b582490104000402003403241c00b03500400704a130790303076400000d183c170500402d401250307407500b8011b00a4543c0460040343d22502442e00b5512002d1400d0f03058000d00c51500c0502030030b400100000200071210a54004813080180802d404460780300c4000c0d1a4400e1000c2c1e0340e480f4a52400040018542c2c07001500d4600704c524080384a200300705007079450203100b038100760b92541c004281c030700400d0703401010103078040c18200680341000400c0000c588c0e60f040010f03400c030500030015000100340d2130411001e07100000760f07400c0b1030f074010700300b4840c0c9500000403100038004c90801001240c6035000f02c10302811a010034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 215781232 1250 215779982 215779987
    0x10c0b10150c0210270305010b031903080a11040b0703030c1803020f060313020d0f02030d050c06060f011404090605130902031f090b070215010e060d02010c06110c031c050c 76
    0x41c84c00c0b101500114040d90010000307100d40401d44200c000d160700514410b90001a41c01403c0081600d041d1898072854103107540c07400314400007a40140429003000c1c2001001c0345444c040c12506850780960b8102c0d18a100c00403c400041c10760540000c00c0040b0030b5140c42255002c07040f0ba6600321400c0f03001c06900098000c0c11210700e81401001542d000309208440040d081d21540010f5064503102c106942c0100c50003055000e6180a10401030f0303000181c18640d240100740d00d002503c40300010041403144640b1000c44c6c50701c2e409550105003660341e500016646070349420340c4c0d800400030ba00507140600c1c900c03840c040b4105c00a1080e40ca1560b002001085540e1030082483c1a03107441c8025172041e80e440d04003150005d85126505400342c4465005012542103040122141080580c0910b14162810781445903d80741d5a0003828001d1702842c0c0b030018445181421400790400d2a03461815150015001c2d50b080d90210142c00c0c0350000c01698951080183c0030001924403d40d607185000408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 215782482 1250 215781232 215781259
    0x1807021e120711030f120c0111040e280f1a060a1709070b0304030503150411090f270702100b092206140621060c09010c0b10150c02 58
    0xd614480720f040c00000c0c03c40e0604030f00c1c3d165140c245a45441031407100c2401088000d0a60310a00500044c1c1c6507407600c041c14180340c400702e10403814002d0002c10205110b99142130440c14041030702145000c55900034001011008180c00007000584160300c01030201002c080c2e11807a026040b20400102c559480d404198008140c001126001e8550321503889990070010b503004510028510442c002e40f5000c0e143d14020620704048035502804610952803e190105103002480c244c5500e0002580e25050b01d10251010940442d11810b1301c2120102400606a9a400c6041410710529065003522050004004100c0c02c0d0b4070300900c420790001d201c000080e030b4648161450b03404600c0e6080c501c0c103942555140d1032f00710b070000d1488020940115081250718101142c5250b503020700085102e014480000c0da56442d007001520641002c00009481410340c2e201d000610500d0303070055500c0509040141c1d00100c07560307251003130111120740c0d03580034288640039245220100d60050074139110304a4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 215783732 1250 215782482 215782493
    0x602060c04060f02070e040804090612020a0603020306010306120c0323190c171006120305030c07020f0a09090c0f121407180e0c220b1807021e1207 65
    0x140280350f003184111203000802075a0308602602441c05903000642e5079041c102e118095031941c3d0001000781c070001da10100142c480012043c00c42d0203500c1e0060712502d4030001240a0200b075400800010301c107449460500050070701e241c00310b0344240e03d4440541e101c460800903900d01d041203041d168001001d1016142007881c0c2c0301140c00e101e00e1507020019290868100c1e044ea2580d0f8881203a4018961a50788611a01c00c0d000641062600d201840d1141c7d5001041440020300f05043d01001107044021034480e90302c038150701d07180204960300140d12908254010712621900351074080740c08100007225005080c07a5402c2c3c40003c80441c203421080d890b080b1441c110404004e48034842c0e44000140c00c800c1c8180c0e0740c1500329407603003c110300d04c440020b80d2504810180170791041c80000301642c5042c2510300200b4030100c1182c00401c04400b004001a042d0f1b2007401d016a104000c01d0400000c030b540454403111003141400000200039a5000e441e40d81c1401c45c802e040502c43c100306400101e10b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 215784982 1250 215783732 215783747
    0xd081b100c1e180b1c091b0e10120c050405040818150304110d02030706020c120102190f0302070f1a07030e030a0318020a260604030509150702041b090602060c0406 72
    0x817142c4c01c0d030141e140c0303c04800001c0310f00b01c941c00d0703900c060013081d16603214200f20705800092000545046c4542000c250074110b040d428441c400d18110030800c2c0008000e0a003400d80300400e0001d004104030700c3c10303040111041d4490701a104a115010518589910f4003440700c5c26020059105a0705560704c1d82d59150b403000c0304041d120b61103000da074903000042c6d508200c01406080f6941c060900040144103002d081140c0c0c0020498070b9005000d00260b01c0210750111802030401e280c45100907058800c107500034414000054080e841d40a0814140701110141c81110203a2001942d200d0750382c3d0742d08508950115900c5449500208071f0a61824401e401208000a00d182c01c19001103180d4001200818a5441041c041c20380c0106011035000c0d48502c840c0d202c0d8004040c00d040e14060390700a00724814015074a1062a0468420086040c0b543c15034024a501034002c11601131000410780e40707040f00ca0001e07000108511008102644007081d010301075a0b039445003900303107800c1c00d02c01e980c1c03c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 215786232 1250 215784982 215784997
    0x50c07031203020c01050c09040b0a030218041704060c0c08010e071e0e01030b0f090a0809190504151a0405011d010c0506040b070206060d081b100c1e180b 68
    0x10380134486a500700000b803141c140254200b4128030750300e900c0841880300350b07112680024400c9a20b00010030140e1100d101c041c101c0108401d0440d800c1c2d80c1c5142900c5ca1090b43d0150410b4200b000c04c0c007048080e08030300964038503400784411604041e50b546015007610500d910300140ca401400c1e08001d030702440b40180f4100d04180d2249501e403615041d1102c0c1c01c1009034403d45004032800244184403186946180e0001c150300e019100c100e070a07032101440e51050305150390040422680100200710131762340c2c84000c0d00c0000c000b0b0080500100003a040094a80107081c0d10000c110640d82c8001c02800454085a0044e1901c020940c50010b4007020001000603d5040c0100210701400081d001e00c2028841e621078405d0101c14104044020700d45400141214000d1182c110301c80302040200c001e5500300309581110801c002c800840050802940c400c0c00320f80e045c104520718036503039000340210181401c0f0140f00764401a6699040740d0ba2586005641d42c1c120070070343c06000c5000c1e07040080501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 215787482 1250 215786232 215786237
    0x4060e010e0301110a030f15050918010906090b160e030703030e06121305011b12020705010b100306140409020d080705070308030c03040203061f141c0503040510050c070312 76
    0x3501082c80010005900c0170402c8000a980c800000d40c04521781d200b543e244104034001c03508003d04180c08030b0300f07522014010780e05032880740c0302820185109401988403640c1c00131041c0890040c903c4c00f614607542c260703403440703035003070f19071740728000b65115032401d03049044010001d12505103141c90694501d050440000e4006a003005041d040c008a14100783c0291007102e802c81c1140002e060150071214841091198030b01000b41602081d580107000041244103260010303174440384c0c0e250290041c131389142e00e5908448a00300c40c44003d43c040d44418100c40c0800c1501c203101c4610400c020840d106190001c0d071040e2018501c0d0081110080a0406c091003401110040e40e140c2d1554a101e4100b01c03010413100100004000031410b051280a0f085280000c61003204002c441d81662903031154064076055003d5120720000c00c0e5607800c4001e80e001d04004d07080301050041c5c108161a948580100d40c081c0d800d0121044050348103004490043d04840090514181555600b10702400c200302140c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 215788732 1250 215787482 215787491
    0x200606010e0409050115030c060302040b03011814070206060103060f0807030b280b0a0e060a0e0703061d07030b030a05030d11040b0c0c040609110702101407050106050901090204060e010e0301 84
    0x201e091040c01c40c06c94211036141201451880c0800c99003070981c00103010140140010080d002e00c02040e00d041d141101c000003c0c1090940206000f4030b04551504881400c290904c8051034001c14414050002a0b0b0203001090321051941c4240c900340c8282042980145410030100d03100c810119001580b2070383c0a81ca400210110020304581c0494000c9038950365400450b161a011190900815061b00f400341d083c80c0441c0020450304071413189150700340c150000104510b01c20341c845000760041d04000e00700c00c1c1c2002e40000d1581411104200840c1c41d20003c2c00383d5240009080041c1030f030041c02035140c580c0c4400180c0203007000d610034200020062001080100c02c400242c03000300c003a14000c1500c0c602050030842540d80c03d03131000818900d8202c80400300e00c40c1400303c8050310380580700e42c6076508802e0021070380604220425000e00c000480e4076020843c0c103421220803601d0448a21815036203d00d0340000324400e40c4240c00209030101e200c003129500443e900c1c00c503654020000503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 215789982 1250 215788732 215788751
    0x510080304050607140321010f140306070c080906070f060506042901030605060a08070327030302072307030311030909061e09150301050a1506050f1315200606010e04 73
    0x100007c0d1680c022061400450050107010340001d0200c00800914103c90821220b80c001b0988a810150070001000590800c00c2d091200c035208961a210700030745070315074850403070078890303405142400225415410600812220724090244406c50140040c481c00102034040444000080e40304129050540703c8a00154503a60b000141442400c15180c04540e807800c501c000b402c840d03d080600505800c0060747c2c00c0b5a0841840d000002c603814100180d0310003450a00030300da102801d10058201c88800a4030107101303404602541124465158040d80a1400c900180c0b03034040c6462041c1c00900e0f00c0d0000e8824500390039445100e04035284001c1000102c04041500c0c1c603401c5844411901c107000060646060074030503a5400030000f1b1041010f00c8624444000c0102e8500c03c0070704000001c00c20500e00d2160f80202c030300c120030035502204895525500c0d0130852030030035a21008034420110524405001c131248c02c11820034240503041556850340156014440c031003000760401d44e07400540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 215791232 1250 215789982 215790007
    0xf020f0a050d0915020304140d08072708031903140a09030c05060405060106020c010c0f14160609051005031b0c030c03120f061806091e0a05100803040506071403 71
    0x1c5900c40c03c24001595900d060700b07101c0e00f4041a801180803680c400850300313509e5540034000f10340005052a203c0c401c00d40c14440344004214040e000d40002d650783e0000900c4007000001001c5908031745483c410840d004e01d034190203c9a50400203404002d81000084000005a01811503144241080d121840443d10b030640b420808072806c40e140e510960040c00b071960104800d000501007464030324102c601c4c2d55034000d03108a5850b00200054211903405a0464042c40a9420742030341010390345400759240002004001c1500c02c42e4080c8481103807048109220304112440340c10503454410a416100c03c040845511901001109000038010303080017030400c0c0010000f080d07900d9101051414180f01d0b2007030742074019290a02c211501d0310700f910381c40c008243c0c075584120b007110855003d66504240c1009803107448448140c104100c82001402c5075664003041c0a800f20416840b046911000c000e6528829405003d911100601c5150000340040920f040c0c0600b11b2410f580c2014880c2c403a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 215792482 1250 215791232 215791253
    0xb010c0803041b0503240a0e0a03020703060c0c021e0f1801150c1a04030c0206042304020a02120708040801090308090c0405010f0519030c180f020f0a050d09 69
    0x49490700055201c0d10480101401002c015013030890143c0b40c400039802c80000400344d05180c0b00700c80280000080c03806001039200041d41d0f00c12500b0784500c820701c0e14000f5210b007940e000c119080d40c640f1a5401c0400d104d04440840300da4040c00400c615690135100510b00c6044510541d40600460040d90305911488520045001e0403841122103504010102c0080070701703502d000c000c01c180d01101c00b01182c07454869071701c007804290b400103907500c1342c0c1021141690000006500580005000148401c00c58600c010a82d2088035002d101c60204080006030705c01c0c1613561005a03c44010309c00a4070031070b002805128859151a440d00e60385001803829a202c2c6102900070900003410054a02428414080402d208a50401c03480d81405942c0e840c0c0c003281e014a60051200c1c0425040d00c100c0300000d07401560708018144005a5203012074020040001c0708001d1541c01c02d45030840107609402582e0035640031049490520301a002d0071202d035084070010880040d15211800c0201e0080f016 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 215793732 1250 215792482 215792491
    0x71511040f0602280b07050d020319050708090d050a030b0d0b010503070902040b0a0509031603060b100309080d050601180303050702011403090d030e03070b130309080304080703060b010c0803 84
    0x2620701c541c0d20304074000c2d003010920050003941c0d1085a8561624500c01340751542125404004401c858442c0841280c07a8018220100340e528400010701170520322800144c021f10740008c80a0101c0d07070324800d04031001d0030281c0781083c5035880110988c1661780110040c050110781464001008114100001c000346091042a20045014001400981014010817010744546c92055185c01d1802030840c0b40c07880380d20b0711101044804203507804166404e1082c003801c85034405420700229140c0c20030400a00a50704410700c81d0781301031000e030b42d014044e01418042e1600018100d0a0660250800010306401800541005060506540008c820104c4400a1402a81d50681310003040c070001d4810018001c100d980c500b002e0041103880b0707000140d191508849031401040651800f003255103180998080101740c100c1040c01c00080c40301c04070610140c0741c041d03919010100d40c3d44003090b07228420303800307112000e800851080c00410304c00d0700b2038060362206140c20a0111010b1300c42c0d0641c1d400542c0e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 215794982 1250 215793732 215793749
    0xa0e03040b07030201060e090c01050a0c0204020d0c0e040b010903023313050d1e08041502011a0a050a0b07020a0b04060302180103020418050907030515072307151104 73
    0xb45141030560910440313010b00950825201541802017a055440c000840c0b002e0410400140601015100701c1c0c844140d06d03400741065450748080c203d4038015202004410740041d030300c01c00311900b030b10785402180c0308084180c548189450450702071048000604402020f0302c40327101c8100318040340c134802c41d40712800d0903030b081d03910b40100042c000d5403d641a4001480740511602141c0891150488194502d46051900b2690481441c04082d94060743d40584c5625142c02c1c008803c640e019002215982c00b114080f0b100d00c0640c604100e0811980d0180c1034010303054100034024004100c004000c054002001c040c1c03100d58900c6a0b40c004c0d071054010300000390300411400078444111450442610007403c06606041c101a0f4540c1070355485169400a240c4074004200d60700014058000030315000f100340c2d84049008000801011000d480000000700181414101c40f004038107070307031020b020381112540b504070581c440c20805a00b50071094220390317484200c500c24001c010014001420841d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 215796232 1250 215794982 215794987
    0x4030206070f11180a02030712020d090302061008030a0c1506091e110a1b0501060b090a090624020c03010c0e0411040e0a0c0908010603031806020d0e06030a0e03040b 73
    0x51904400350074180303500f18040e5071104080c004404048410039440b038051280161a40d4544500315000c2100c1210344801a01c0011441d00a00711500004103040c0207408580c020f4a80c00b8a00c1080030940c4148502074006119904800b40700e00c04201c0030074020000d014008020740d00c3e0300c040380e001d0f40c0324214066680b40c0a0205010301c0c4104911000908001c01014107601c204850f9833285076050030030084039141c229900326400743c16520b81604030000b001080e07110300c52a8982d520035650548a42d001150000c0d03d20407a000c1c1d2030030386040525004465454507403c4469500084c405c0043d030050420003c541d841c02d02c03c20052184c01d551b0140c00d01e49044c01c0c801107440c2c0c1500c0d0b441042040100744811160014001d8020410400001e6a06042002110f0a8035070b50007003141542040e000000703040c0e0003980d580e400740101c40d00118890f07a17070381e042e42d45140c1078115901041d141c1415000c6458400080c550207004001c01141700f62950380d50350b0844e031003038002101d0108003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 215797482 1250 215796232 215796263
    0x14040606020114010311030f0a060204060e0307081b011e08070e010e24070803070f180e070e0307050d03030e06010812070f1e0812060a050a03060504080403020607 72
    0x90244400818040c0002c204585818100720345010f4140000790000c5404110000552000c1010f0203800649509545100c1082c1c07410301c0181d4007030303ca1000066640c8020700308614001c00c82004413504e1320002c0401030303070703104a80d0011038603e52014180b0820f410040030005494100304904103d42e03440010700d140c01e010203400d9824080383c0c1d6042054805a20354036031101c00d007014100250007080342408581c01201035041c890000c00a09603c00882417014081c0c10408540d40784041c2d8944542c03546e1803a242c803001410310320599620019540c003141d5428004d40158000321005030640d0810381d128004a5158000e030b101c1200004d0ba241303540e51b4620000d02031903001d45001c2d005030804c901090b031100224066808054500252072208004002d01c0c030012103400c00211403605409031040c1400403460300942d0078001c00c090544005501c81ca86140c1440c1602e400900d100d011a0031a11440000c0800910440d4030040c100404000350f81d80101403d4100d1040e2550203502c044d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 215798732 1250 215797482 215797489
    0x40f020c1002180402070f08041212050a080a020a0201151401030b0a080a0201120905121207020601061d0f19050a0905010506030a27080d11030c3114 66
    0x1444030701400d5074030501042c2c0c00d185140b0070b03004415404840c09615500e150400b40143d8600f004010301c0460005800030790f0102201c240e0603a43e000c6c2d00442d03402050108180c2c1c075032144100040010343c400000414860956003d0040c070b1207244000240e01550f82c00030140d10303602cdc6d0809940d000d0030900e0a0100c1d131340741c003c00d52402429102c580400c2d240c40c1e0721580c1c84800c51402414080240da5844d1002c2440d4040410690018101ca0032004000b010301015446a84120403c581c01030002d1441400015414101c030000d546404800c0070f42d10040f480c01100403030255100d400c14200c8902584d8181d03080c80d01c40c0c420510100e1385450801048440302195216008050030400100034550303490342a80da22030b16660010400c03611a2040d00c29407901d02c01c003030040c0c06165460b80140038020014200c5403105810030031403003201307602d03481d01d50000f2141e004401808200700392074140900c400032902d0b007801c946000440b61032410224981a550401d015106114120411130b28 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 215799982 1250 215798732 215798743
    0x1b03010b040b030303040f1a07030501031218050906031f0e0d08011503021b01020307080f060a120f06020405060309032706090907110109060506100e060d0515040f020c 74
    0x180115401c01148880c54080f03034a0703000c000c5c405000b06500021101c24401a003e80201461000300e10070980d180411026004100038003007642c0c4500102940240d442c01500e6410070210725042d0040660310744410050030180c020301140d011b00442d5804072460500d290038018800d030404000c200c08050424591514140d8624401080490b400400030900f2001d15507807210301619026030f40302441d00c0d86e101d6801d0000145410703584000100042550300c000f00314021418104454800d484007000c002c859600c034040d0309004088504c0700000515035108202c0c0701481043d0250516513600000780d4990411140780000780c1000070240d9a00c1001c02141845034800082c1041240d12900802d8203400341c2c801d62401007007454040f0b420b042c0200003001e0955030810080c4010b44092801901801e01900c01c58042d21840c11001341c618019484140c0544026014505105003041c844003e000d02401401c84400740207800d840b261150701810300313480c070a030502698402d0410362403403614 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 215801232 1250 215799982 215800001
    0x1404170f160e060406030c080a0c05091512210c060c0a0f1809050a06030501050606030f130611070c030b0f0105060417030906070b060109080a081e0c1b0301 69
    0x1d0300141000c00c58808000300000075500720925020141c0d0360031003c80c00605441c4c0000e0441c0651a1001400c820b000071040107903449528402c400e282d0f10b000703001c840e000075100b800c1c80c1d691051000380a4141144254100c019035011103025801007800010044070300c2d000400024800192144410010401d06820900340f5400354580080d00034010108a921023518041007910340c0e8034280302c0d5403202c0d0a8040e022801e401c000500307201c3e224100a0950344412503007942400001805c51a10700d0a507031042e1098041d50302a507940900760400b1102c043c000b201d175642d0380c0030b0f444040d100c45006405200e12415030b81c5066801c5091110700d0790320040c051070304009454014031140d1503410030f440440384481506240500900d00c2181136010f081100c1e0740148011a040c03050050742c4003020700402d800c0c2c070b400b41c000e500c1c3c0c959640c50b0169400054440281040200401c16581c1e4588000c030000090b900e0400409401d0b807420318101c41107241401e50401600c82c2c2c140380a21501800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 215802482 1250 215801232 215801263
    0x2100206010302010c1719020c1302190503090316121e0c03050f0d02030a0207020f06072001120c0801061d01081501030b03120409060b030f0610140417 67
    0x250b1540d400204210342030513008041101c1c0c1580602500410340590301c3c44d440780c040c410920082c2020003903940480482003440f4441c080104a180c0700c05200f180c1c004241801800c03504000c41f10281c405910140100015204c02c000500200c400d600b202c68030184a800414404107400070000d004204030303400350803c2601c1001c0c0126a03a0402803130320060383d041c1031186d116010310740030082034051014000c0c0c09a00000030400b11000039402810360310f00c02c80780c2d4007a0f24110307000d10045000d45d10000f8024405110f540c594901100c10101d81c10f541454a012a003013074440c0710050341d501c802c0302004151400014080c46030000c81e803424001540101c600c003100460f00091403001c02800c1d406841034200c08084a99100750401e04440c0e001408568403801d4030000448a03500a2068800c0607150902c08260440b4200c1101e0040000018000203a110704007042a03420399255003000b40140f000110506040e404098030007026203000324014401c0c003e01c024202400300721450507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 215803732 1250 215802482 215802493
    0x4031205071b080607080402030c12060a140702280c06081504200306041103070c050d140a0806041e09061d0601030b0702190b0702010f09020f1009090e0a021002 71
    0x3c0781c0c50010722583e010a180c0390000a503140d5001090400004c00b0b11030f9004030620300030281c88400010224052400c02004008034079a5000c00078002034190ba040c00142c00403110546101c028440da640786881c0c00225030001e41c0103550350f14032003200fa44098042080396040040503813101007040c015020a4809014402803150501500d90340c29444005a003804030229180e0389565020154940c3c0321413a160380e0b410701c000c001d1304400c01003804482600c14800790040c000d00c9125064149070740f00307402d10306052000c0d20982d0b004800401c9940c0159860011505072070003911101c8450000d0b05001400d070301c0c5428400e0030b50b4910010100e1105014110060161000901c030303045079004409200651640350707083782400300c010b055014485030031000c403007404411030320503004802c503800800003144030728001c0382620669940a94003840310440c000032400c000c4110b83d800400c91134240000b94450300c490048035000314210100b64010700e2280d00314200244885c404d400c40340003e04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 215804982 1250 215803732 215803739
    0xa020901050402071401090f120e0310022206030b01030b0f1c0203030705010c050307030b0306070f0f0e06040906050301150e010b09120303090d0909060617040804031205071b 77
    0x9040000620500d409960300007000c909001c0d2680c0300240b1186038400070300c00c140c4d9504143c40c90701e02c0c0c0c01080d6404912101c101c1c01183c010140f403490581d01074040c200a0402c0d1807070000a4001c40500406070085038182c9549149450962000e003415850000d5160b00c294001802c81d04240002d50140c02c1642c2500d54030340d1410898040300101b0158104a5025840420705500861000419a44c02c000005283c0c070b410501840c480c0d103031a0340800400c1c01c20360405070360307031019204c41002c600345007000c41c078080c0700c1d1200d5504001c80e070800d882401903000201d90a540240e000600960b070340d201c2407010745400c0c021b0348401140c44603082c00c8241030580d1101d8085041c030600303034030010000303e880c0c60340c4484001e0f51600744c0b414103813503c078074090f01e0482e1110444030343c142c0000c00000b070100303600f1164415401a591140d48844503050720b8042440740300700142c0b050702c8041040c440000020212205070051060b1943c0315501c8240c85c0c9060410031980074100541030343c51520a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 215806232 1250 215804982 215804989
    0x809010b0a03020d060e0607120f112d0c1605030105040203071818110901050111030d1e05090d1b02010f1b02120d1206031a04050709050a0507110a02 66
    0x642a00d40440307404060b00e603149011402400400c840750014092202081710080c7c10800242018581200c06e201c0d0785007100303070311003110050000f00bc01c200707082c4800070806189001854668890611030001317130030002c450b0070164002e54042c103450b5110340d1554074011000d13205c0c2d80041105400901c543d042c140d00081d103520a5000e00342d80014481484240003015401049a074000021a150030b41c016082020085d13008554040c05101c03070100008165224050906c0c0202001c1c01560a1206c010a064090104107030780d40080c1400510300300c004a40d40c440d2a01801a400041c0789000d02c9250241184407080b0b201e2805e2030f034114402c070240c0d070130140400710003290b032401d0308041811940c2d41403450040c0e40043d4220101011001c400000003034101d84010864440c48440741c00c440e45070707041d11031500004103001043c640c1d16016280700181c0e07030b0700507100c0c50a5a071166201c4985404446040326032007405520355051000a80d0001503e90081094002070094600b00d034011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 215807482 1250 215806232 215806249
    0x705010c02130b1e0f2202070804051302030117030a0c08030910090302030d1109030a020f0d050109030f080109090b0c0f04080a050c041803022d01090507060809010b 73
    0x10b4000c40d0301240030040040c035030384100780242d001000100f8258981e8403400e8011568850700d40910007a4110500740d181044001400c800701c070000810400c2d480140300040c0d00207142c21035001c0014031000c59aa40e0b450b52040c0301c0740302e55000585a42c0b4016101c0e050b00c0030f4003c00b062541007008210b0320b0b5544600070507103850300301d00d0081c0d4039214140d0040c50100603003099044245410f0f042ca080642c040028519144405802d1250410292990f40107120300d003400b03a85580032288050050900704c10030040310300024a416001d0b501c90b00c2d124251002d1400c11400608503803040b01d001a041400c03903000d0001c844040008280d1035440521075a0003600307041e585007020560890100c0308200301c9000d48142000e985e0518810710b031881d40ca07a4000c10881c400c0e42400040c54503511404250100146c041d4028106101c10040b00c010640d0303203206445c82d80840083c100f8100d9400d029418078184950010008545803000003044c0c000058030500d45039041040700f54203a07455824 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 215808732 1250 215807482 215807507
    0x7050d080f0a05280903030501140a0306090303141518070f031a0a03050c10140d0b0109091805010f05090a0314130b0c070608101413021b0708070501 66
    0xa82d0b4072602d15910012040350f030301c03001302800c8210b81644124aa00b0542c1940d00c07a44090205903201c002c007000c94846901103075048545c48100704040781041d008040914083d050000c1e44e411100c128540744541261482d16040182c8030350b03070250805010b1500094009500d92105003006c840040100540e40c0c00001099100e840b05e03215900c0900f144010381400a0001c049181c5d03d162030740e207940d803042c0f201d4450b81c0000460041140543c2e03010740250350006505190502081620300104855200a81000301c4202c0108002c040c621900105c0203044a811448100c146401425103442d03101421245052205124500100003802c200d4141e041c18440450041c0d1500e04d0018020005015019141c0381000561105c100000701110201d030350645100c0703070b15158284c80c0100c0503184808840458602003140c03406403400043c806078000d0990340382102d0a400c0c00260b030001c41e005c0051403950021a062424108030303440c0240f4420020340a49840d120020b0909020050f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 215809982 1250 215808732 215808751
    0x6060a140306150a02010e06010b0c030f0c120a1e18122d02030708010603030f0309051009050303060418051902180f10080c241e07050d080f 62
    0x418029543d03540f0321070041c0450144240c8942854400901074501110040c04ea401040000300c0d04038855001c0702d0001c007140c40110701e001c0200c4520030150b0300142c0ba414483c000c01c3c01c00f00000300540014000c0e906190361741c81c0e1680b0b450046070041d51082c0044030520a200f2426891030510107500c1c42114688070300300448044070700b4035500c28100c2c035102d00c00989001c0c1d4542040703032110040220b41c5000780d00701d0390740513102c020b103501302c6480c1d02010700071034040301d00014480d10940049002600c21016100724141d401c42c1c520503075881d24011103282d003001c020044581018451164070590303001030740240b0700c0c03152100303171b1182c2e0703205442c0d80c1b40c2c4000500b890544d10360302c4913070250031100c40d608105440e0903c071403a90050140c03100d01e015003920790b0000b01c00700000b600301e02010005049004100c0c91100403021054a10704081c0c88110a04c50001c1d280c840d81b513170314000b0b405205405d50b1070f2100e103402820184200382100901c10460140044038a0400d510356000f200c41 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 215811232 1250 215809982 215809987
    0x2808071103180111030904060909061b0507060b010903150b120718020a0c050f0304030303050601030c020d08060415060e040b040204032d061d0f0c0d06050a0e190b06060a14 76
    0x10034084c0c2c00c51041a44c55900103081010000719060a64405070490340160000c00084c2a0707040c6034074003608101c940c180020070500030071011803981d40c801f00c41c10307c050629040c0f141e0b0300e6a5200403006880341100c0a5952246245503600344100100441c0414402400308541840700240246c41d140b180c00800950105480040074066000b0028550700002180c80c030695088030300d6920b42c4640800c40000c2d040c540420901e5000b0300403000c06459540140070020b0008000325020310004200c41da0203a2a0100c141900c84d8410581001c0c040366551203618280c104140016104900d985c580101c0c0304000400214224011201000342c0e00d10000079540480201c0c200010900c072030242005160100542d030304500010500e402c20540ca040d0392a03804400002910780202d00a0143c009070080980400160998003c59101c911b0200000e00d04a10441e040d00c0c06c0e1504445c03102414510380074405224a034a4003d6010400311600d0b80344c150300400c014a021540c1c142114200b001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 215812482 1250 215811232 215811257
    0x20d030f02070812150405060a060c1110020703020109080f1203040501020910030c030b03060c031501051201141318080c03090d03081906050f010528080711031801 72
    0x550701140c80090700901220345912044280b0346601206a51000400382109641c80950815004052050100400c1d984080e850418151428003c144080b10725500380001c805013552040311480b45034010703a0003021581d007103200241092180c1d412920f1564000410661000c20014100c10200241c0d4000364076a201d030315259029010b580c4c9610340c840c40d082900318010741c0c5a80850352150240d40d0600207400900245915100c040d2041c0728441e0b004c00004034044e08a500d814580035041c90882e1401c00c0700140c900d229003007a049400211a115030403c202c1ca0301012070203903401035001c00c01c481003044c0b076003c007501060702000f0403044001c41d489101d0041030082e1516408060511400c0c6002840c00070a20f1904407620919994a105034a0300f9081501c210010b0340c101070102c100840381e071001034034240c0119003442004009580101e0300440c84403070304011140f464480000c1707402c04c03041c050009200395003410302c207500900c120743c03201c144180149001d04080c2005000f1598 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 215813732 1250 215812482 215812511
    0x30c060a0e0a080a05161502060f06120a050106080d0503010e011215020d05041506060e0d0809150702030114060f10021006060e0307050102010c0c06020d1d03070209090d020d03 78
    0x1001c0c1e000c803c05008104283c01400408914030707110282c011640d806035600ca45402094a41090402c40180d1242e00000c0032100d440e10201c1d00004010706100416079400e001502c0e000c1903000460700c0e0f0351240b004000400c0b0810a040c1e0300d030300e2400e049007150f0500312012910401445094140c69100c03460b0800d00581c64003118280041070010365481c48040013031000743c44155012540404c2000c00036043d501c0074400c407001c0e2850395490703043e200040410080c140200c03213421350f03101c641046100129541c0b84031180581c403225213001e4403085180101070844080803980d42009c04803008200c1030340d03100b1204001c5550122035410385075188010480c5402220941c90000381d00d40307030021440c0d5800015500030088218210b40805440e01d004909a0b1004c1d1005c0000ca000d409a0000295081e0040d101110700034200203500b40b03c400000e10844200038001c101d03500300051110035800c100e020681d001048400500449401000096544040d04040020582d603103001c0981081c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 215814982 1250 215813732 215813749
    0x203100c030213030308060109080f0c06030402030c03010219090b03102d061106010b1608071506030602041517070309050c0d1b080c0a060302090310090c050f030c060a0e 75
    0x1083e9140d84100710f8680c5406080041d050714814081411384100062400c4000386043c80c0c065a030020b403c8003040d0000b400150303000600100c0e07240c0160310002c0416107091000d420045100019006403000d1201c014144900c0d50300008248d00b8200100079281e0500e0015008407003604000f12020030700403407980541020b081601c010100c94440021f001c50348413000c01402d040f0041560001e91303a8008040c1680314500c0b11000d041c040344070080201d491080544801800f494070440307040042c844c90412624150802c41d003a90340814180101c060560008070481c440c1d040c891180c0c91000c1083c038101e2001064441050380391400002080402c2c4106102d010b00640103141411007458015200a0550304160b9407803014000002c2c59078001a21000c0c0c1d01001c0e100c505040d00b001e8044000c4e41c0541109509442a4412034130301081c0343c4101c0c80d83d41d0040c03507202995800c003001c00584003140c1030010300c642d203d29003084031944c8180884450b1680c0b030424102c040c03c120080342d03080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 215816232 1250 215814982 215814997
    0x1509030a12030e06060f06070206040807080a060e0d12050c0708070b070e0108040f020613150309020406050f150904090803160e010507030c110102100c0512130203100c0302 76
    0x14051a10104100000011409014112030b00c0600010400603071199544c5800c4495541c0514a600f2074000707800c06200900700940060001440e041d1113100c0c4500c0c0448030341c42a045907000040300824000d8510401c248020804c2c040c001714807041c68010b0455402104d0344110a640320b0200714500d032860200c42c5840c0d0320501c0700d80c94100d9410308040d200d00c1200c150021903180f0f541e8030b004e03610407007840c3e110f90782c0943c0d14141c50515809021880c0c024010601d4880e400700705c0444c01c0700100916100304501ca0741d0104130ba51351441030000303030b50040d44450301980d5099900000c607518444201d080490020041d622190104000f034040c040401001d03188170000028007101107a4525014021251620703902048440b640044071980300b006001b90024a031b00300280b001604088402054440520458038210114500322040315600034120300820400038024151060080b1025403110320b080d00c0c0152013800ea00403944500807414445c0b0074075039070082c114040d4080c2d03040d101e04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 215817482 1250 215816232 215816239
    0xc1505061909140901060e0103140102070b010803070516060f030b27100e01050d020603180607020a031101020f0f1e04030c0305011409071a0c060403052709061509 72
    0x45660340e940b00c004205400b20f08050078a00700000c0c00b081d0781402000100d40c0c0049008046a1842d01c610324035000008040030f041d5020000d1a01045007079098034041e081035006150365104900c3c00c1458026681030400107010812030410002c0c0d00015004000002410b01040900e030600c006030f03182810500c407418144807540c41c407500016414025220320302c581e4002130810340714483c00450b02e07024031601d42d018a854816900506002019680100c00d02c40115640c5a1000c01c6504107242210900010f91003007200300c052541c0101402125003050000714984003144922020718130910300200c2c0c4414000a0040c0346149400104903964000c0303840a803a2034030f901d05200601090700c01966990b00704050280305054508502d03000d01d485800504001c0e261244450540241007600c000d400310510410032a000300340810340c81548641d0f94540c1d80c2c20b8002c845200343c4418142c5103500f802d000e48888175030700c9070700f039503508548101c41e5908108a0304070844514411104036640 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 215818732 1250 215817482 215817529
    0x60801020f09031203060d1401020d0e10061e09050912190306090507080f06010c020301090605010e010803030c03070e210601030b0604090f080c120a0815010c150506 73
    0x844404040d01c2c02960031000d40341e0050f44107403034100c50f003c03e03200c030396004081049a400084203d01d00b0740c103100381e003070000d803c0c01d00e282201c0382242e500d46081e0030250810003480c41059124450000038107901c2d51600280c00280c00200c894201a00031130005640c0d138030100e0f2841000b0407100344080401e060990b90f0b1f5501c003902c0180c0030400c030074450109007400760205101d5007501505105410996854200f0b80e00c1403521603200b5000b03403505050068080ca03000250f100ae00071101707018041c0401044951401d0f2800c001d8030340c141d005645580091003031241c260440300c03c0f03c5c1c0000251402a048405801c001240804208902000465132840b802a6881e012030b4840c12070380640d00c0f601c4a1390314101030000f591504031004008440c000e4804000514200181040c91f91ba00100d49866060050360460790b40002d542d100070411180410080009558166602d01001c1c41c1503402c9050640e0f90b40c01c0c20004140d000340c0d69845800052883c0c544c542060011400c4201e0000f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 215819982 1250 215818732 215818747
    0xd0e0309190504060f0501050a0c020f040603060204030b06100219032a0c0510021509070b160b07020c06070b071e0522051005070c0f060e010210050907150306080102 73
    0x2520007880b8818580240d0500d100010040b191010810454006840311450200c1c0300000b12001000300078100c0c0d02c18200450303040d15803564031030f035405507204a90040c0d6542c2181403403000100c1c0202514440c4540d0600b100c8100d42c0812050301040c00d004035004403030b403a460195030b030103843c48108581011060520883c0c900000c00780034040c1c0545a100821511b1b4020300c854605180020000342e480100380401d800d500c007070b500360b10400100a44030680c1e00c072540280d05500c9140a129003110100707000e0144074100368003c0c1c00800c14002840540f00c41008500c9600502d1b00280806600c90005501da6005402564440c0000c42182d84d0040e50307202c3c0586a0381140e1903d8601c54800b038941e00d20054040c81c0c00b001d5640c0140100419000340b10110385560144d00f0840b010b1103150300020f1200503400000c1c0103080c90b5100c40030100003110009241103480e04210071641e08200902c22802804600081034034400101c00b0b40036410380c00150003810f119404212650710014104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 215821232 1250 215819982 215820019
    0x5010f0c0c030b1905340201021314121b0d0f0209180706080408040e092121040b01050f030c090a090c0e0c0d090c0b120a0f110d0e0309 60
    0x81e003106103401c41003001e83c03120808511003d40f1ba6001705419500940c8162580b203083c000311700e04109610001d841e01d4807025110040195a500c00c5007903d0388040549014a451007911450b0130500c402000c0c0c84800d200b00c2051440c0d001d200c2806030151180c0603091100304285464084d80140c446c070f559051002c0e1901a06e4480c03110740c2c49900400d20049080b510890645004940010f007484c00c040c20200d03002012000905503104520810407000e460301c800f00440d80141400c0c0c00303800d48901c00c080108800c001c6a04200d91456203c004110001c0c00704500307541074075425170f141d030030495405010034035208440c02e815034012030f90010032003001490340140390800e00c079803203c0184a0366003140c17001d10300c0c09035184564500d00b845200e4001000e9480a54034a0040314104005540c440c02c0c4c1c107059020290000000c1c007101d0403c0800e448500a5070503800218008024400c1d10b44000039180c01100d13545422292070344442e041c0304000b0016070b00841e800904100e0f10102c3c1c807940 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 215822482 1250 215821232 215821261
    0x30e1506040606030908070b060a03171e0403032007090f0e070509070f0f020a060203090c0108090c0d081305040606080405010c230306010c05190302011505010f0c0c030b 75
    0x2030038400d908165021480f24403030301480201030b6000f00058103144039691070314003a160007480d032900301010010010105501c1c0e640e01c554451058590365840b181c3c00d196882c0a10001070184138814100020000242c1c070a90074100c4c101070300e1015400d5035202d1101ca0810032140c3c40741900e2030400715558150041580042d500c821184100e4843d88ea40d0307804e2000c01003007100ca034000709000c80c034115070b510700034141542d0f0340c10b40d4410b032210031540740d03589012a04240e0300c1c0e0f62144d00403139903e011960030620303ea0700003010358010041e0f960902e00080503111040310040c69100d022030003100b11a0100490b41c0030708001841800215203d030030040c0100d030102c9091701c11b036003065040b504841c0030b40c8010031269240c03c071008801c52004040807040c0d00240200d41001440362102009c41d605000350791129400e8894000a80c881342402400e4880e458000d9445030f5800303030200a240c1c1c01003064031000c409414500c07035000c21800c052126520b00d50000d4850b155000c01c004101240411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 215823732 1250 215822482 215822491
    0xb04090b09010b1b010b0d0308040209061f030b030109050a060b0108070903051c020319090f06050408030912070b1303031409030c2101090c2612070201030e15 70
    0x10401410300944100500c020082c803440210000400007440c0140044000002d0503485400100708800190040380d4100d60341c20081c0c00144d409800d100441c40d150303600940003c4100d501240100c06181c44d001200c0d07140d6000f10906540390035060a0703840039045001c0d02034100e4181d50911525060000241c204460500d0000d54070600040915029a03614000e50707070000003e103006041900c1c2494041d82e400302020a51005000c0041c6180318030010b2950300000381c1e64000d6042c0340c00002c44202e080b130f812010a011042c032084c40b09507000010b5448400048524420440348031441c2410144980c200c0103900c2000282a15101c00721281941102e11a558080c0b55440e0340c1024200340c000e05546960682142c4a0000c0074500032024071010000400d0400c41c110301d0700e00503400c40300f02a004444d0031504400405c10702c90002140c550010c10304195030300c004440721a554413a80d54061182c5261008101039055902c282e1114000f18500e0b01260840780000c04803500540d030444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 215824982 1250 215823732 215823749
    0x709091101020601120305132102010909020c030315060708210106030e0303060405060f04090308011401171f03120806130218220c0809071d040f0309050a0b04 70
    0x30502a940d510010707a580c102d601802082e240c00340325a408a440d40d2005401c0380e03081010300d401048200c1c01c4202050900d061003411b071289900ca100161007010140d100740b000d540306110081d507010000c81182e5008a03041c10542552050300d000440600610798007510408002c83d5459480d4202e40d03603202400104841d51140f81c2c0c0e1b82000302e040e203a0b002c000c2c000c20b4000f8408180345003015006150000700040041c4403c620400101d41102c0034400700b1342c00110b85400410021003401140066608203280c100c1d1036480d80240c0b440410340143c061012401001a981c24122510006a016607440000009501000d1a00070200b4000b0f0351500e00c20031440c0d10450000c0d01500c201c0d10380007240002000807621f0801040360f00203400454090100046102c1c00f40d03c411880344502400076500c03202054145100c0c40d40ca02501500b00c940000584401c000444102d41c0f00e00b41c2c0a07a1100e44041c010704130746821102c0e41041d034046600300c0c408040205400d41480042d106a03107031030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 215826232 1250 215824982 215825003
    0x170312010e070f03051008160504050a090b010b0304050a0203060a1406090411060c120d05010f0e070c02090a02120f01080f031306030c02030c0a0818010201020a0f08090c03070909 79
    0x1c01c0c40201c26541566001e01050304080c0f0705800030300a4102c5540482007452500c1401da4400566080541306640141440107102e0306012502c1d051141a0300454942030400020304240c0e185e000040301030190000c1c1041c08400502006010444880a168040c0550f0610b05181c034881b405400da1031000d15071500544001003141c102001c845200381d030043c081c0c4442c81ca041e011f100103640865541e40c070714003455160b41500210500181040301c11000005950341c9401038880c0024040e8020001411208050000155100d06000d03103160b01224001c01c1c0b610b50400d87c1c3c0092040082288103aa030a80400100d5101456964100d920080a40e4943d10451800546074454840008101c24400f08280701c840c2c0300743e000036065082801201d00c1d0019803042c0c103240194034202107035101400039107540310041c07286072000c561000380029408e201138440081c2032102100402d404120b080000141c210800708100420100301405440345581c449004a000e45019042500d5040d0700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 215827338 1106 215826232 215826239
    0x90510030827030304060519030e0f0703030311120408070215120402100837020c0102070c06091d040c0905090a05060c0306150702030717031201 64
    0xc10480b542c140002c003a45082c460712030541d0081c0c0082c0300412a480e0018260340c140014045103007808400c00f80c00b00e0080c118914030308001c0c802c00c1c1480403803000204014050f03074002c0e68203022800c1800c1050070540301c1d0b80f200607030410300440000d000c80c0f10301d005003054174070041030703000040601c0c094014180c04c40d400490140e0300b058280800c604d000c0448039003105041c02d182100c0e2818250050f03151a1032100030b52400d9196001120f810410a484003108a0081c8215242c020064000d8000d400c000c070101c5054884820100e000c501550300c1070b00311101c4811400000360703080c0d107403442e90b04060811202525120b201103207125040c0034051041031001c00418000c0c034a400c200d882c0540141c40512207402c20010304c1b2094848240880c0c41302c01b0703103906a80d11003451000c00d203805615844140c0c8c0c11180b046200281102000824102c041890f450942ea6203 = true := by decide +kernel

theorem cover : BRFrame.Cov 215647482 215827338 := by
  have h0 := BRFrame.cov_init 215647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 215647482 ≤ n) (h2 : n < 215827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
