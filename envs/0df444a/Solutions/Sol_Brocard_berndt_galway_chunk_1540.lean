-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1540
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:28:21.132194+00:00
-- url     : https://prove2.me/submissions/5a2f6310-de0a-44ad-b0e6-209f93d594f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 276798561 ≤ n < 276978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 276799811 1250 276798561 276798569
    0x110a050102070c051801030b070f0e030a060507090b210403050f0705060103050d2a110a0806150103090503031306090212030a031d0a020105070204020408030a1d0904030f0810 77
    0x1d64540c0322a10782014150428082d43c0c0c400ea82115002d9039078104529418122600305244c0ca07017130785400d0700c141c07114911402040200019040e9458107514100140d4801701c1c451000002c1600c0d140800401094079a00600c1d284107003048071001c0065198004a50440c3d40c003074444642d00c0d50310741503646210341000040e02d480b02007803000600001141c042e049900030000d480c5403401c162030451710782e0a0141d41000030345440142d12150408105c490540078400c900e0003da0320062000650521101c4c2d0101e06103500c80c0c82040f52102c151011812074900a0030148038078841c039520203450303020003040d41000b202500311100900c01030307400280d16250054185407035408103062003a240c1d13100c411608017003400c04c60300c0440b11100c0c29180d41540398140140640c0421603004583c154091141a68059024417022070450400e20007003600a041c2d4031000302c1d40c2440c85c0700d02450208000e0315441a00110100004030360007011604901a051500c041e240e40c40c0c841240c100384580d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 276801061 1250 276799811 276799813
    0xe030d03052511070b120a0209030c130209011e091505040510050712110607030905150f1006050a14030a0e010e010b011b150b06070b042f030706110a05 67
    0x102102d0581c0c1102040740c07940040019584420740f111a01d0009110701034108025110030f40018070120095806800c1500d002010788030044081c4002a110800003c1529041580000d60440a6801c01c203561810034400003008180f1800d004042c0840e2210301c00d4032040995031410040035441141190701a110040003941403103629600103106030491003013250000000c0000200c1c40e8082ca88154040c0d58a40003400e8503030341d41c41d0803006480d02c1034044526110f0505051100c604043c075041c85080c11a0190041c0c2c80e1100000c55400c0b002c0c0c4c814014071000300040d10649a020840c8840a0748c07081d0b280e40e0b2502c900816100904680070050125460b2280501c1c6590b01900b00c61075000003680e5075100310800e108030705203052030184014022070f460840c0701040707083c42e04541f199000062901d820482541c030381e8100c1c031000329002c0f1241a0030445801d007003c0c02040000c905981d02003861201c1ca48000840c0c1d64907102e0081e10140314100c0300c42d0066140c100400509031f0f80c000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 276802311 1250 276801061 276801121
    0x60702010507030212030a021b0c0f100c1707050c011128080a09090b06090a0e060604080a0b0924130212030d0b0f0105090a09020d1b0806030d0e030d0305 68
    0x40180081d040321a1248078682704d50000c00240000103001100c5a03802132440410310100020003100c07070344070a0750000340310400032030802084250800608151800ca82165a072545140031414620030140307441c1403148549500c03280c41e80c0040c204041c5901d032168440318024441d00f08035007420320320000300000400203a0841e2705071b10092040c22104500340902004501c102082418059030040e1504600c0d5410f04100b00c161448200350080306c05045a450152616841414027005140544050346540c09001d003c41e01000914881c002c0320f588940800552040c02c4048c0b800905480028070352000d0200565440000c203140c100a03120443c0d654158810145029051140c644c51042542022034603aa500450446a904038001c028401d8a410200c0c100029080100400c20f5140d90308050300403064012428000b860701070702c800950307142490815207095501c07280b1100300481118402c0a589001070400070200d00d50401184603a078840c80707604168080b500146504c0c0c0c0075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 276803561 1250 276802311 276802321
    0x1805190c12060f0522020f070c08061e040f0201021204080f060a140c03040606030209010f17010c0203091c0b0c090a0b0a0210020c0a0b040605190b06070201050703021203 75
    0x60510700075454185410700001d643d41540f0100e10700700d44103a540102d06091170b4130700022070326044040341851000050511484e0810000a60021042103440c0005100140082d000800c22543d00c8050700c40e00380e50071901c0d50404041d4200280c00105031407280f948420031a8000d005031042c3c50890700f61191956610b140d0190303900e031003c980000314002c840210f0800407440c02901c1e200e40081c545030100c0e4440310100840c0d640006c106503030702070341c038000840160b64981c3c180e4000c25400c5480120a400d1100c400410032100c060b950042c0e1608490b4519607401001361590a0310131211070000700240304500000201c0240004c109140b040c080002d4080114042c1c50700f0001a03802e406015240e03001070303003107103c9d009250026901c820301c0c242c800c0c96207800500b813003800f0000742c4800000303950b9890501281601d046854a44501c1048031241032140d224030074045515092104040600100b003041c0b1035070001174100000020441c00b0705000f080311040018005540c0340e624a42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 276804811 1250 276803561 276803567
    0x50906010504060501051201060c1416051302090a1a09030123130c0e0601170906070e030304030b0f0c07020a09020a1e02030d0510080d020c191805190c 67
    0x900030716110724030b0410049183e5205106036003452035403400d090226401c04400b900e000410b031404a5210110050b0310007071090a00c40f42d100c1910462101e15036504060422140041c0640900301081c4188074003002580c80782c003001c04a9a03401e0300c02c50840c00f9003031a1429071052102941c0c06600b014900500c0142c6030441c8400a8100c21030400e0548a00010104643e0000406400c00e03200c20002d0107581c4600c01c0994022505040010b0071100c0d018075510940700454500d10280c0020042044003034004941c0d07c4692411005146428103580d140c00040704094841c00d501404680061604a805c000712940650002d1904000c3e13a95061500040d40c0100d25080006079460b45030343c1d07507405e43c515142c90424250040c50504010500242c01010b00500400042c40041000101d4801c140080302c91140c966014180c0c0380002000d202080e102986c0600070302449400030080c0418804145044141034400406c0032b440c1c0340d8070007a6515081e03102488246c40c2c48181840c80b50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 276806061 1250 276804811 276804823
    0x1501030e031804060603111902101b181d090a05010510031b0506040b0304021f0908070e061c0305070816050105060301050601121515050c0616050d0905030d0509 71
    0xc2c112001e100c2251900012030039200240c0c1d103060442014440408002e00c1c0041c408a00c414507c11240c07488100d000c1e040c01e13550541001c0810366180301c0503503007442e40a001e041000078000d07807030380010745400841840e07910305c01d401d044094a480007098070560309111040050703402c0310091241e814111074100d6040198401100e188401e00301c1c05980c0e21140b1846411140014403003824645001c02c9a4101e520040c400c07603015401024103000801c604100035038000141c0e540c0081741c2d051021462528803150000b050101c0c0540401c0020780d5040d01e00b2044502e00401d40f1080003091070207580900a0740c40040403000b002c500c5d550400b5411401824207800b85c802400b094860500307041c03c8410558085d0300103409144070404280094210b8810000030178402c507540340c0d45800c0400b8081114050174002580050040032000c020000309411606542c41a112806c2014016182d441028030740c1941c691140080c909001c4144151941604050024495890040780d1140c0f10700c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 276807311 1250 276806061 276806107
    0xd030203010608100f0510030b030106080106080d1b080a1206090b1305090c0603150d050c0316060512070512040302010606181805151c0303050115081501030e03 71
    0x1090380e8000748804c0e400c000300c0e00c00c899a55900e034203014100818080b0f4190007400c101b040c0b5131111421890b0703450901c0340360014400d0b20300000352541049000c50030b150105005070104900782001048081c803210701200100d03031111480785d071403064100a842e400040a4a244030703902d826000148402c4541080041c40c4040791480c801c0c0b0045048841190070036540c281495010340707050b00e02400c2c40001550450f0315501400301c40c010398400604080224202150b064203d0308800c11103082c10884090780b4908141c915a10501780380004059004910300c8106032008000461049805607040b15600c420715410041c0c50320389414042c0c041c0400b88038810004100307080802c9813100d941815000d48003107418448444030442070900180c207002d401c0f820b080003c51040c407d0342e50303403040300c651840c1c4501c00b9000c0709005040140440303805a11034600d4148403603c0c161006d03448062154811184200000c0303040400004800a20b40d50305100f200d03202c00a410220f600a10f140b000042d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 276808561 1250 276807311 276807317
    0x11060c090f0a0303210203160c0213020414090c040501080c0a1701030f020306010e1003060f060503010207030c17031501180f0b0705010e0a020d030c060902130f050a0c05030106200d0302030106 85
    0x1042e00700404100e100444148c2c4000c81110f610f21621807007015404900b0f40002d1a800714541d0b02010103049a1181c0e004160700040e034840c0000c181008881158042c2c1507142c82800d0a25140001e04144402000201049400540f40001c1d901034072030a415507000c102110281c2d0b84038546000c0c02d80c45000300740d12a00c100d1000160705958002050b218514640f00a08914990b940300005090400c00e4003182030703195240401d1a440910242003204c0c001d50f09c10750701841c7d0742070030041c2c1040d82c0d18000045204004100c2803c1e00e05c2201c04070440c0a1a146141005254035000803503030b290045401428001c2002a04c1d0800c5c4028021190152008005132440c1c034859560302c2c1009000203400540c07800038480404d0081401c596014019080405d8251403680041e5050310429400c60800d0b585d000e845e8940c01d1103100b484d030300100c404401c00001b20f03103032000f80043c001441041e0404c90000c1d8241009104110000c808013005803c90340c60795041d420182c042c2d0801d005507000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 276809811 1250 276808561 276808607
    0x906090c080613121b1b0f0911030c0f0702041e0f09050c090903040b03040c090f050f0a0c09030506090a140d08041502040510020d090611060c090f0a0303 68
    0x40062001e5420100d90388050186400c01000c401030b6441101c014178a0b43c83c4900340c0043d4085103018400d5a50060f055132481e1030035080040d8040f040350313035070032000846180810b0100c0c500070a900b00c0b071b085116070900c80e850303100440c010441d0f4401c03540000d42050500751750020044c01c241000401500114050040c84c41c102000d400311000c10364042c16990201075009854140048219004000241901e260648800b04045980d0040e20100c400e801031701d004100c03402b018840c928000400072000c0c0001d041044148401c682c001d85000451ba41e544160003000740981004002540c0c0041070390014607229500b2b603100d1002c0041501e100b045d405d00c50400b2080403660f07030000f020319140c02900d5140c5444502c1046810700150b4202035003080302242c0c5650780500200006483da00a0001d41408a4001c148001540c82801480340042c42c40010a50101345e80f079014052030340780c50f03c0b00300160000d00100c400c00d08139608000320000200505512100c0501454000d50070b1040c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 276811061 1250 276809811 276809821
    0x80d03021c0c1d1e0f011701030305030603070f060e01110f070b030907060302030106051c150305010e1507090b0706061a0a030c02030306011d0d0209070207090f0b06030c0d0906090c0806 82
    0x302d07010072810b030b540345420341224280b01d403174002c0400400600c113140c0320000c144101c03180922140e00380c03c203801181000c01004194039040014401521048a90780343c000d00c4c1c0280a0140e04001d065981405088000b07030f03204000401120325095226002c40d44860307640c10b42c1c0d0003160700c162004103c9000d10b030000302e00f80b4000d00850381241d00307030383d246d503e40b0800d07060202c800c0c00780a142140c83c0d601e40240051034450804002c0245000b6000044e0241a29940a20307048400042c00b9001b80c11350304101d800c60300850860100e4006e80559070795519585031000003814a44c1008100c001015074070030f02040800301070941c451407510104050140c190090381d0744d00080704ca0900207201102d10030000417401482030300c0c104010341490750601c030350717400101215001c8407400c00607072100702c0802c0307500800d010303070f0071402001001040020800c001055091000800c0c036600c040313000a844124615030b5102003e00ca80003101001404100d2401c6c0003807a10f0787c070407000b11f482201c011030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 276812311 1250 276811061 276811069
    0x90f0b030f0d08040501020702030109080a0e04151707081603020312070b04020f130f0b0103110306180910060305030304030801050402030f1b070c12140601080d03021c0c1d 76
    0x5101d01a000d00418480c030407481d08484080c001441110155000d100010068030240101b0509502c650911380c2c896000c0b00000b00740354041c01c0c03918440d030b081c1084892804501180a805e40c0c58814040600700d048a4265207401c0840e480b034810380c0f0800303483d810a103483d402040c003500c0c400c0341a5480915814a10310090140290240a038003003100424014a404071a000f07660390041e20349100d0030000842102100c0003c00700d40301c07443d250581d2550f19030b03042c402d4a5089003a084513a045040020100328804086020a0710301c503624400300d000390408001c0107040e40400301c2e05008842d207903d0215200d8200383c0301140822003410000c65140790900035240302d414601949095507540445841036030400c02c040307481d100340c2006684c011130300b0091040f01070011034054240d040018a007000c0144855080c2d660550001d0005001000007c120948010150301c0c0250b01c0e20580b075400300c0c0c04150209a0780d0828508010000016040449100414800320f00c06e8600c10f0140280 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 276813561 1250 276812311 276812323
    0xd24021e0310060f0e040218030114100b04180c1710030314070519080d02130f09050403020a061a040207030806030c060c12160506090a0b25120e0304090f0b03 70
    0x110f0007102c001151411b0030303400b034405410041003020b0104885008242140c6008039401034011200c420492000a0b800c5064014180602c00c2c0b0b1420386404400c0741d0364502d00540580540e121251428807d11642c4500c1c2c0c8886110110b04413070400e60301070b02d40d10010784800c5001c03c0d22500c4c5412050740010507500116040009085003c040f40c0300620780ca00f0030601242c0a41092080806a111900c05032018800c0d400d20003042c0307800c2584800d452404c07948102c05060030002044002a400301d01020459403003280801c440401002600c01e441c0da903200c2c19081440411040c1c02d156000700382c1e9010316810390a9544000300241032069501c11840c200071241c3c408600000d01c80c4901c8000e240600008040c4000d4054075680c41381401e405580d0320b1030f16488410140184041e503004150006201c0c400510300340071401418102c1174031943e00c4c0c0d081c41a41503e5103040700c1d0307130b4124100881d03064050f00d56880d25486408010703c00c05480303400c0c561404112107098100001d413 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 276814811 1250 276813561 276813587
    0xc0a03080301030201050c011b09031704050a0b0c071d04140703200d06060603061505090a0b030603010b03060a06061103031506032502010507030b0d24021e031006 72
    0xc6107968219001503540b80d0040a11280a41d41d41c1144000030603208599400d05c0010741e140d0740a28a5400c003000080300c8408242c9180a040004029175521701e814002100ca10000700364445800305040d5080000c00e520019050100c02d52071103040d400440c215105c1c9101e2a0f81949104400d800d1654490980c007005000107000c000e4a101c2425174040c022445400802d4003a0400342e030350700c01007660550307440f100112b500d400d0140001e11001041c10070350b00c880d10f8510b0814480f64009080080e80703101750081d200b00040410210389003900482507202c000342c211095810410310040091515100b00000508072a500c48800040441120301911400c801c030f030b1010340014100030f620f500140c4807206e44030340e40100c01c00a80321039000c8030602c00c3c141c000050a10342582c000d0140d0320011000d9200c0d000040e0705030001800301c41219021000000744050060008103c407000b40700390200307456101c00b44009003e071400403e00440c850240c06c83d10801c687d46d28001940d010a180381c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 276816061 1250 276814811 276814823
    0x1503381816050309010603080c01060f0e070504030809040207021f020f0a030c110105091306052119031404170c04090b16090b0d020d0c020613030503101a0304050c0a03 74
    0x8260301000b407003a4040e58000403842c4c000928150341340d0b25280950f121030071a03242c0e65104e140420041104402000c01015040903050301403601e000014581d100e60b010050111401103040c14440e00d0b5039054468290b0b01420303070300c003560060483d424003041459901c40188642c108000400740041468138405a040c0c070740c22607008031503403101080303000071034140d0410a0a2201c441c40760b492104440704645090b80005410b424102405072981240c4c005c0140300000030141d910307642002a031084055080c5002c3c503600d06440c41d0486489140c0055006042c8020601051070080c1900008100b01c0b0f10040b00c01c40520501800180c0e01c0850000e4403102041d0b00080c88001c481c20b109554070401d2800b10100b58030703420240604d8000805250000c1c0d80860400c800100500c0f54005d108024002460103140008a520020ba2405401070410001002148803203443d142548050700750040724626200c42c4224045003a00708407029101b074825080c13980c03141c1c2014000d150039039401213 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 276817311 1250 276816061 276816091
    0xa0f0504050406090f03120e03030105150a0903050f0705090f040803060d050309030304090603020108130b0106050702041e14011203050412030509040e07080d050415033818 76
    0x208000051a0050043d90038070303107030340b007040004501034201301003503201f40c44115a082c1d0950b8140c04581c00d42004000b16032040005200725512100132101d07540d86040c500c2d0f0b0301c0d082220111584425540014001c0c46507102c501c2080e04c01140c102c064a81c01d0b184080c603584c070040c01801500003035138042c11840c02000802d4403401d00003017038040346000b04122442c1007401000f1078515802a030202e120b03540d90f0315051003190703800814240c11148000d06e010100c8915164a80f9914040c4106801d11100044040c11034980e41c20080d040105e1400d20368464106030114000340110014904a4100020000caa40d02081c0e045810094141d45c9650900b810320030301400d0140040016807d1081c01d20040e2600e42d00d5000b5103c0b8080c114026211851400c0001850f01048020000c00e00c841403005000e24102d550007440c941060380703030224106041d900741000d6000f0040081c001400161140f801e00294912200c01c80a005d48001c882ca8030000700a0406c401c09481c0d07814400c0b055 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 276818561 1250 276817311 276817319
    0x302030103080f0309150f0106110a030e0103051b03040606060201320c07060c030606020c011b0f0303060308030a020705070608040b06041d03040305100c030501080a12020705060705010b0307050a0f 87
    0x900e0213198003001c5c0700103d401005046800b00c0a10400f25111840ca070449001800f0056000900e048044150070041c03101c0b80d0103a40280408000d480e0b801e04050b90741002844400012016a0390742c0f01ca44242ca5036418035041101c0601514003420002d50309004150028082d82401c0a03008140803545103c101019001c0741014103002d415558103a10a00401d404282d240c4126100d4482a80b000102c1d246041c1c40a802d185562114a040c0040c507130711820f40568402071036003582c0d8080c0d45030704100c0031482c056009008582010f816a4408010090400d1035580140b581c03034041d00442d449240c0d204800c0703880d04012540100940360540c0814104d0800b9009003a15030301080c281d455481c25441d2551079600240c0c015074003684a60b60410075140e080c4901c0064401518040c4015030503d400c0954624005100a202a100701c00b201d904a20901c140300c098500205142e1b503640050501501801694059501c00d000703d00c000103081c0b404c40a202c0840d403080020180a600e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 276819811 1250 276818561 276818587
    0xc010216060311070804270e07030b0a15120308010504050c04170c1507030e030303090c060706022a010510060f05070219060513120b2214030c010c030203010308 71
    0x15103c45160f8020503c80f120014840d800600702604180142e10000d6215420802c04021080d000c040850700d810095600030102060382001d99420400e000d14030b4840ca4110001009040c004030000c003581403010071a0301029060700c0c5407901030707034420220b079881d00200300490360709840c180d080880820040201c084140b0b850380882c000c0d00306440d1021003272400720320182c02000782e501010100003003000400d42c00140f1050412410b8001750306600e03101007029a1007082d000e45500c04c4101107248800c009058040310540381001d0b602e8210380300c2400401001c90741015618065500f0b02d4001000b610881c1c0c00076003182c1036a030b1150f1150000440964440e40800001e90700101c0c90107082201102c9001050f004041070b5441598911581c0d202e50f0354100641c0210b0b4064616142c0840403645040015800100212600880c071556140500304081b41c0b04000740701a034003e044c4018410080081e10000034000024051755078100d90807401c0b1700c4240401840b080081c00100d8804070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 276821061 1250 276819811 276819821
    0xa06050c07030b060f04090b060307170309040b0a08010c020615191e0806010f051c0305030a0506060706090506060f04060501140d2a02011503080702130b04020706020702030c0102160603 82
    0x901620014003485d0583c0841d09445c8840703c00c0d00e03103401d01c0044c04030a043c01c200d8080208103083e0000d0004665550040e16442041115885540c585103010481d41d200842940105883c00080082540d06103000e92a02001ca601c0c41d000301c0400c40c2542035041c001c00c031000b003000640c9031800c603e08000340b040d0001420700070b6805004520318082003070007040090901800da0401c1800300103280408005414074040c0c80601c01c0e20048400c10b0001e074204003502d03040b650b80c0c1000f058070b80c0c071440403c06a00a040010b8610b6040c600b111091000c00704800303000d04015942200001d802c50140000c1d10440d100e00b500040e5800c8549a419014001600c3d00307000480011510400c61207041400ca00d0780b04515903181200c1c501029070365024801c50036001018807881c90041c0c59034885200314011948003030300600020451002104a41c3d00211200c0c10040c0111f441e000c0303a00380280213420a403402c82c001e100c1c5204030003080d8000149a40c8000141c113400c5c1949003091401c4000d80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 276822311 1250 276821061 276821071
    0x50106080a05062d0a0f171606030c021009030e040e0106080a030e04061d190b0603010b340c08010b06161106040321080115030e030d14060a06050c07030b 68
    0x421064a16804e50ba15481c08000800104c55050045070808041d00b580083c04524a0b000c1d81c0110048454403080c0e80200d800c5800c18100040c0a8009a405908140480382c05907011840c144101041541003100415401000c1e1410081d49502c0e442d002c0c02c0700e825000e0403200c1c0d07000071000070000c2d10500b2051820403010f000410102e0340d07074041c1044514100c94040c503040c200d8042218020350702203000d4041c413900d8400e0000c2e41611010070b103030340710600440124440000d0745000b04031941941350003a025080300d82c01c6400107140d0303280701082030000848510030320840000f03518030140680c41c0c091034000d0006152004c00024038000b000282d60032a00010075100c0448d46954803005080218001c54021180248050a03101481c3c070044007503041c08a40c1005000300e01500720039228006d0b55043c0042c00e6000e50440c640b8501850300840c400b1750606103000d40d200c0c1d14901c418045d441c10f17110010a9520303804191494050403040c80951750040c0d604102148800010503080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 276823561 1250 276822311 276822379
    0xb060d0b01030f020d020702011106010e0103080c0f071e06180e090a080a0c0b060d030c021009050a090b10050f07020906130c09050f0a03030c080c0c0a030501050106080a0506 77
    0x90405503c141c080c1d8125009090308103601092803429940c100f02a068070200c040d015045640c1400400c8040090602024090160200703030740c1504802013000c6505203103404200e400890b40c0d140d400c50580c1214603800c010f900211800225140907090300c0003031921580f1150001c0e810080380b0104884c0003030000c1100d200300101100030412580040591082c5030ba54407074150550306004c0341008020303101900840700e02103204042940711443d100c0301a41101c925480408880c2e00300c840d040180c1203d6805510280000303591461907001c03004460781995007856074075140d04255003500030a242c080340d408003005940e00500d00321548941c00f0341c000300481c0d01c858842d0750600c111511a6582808034001000c14801c03880c1421109885940481e919442c0c1d905640d002803645c01001c1c00240f4640e8007007000c0c4040c2009200e44500e2040280181d00304039501d04010303000e04400c0c456000860b04d00d10204031215042e000d503d12030440a003491140c1d4031040c140346040518940d0900314 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 276824811 1250 276823561 276823571
    0x306190509010b1218150601090503011107020316051525110a050303040b160c051018050301051311040b04051f090207110d050313090f0b040b060d0b0103 68
    0x34554410301c000b0b01030455070107541c0c2c0740e143c014111413002d40d01030842c0b038001c542e0880c4d403400554009004150607140c0080ca01ca9900e64100503a00a0301c560001030b419401c100202c890a940c40e405000064000c80480f074040c1e085565030b440500aa0040035003151903005000c000700c1c107880c020003852030b03080b004090123240c042c1c41400141003028125070340c040c5c840840d03090f0b24100d030008025041c201e01640c50103203000e584c5000d40c0310340600c0200081030355510406005a0300030080040c2006440c92207420030070f4000400e21403018050900010080c1d40114880c18140302e010320911480c0190380c5051025100c2d4a14400c504c070036036502c0358841c001c0d04104e40300c502600f030007881488a94410001140d603440c5804d05541c10044806106000c850003041e590403100f6901001a1040140401c180c21301601307510031806070411940c500d10b000140200540d201401403240e0744410010000000b0400054906500a0310ba100310180035085101c41c9a5014100300f40c014100026 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 276826061 1250 276824811 276824819
    0x270f010516060c03020c0c1e011b05030d0903080a09031b050f0a0c15030510050409080f0a0206070e060705060a1104030c09020307081f0b03040f080c07140406030305030619 76
    0x1043e26124150600002d030040b80d00032217080704014109201c541190302803441482180019280010307404520304200744000b04051b0210300f887d0700202c85421000784d07643e4602c1a0201005071902500803400140480d0009a00141a1040e503800a81c16580d02100c00c1107491a0191070716605030568860151105200a038441041420301e400d100300c10942c4560700c1e18140c0801c0280144102d010305017070900700504948100d00d000140d40088400180c0c050650901050b1401601040b10b5030040001c0d00128194000a44610880c00c56481144805101e0184551030140300801840b41c2d10100205050b8030003500038003d03200d00701000e1800e2503507a88460019041c0da07804220181da001043c0030406901071182503104144000d1060004c15405800e030a03809030740300712010400048081410401d1560546d4000340e00b0080ea00c0d12540c1c3c400580361254903622900c0100b03820007640b8091800c2a004990459070152130b0b260a558a030018131690062545c640305401d1541c4501007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 276827311 1250 276826061 276826073
    0xb0f0703030903052b360503071e05010b15091018031a09010c0c110604030c090e0706021b1903080324030c0f06090f100302270f010516 60
    0x4540060309017443c4100d2400700760224201c944d203600d403200b2400c0400d0410504465030300c50043e0300110514400d503841150034600d0850068480c000c00b9401801010100c088690954100c5180128001c011190208041040200382080313200c0c500071090204000610344074607985100000344c03c07d001c030320f90b4010050b0300220003500100d94069543c948000c1ca01c20380e000140c2c1c0300d04070740b008200018640e000580309110b501002402c412100411715960740340c044c203580007183e010780a049141c0c1c4540d039000107040758214000440c495800b0000d43c843c03000420445080e80c6c04010700d08418080c1c188050940c80380e00c00e0b12010820b460010004594030015441194054802c0544400c2c03040710b0312000300000c0040d4480c2c0d112515001d2159104c0c90a4100722500722001c1d9510b04514002c1800c541a03400410391118941045103101c1e90160000c0001804072682581300000000c003682264404807601c1e50082c11014610701d0300d5000790020030361042100d000f64800031641d40c400c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 276828561 1250 276827311 276827347
    0x110307060507060612050c060307030f09150513030503011502071502030c1b090c091c0b01061b080409110c010504050c0901080a050607141308010b01090b0f070303090305 75
    0xc000050800501d070000d01c0b40b1841584043e154090020704528902c0d1100360b9901c4d1280903c6100c2c1c0b03070000104074800e02035400300b0040c0440d4030051040300740340d04202440e0ba400c038078944003142c28007000800c88c8502c1c00c11000401d83c9900c46c9819a42401a00000c0c26800c0415038190b22840c58089075001040c0140306007000300390b0085940d100c521240302c0c20001c207136948a42c0640003c0305601d040d0354a107022644003105034802c5450b2882c000c0012042008117a041e00c2000e40140700c0c0c4103101d142400716041e5511515100b191164207601000b00c2c4040e2103029245500510060220700c3c15504409082d050321a0030b241045200f000f0a42190020390f0104d9490303010300303103480c0181004a0350500400e503107000f0b401618200e07140e2a455100040c010010043d4605546110751222030a4070a07248102408001964844103100c2c0205518030b90b19012440940c000290f107254141201d60903202c4c084a00e0400c4c0c0e01da981a0043c20062004030b0071f2010512402424a4404600d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 276829811 1250 276828561 276828569
    0x30105041b0e0106020c0402071e140f031806090a03020a09050603010b1e010305190f1a0d0503070803040c09110d1104060c020609120f07170a030912110307 69
    0x41c5a0303a2030004003400c0c00e2280d007940310301044840070004200322500481d4980d48804203580150b0b4034a00da1404441440c5681ea0741c101d03450050301c00700140700a0201c480c4100d000e82040354002c0003112501607aa01402c410701480300c6142810014900300a4090701080a01508030003440b0b03100d0307001805802c040d41111409540c0d43d01041090300c2d0074042d00b01c1242007518003071042c1e0055072910513101503001c1041c3c14541c1711804178803c40b01e10703003031007551003800c03801040920040241d840c068003a040f16050781c0e225007080200e01c0d180c4007032101a000d600030001c5240000c6a602d40e0200e800c0200181d0300c100c6588400a04500d99008040c41e24000004260f42c50210ae0641c800708c0c0c400c8145400481e80500051081c2030f00301d00c01207101d6404643e031035140d00c060030014007051064101c8000d40d01030003440d080c80e071000007100000c0d103603880c00c420b10790034080003200c0c1d9808800c40003400050240c102080040340c5168094103160103010754180c80114440401c0c9040200d501c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 276831061 1250 276829811 276829823
    0xc03010203091b01030b060304021002070e1305060c12071b060c2105010302030c0f0f0301020406020106060f08070203120403051b061e0c0d020c07032a0e0702120a0e03010504 77
    0x41810784496038080e034155403202424108426100d1b4408101c080c0801800207003d0201c074506040d8881c001c21944000341070b030162010040c640142152240d21030200201c1c0d891040c40081784a050703134007040d83c00454a18001584d0396581c05411600d01546100c0440c00003440c01000f40413400034001c0840452a584070742d240503a006034040c6442e005590580c00c02031500d401800181c0c1c003c5003250042c102103806a60184010000955082d0440302ca03943c598400180024400e8040d001181122280d494440d100000c0343c5003590044400c40c2c90744d0060b007003049220300101840e400f554105000340360071820140c0c2000f0b1800c80f554200003501403944031204100d0904032616441411801d01e030303d086a5818201d41031011800342c220818011074001c0340400c0a41e0b4100040002140c000d0201810417103090049100555082c5203480c80b100c0d40303440450b484146035841030240c81290700034074540890080c0300100d50011442c40c07042107010610f140550340c0901501d80142d01410b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 276832311 1250 276831061 276831073
    0xa0501020424020d14091e0f011b061a0315010f090c0806210d050d0c05040806060f060c0304080106051e01211d0307020f0906030d030e0c0301020309 66
    0x40e0030014211840701c0c400301c448116100c07007501a80c0130503003000089042c01d0011800300f10301c01c0483e80e40151141250000100d0104846003511500003031119001526228004500300340111a158104007003210688251180c0d800058502d612001101000305200009a00035000190a050803580501710f05402e180060040c24a03c0c5400b40091500100401c2001c040d001e000d442c001700201600c0c40b50001748881c165036010b82591035110283d42007520303008c1c2040840178056401100c101403895251141c05001a8001d9003100c050319403090050903542d98490400c4891014040e6541c0c215100384540e4031464000c0001d131002d061101e0010884900384810701c0b455010000515001030f140310f150804903600548800f00303a8543e80b0281c8100f40d0000c580e00d014000755686110b6405240380750031411500071004d840c1c4648204c0b42214901142402c2000030101a0341541e450303000842c480c40098000d038031802682003000c06445a00894400003822130300100c4070014560856 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 276833561 1250 276832311 276832319
    0x4050105090c0a031b05120312011d01180f020a0c110301230403180303050d0e010501080c010315050a060806120f03030103110d0b01090e0d030605060a0305060d050a05010204 77
    0xa0150a5012000c4070040010b5000c0c640018211520740c440501404032411108004050852030b000140c240500880d0342c0c1c18021080c96620341c84602c0d04841082400000b04200ca04d2414849003000c01120302a03503a421b1101180c80300041200201310305a480c011711900244c14000b0700401c0040c1e4a601920310031609001f610030311914240e5200307074903290b03500002c40c1ea05003c010b9030b04001c04189060b9500e510f010350714000d03140814522001400320000400d5408002841c0c2c00000030803d001c00c107443c1c9034480c00d840342070290f201e007074000314041c074040d51080d4030240c803d100910b940011327507603180e02040030b512944c1c001c0b400044080702001442d052400c0f480010300c180500401070b84200380440b40e100c0c001800002c194508480704105942d85084481311f401f03402800f500c0855079030b200140c1c01082003003c03024840c0182c228180c0510300a03c0341c00200c80014040600e03058424404400420f401024154031145048610307010801c00c01c0307021400307446080016516820 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 276834811 1250 276833561 276833563
    0x20d0518090103050f150c160f050f160603150303030c12060e090609030304032f0d0201060911040b030c070c1a07050709110a030c090803160c06050f03040b04031707080405 76
    0x24286c0b01010040000b0500405541c01c1d0110307501c4442c0100c5c40400c07042145081044003a007410080d1a0388203031110390100381700c04146210140b021107000043d03142c2e1030310154260703502c001d605e90090102c3c00b000c001003802500b22129050315031400500010b1f02c02d00c8041280c003260403141c20104650208884440c0400070a50001d40b00340082d41545001e5900914101e40b40c2d08588010310081005010401011092140710040109030340c0c00d076a003924001d00070121407190205140c149001d521924003071104650a40e800ca680461950359901c0302054242d002d08030481c0c820007a00342c000b4000000c290b00d00013030042069226920389050501d42d1500750145c005190fa50701d0007500585ca0008a4201d075103071001c40c05c000c9025a416002900d01500da0f92000304039003c0010081c2c4028220402c10340300314410803441da405601c40404480c40c1c066204020308040e000c00c00f01e008607900b1603034103600501c02d15224110003e49081e0b18505c08081e82c6010205000c20140010420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 276836061 1250 276834811 276834823
    0xc12181215111216050d0e010b01120507090608091603032105150108040501090b0c0a08010b0f04060c17070308040605060405040b0a0906060305030c06012103020d0518090103050f 79
    0x281846280381403812151100c10b00301c1000d0485407440711202004d22009002e417003540c100251050003008000c1040c0125130203800c1501e200b0b800180d41c251701c050740c2c801c54130856000d42000d40d21401001d040c140191485440942100c0c29440f0b000b117083e0402e07a00d02402000780d8400d13500c0c010001d810a0a039668401002080c560003401c0404219a9414000c05031424000910780b00c1d920741c84a041c0303240106a1000041e10401f00708040185040d1240d00518100700240d85040c0c1e13503a070307410f06c4031010701407042098204002008100b0000b882603040c0c0c00c0c5240642c0e54a00d801c0d00d41900403140d584004070841c00b0904000800040c08440d00c121603100e902034409210380e21b088d680342d101c528001006450b8159584402a0a0000b980e21045c055a80801107958070143d20080980da00001d200704401c0c0b149521600054404403140c03007144170b5064004000071121454141c0701030f0892901000d122100513402d034050341d10070168034021400790000e4629040b401c004241025 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 276837311 1250 276836061 276836081
    0x16031106091c14070203120301060f030506100e01050c010c02071406070201021f0e01020705010504060b1e13020d02130603050a1e090503070b0405010605010f0c12181215 75
    0x30b000b07100c2000250a03040390189a04829281c855140388900424000c58003890201070f416200e61003650a141c1c00ca6401181620380c075807122154601c12000c1102076600c101c44041d080419603840d20049802116000d440e0401410010b0a0881e00100360b400c50710000c02200043c1e202d0f2004101c800382000c01d03034441da2400d075031140c035088090300041d41c0d441c900d0154254941c000c1c100b07401c0380c20b515030101c0340d90265800250340c0c414460400901270001907a00380c0701c95141c014829000c4c0b401802494402e1211111060843c400000300704003005a202c04900041d02001151114202c030b100500d50320030304440c00d03103a66041410040468400401d0405d4040c1741005200c81d03418801c240c802d190b00300301d034082101500752500074118001c100c00103101448902c01c2c441000710640002c400c4e01c038281da44006488145100701c0d54a060008003600d400c0e0104150191a80f088640c0680d1005112208607000e6680e21440d1880c1c284410a403050007240c62241c507004a5801920112 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 276838561 1250 276837311 276837313
    0x170a1511070606030c06050a020d0f03110a09050f03061605091c050604030f0813140106030c0e15090105060702040b0f130c03050604020316231605010e0f07090902061603110609 78
    0x10323111a501960f80e0038900001d400b0f1094000740140341720320036085100b03591804004030751101c1900e600500340100601410f4410004007070f190409060005800d0b00c241e0b007030038a40c1546040c140d01030710151300804425400c0800c4640c00030100a44807030324014140700360002e1000b0314140c1001004040744032210402c000310700c018011a0760086903d02c0585800070300f600f90202c80c5044060042119a00061080344801800540880220762041c822449a003c044d00c0420503030030000c10450902409502010510061025042c6544010700c4050060f08138510001440000b802443c1007038080b01881d52581c590900c907940c10301070140c100005481c15821410700021515000074044882c00410410350b1940705000c0d1001e04c50564481c203200e049946848501005603000080344c400c0c3d41c5507007414601d40042000180d001c031800120000352031181c5c149080e09020b05001002030340d002d042070101d50201c094021300e029440d482525040346c01007007401e040b418070310001c0900d00e032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 276839811 1250 276838561 276838567
    0x40b070806090423031201120c0f0305060a050a0216050115060806090115051917011d19060515030702070f0303081f0b1909170a1511070606030c0605 66
    0x70031014241c0040043e101d40b00c1e41c804072130740e0610320314044c8640c0b48a80440c075000000341450100580e40d04940600b00c004e030341c10389440c801160545940710082060340520009600341d50180d0000e03030040c200c00c40140c035000e0001588905c05035a049d0aa506035510203a40300a04500c41081c0300038800d5003820f80303040ca0044009041c440052180e007600d000306500b1591100d02c6082104c8140c0034100d40540c2c074800100c002410300200740200366980c2182000483d071000154010a032a203c4030040f09413603564a15051a503444600700e6003c0b250721404041200e556650749501c40c20030011581e616442c00700780080c0f0346481640012035170520442d00b8004a07a1240e841c07503002e070303102c810854800508078a4403501d00d126840356911100110305042c50000401e14100d242501e40c1c1c400c0303401e644580108181c0c4602c440c01007201e0780418004000210000394802604202040c00916001811043c84860703210071021212559600c100b4802c0100122018001e840b1034541282 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 276841061 1250 276839811 276839813
    0x30c030601120f1211011112070e03011b0c050c10120c1803060903031a01090e0a02090a080304060201060b070c06031a03010e0102091c1208130605040b0708060904 72
    0x344801060007546055145041c04205100440d031010000f203500055a00301d0b0319040b0760060641d405001005400c0d4200803030802c2c65641001030342c2c081d900540211800ea195010f0942d041141c0e50071f80ca070155281c1406040510401c194080361070640d46900c003c00741149001c600b0407000500092051440044070000700d503200d2988074400c0205c42c4005164070460001703a90308440e0154181c2017015200c004020400d054011419080c882d84080c04034103100c4050380030311440b910300a800956000342c01c100700516509100c0e0081c038240c000518005140020605d030038090b030010701c003944c0002400c03c00c0d164240f24110085c015580c00c0c50810307490ba6514415075145104080406880b5142c0d07084040220840d0041c42d84024020000b82042c0604c490103500409002da00c00d050b100c0c10100d0140c2400d0901c1c03481544489014207455407240142d40e070450140000a10169112038000065180d00c1000d00403405800d00507660300c0c0c00c40380109000d2008100602405d00841440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 276842311 1250 276841061 276841063
    0x10f120c030b0f04090c03080d0609111909050f060d020c0303010b0901180b0702060a030b03420705161202060109060b07050709050603030d090b01051503160804020a05131a030c03 79
    0x1101fa00d5208c1d0005a40740c16151442c0041c203801d401c0303a40258a80040c02c0303a0310810000a2150340b208407403904841c0da00f008261162115885243d400c03035880c00003001285400c2c80181000c15001b24014242542e45aa0347e265400c01d0302700c610081d60024034007903150f800c02410440d00003800c031445925400d1200144290003038001c028040d1101040c040c001e01c0c06a0020314800001030203c036a1120288525101c0010b00b05240c00320b5006861869071001e00403042040d1800840c1c0a1166034607044802c03030f5564010020032800f0844440c000380015030300072403040101c00c01d80c0103040c59410400300d0400c49513180e01403420b290080110000045000c00e0480440c2e0034014001290340d1103201003804c5220b820501055580f42a4020040080e1510058180c0e201914544041c1d490b4405407411403006070b80340d115200d1111003541910341b140e82d92641c0320b440a0b104d43e1110f5510030218880002840a86020a442c0d40c648155800c00105000007898114000c1800010010202e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 276843561 1250 276842311 276842333
    0x203070b0a050403030c240504060506032116020a060801080d05070210270b070b01080109050a060b010212030906150402041a0f070b07080a0c02061005010f120c030b0f0409 76
    0xd01b440940e02c000703018070201e01888039840b00341040114081068500450003450115412200b85d403419010403ca4200003500c0d40128003914903161014141540d1107003660001c020081c8140044507c840050b203030108403000030482d58803400c4165042c0034101c0d040c070f00700d4104481004010700025016035176206a13041c0004903420111102c052a030000a070300055000c4070003001c0070f900c4000a8210508000344103440c000c4142c48516629505054240c030240c0c2c0b00600540d0040000c00c0c04521b41d82e01205460340c1c14011607680c08154038400440d0307001100c40042941020003042181c030041c104118841e0000c440441c0341504009401d04940c034206410402810302040103400c124016040352002500000d000e01705140200c4001d19845d4100c8900400350b0910451000d118000660f050180503107034012650a400d10004545030803903102180f0400004002c02c0841d01c041d442030502907c80d41c0d5000c94004032503014001401c0f0104500750007907103001c9011000c50604401c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 276844811 1250 276843561 276843563
    0x8060c04170f03131d061f051c0e0f1f0c0905040f0b1011070501030905160905182a0310060803070b0c1327090f0203070b0a050403 58
    0x1050440620421890b2809412400b03904451000041c5004200c86244c0c003c0e00311aa001215660800210001d550850050360802c0c3c000140c1075414603003101090b50750743e010055241a0741025085074804215044640001070403a03030f1201084401201407000c49040010b880040c1016003c03002c0349840402c101111419080e61000340b0950b06108030141001010010300030300c124041900700a0061a1061304513214500d00c1c0d0000e9501c60040c000b0b49180070400e0050100c280c641380c015800b4010f865001c81e064040d20aa040d03444030041c1491002d081001d0b00010546440d120b07030080613020f07404141d1260301102c45400303011904940b251815028600d008229581b000c0803900c0d148000a00391900d83c1005000301e04040c000020300411405848a2200c41d103644448808900c07600000c070101c600101c0c0d052003005261105599101e4148a0418103507401542101c00c4552400b000c07038010180c07140c80000e62804004000c09415040e807a01c0c54404084c60243c82c911032440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 276846061 1250 276844811 276844829
    0x130207080417030c120a0207050603090d0e0a06090e04060f0e0c0f54070e04090b040f1511120a0e07060c020103060b1b1501080d0305040804080d080702060108060c04 73
    0x36902e1b54452081c894100103040140c8060340b681410741025449899622010000440c2c22940e0407851074102000c1e0200c45d2503440d0214078078100b05000b61141001042030314400d40300c030403c0031051498822a0030808000c806845c040d10f401c42008200499442628401e1000c503240b1011592000302991181340981c022040e071518007485080034860840c1c610040c0c2200000458403850700d0071906100c0e034203903500d800d14001044104411200d1509010f0200c0340d071a00080c0c000352a55007210305050103201403441664800d000c860550384110803051300c04101180006620743c5519425030084603444042c028000300984c02c5541d0801c61050800700404010740d00c065901951004024019101e10683d4895013550709000030351601010000386e10a01020f504044e0a4110480c140d81442d0041e140441207600b0490280a002c0d005071079901c001c000009a400c420440300d02842032507140c02501785002407020381014030503402200035030449401c00c680700820307008917001e64144807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 276847311 1250 276846061 276846067
    0x18020304050705120604110604030f080327030a0210050c0708030c0706150303020606030a03081603020408012408010b0607060509030c010c1e090b03010306020702130207080417030c12 81
    0x1c14035600e06011548080e80242c0c0600c01401c11420104025200c2c5014003074076894002400d090088078403e51001070640181e0045085c00650744d40003c50b040340c00c1403001c2601010a401244a0041109d00d0304015800041e050082e183c0600c600d50500e451208104058039019102c80360521400000802403032000000034504800070054904040d04084100700780030502c1c7e040008860240000e50140c3b28100c0081c1c0c181ca00000e04203005585940d034072503a912000307446407415100c48818000d01d1313000e00c07000c41c403030034240710b4404c0c01517a284075103040158400c001e05150b184d54118201590414204405030384801040f06c030041c0d07101d18000385540c0c620300524203500490044485a50814440b4000309900c00c001170b504542c003141e511078540c5080825204114144501e007101e540c20710040021601541c042c0544500107031204105940c0c0c5400a81241d002c41012144520080744c240720b0016801c08800850001100840ca072458104205554400d10308880343e500340c0c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 276848561 1250 276847311 276847313
    0x70f02150403080d0c171005010807020c030a060f05010f1505090a0e13020102060a020702010c123c050703020c0d05070801110c0d090f06030f1401090b040b030718020304 75
    0x1101107a0046800030a202d4030b4480710a82400544482c9240f040001c600402488040100640441c007660026044500c01460400192240b0728018100015401039510540140d1010700c840d14440380300b440300045100800c2006000c59006030800d8126410034241400785120480000d4034041150070645d4075120108000355420300d80b500240074040c0300005100b1041b240441c0319000510036000c0d031300075a41c0e401e0713020200c1c0103842010b0300044c090750310607010521291020503078031400d191460b0b681a410300b00401d5240e5140c40031726140815168001140702c1840415110506031502c0c500e424010340b4002c1d03a03110301458203803107000350001c180b0070014200281ca005003a00002404100007801c011061074000f00303040450780c09803149c0708504911400c128000e588071120300b20300c1142454002c500500f2540c0c02d12000964510800510062650240d03000b0103c0c441c010401091503804d11040d105e00722a9070b07011790303c40c1c00140440764020003108103002d800d1000680300e95035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 276849811 1250 276848561 276848599
    0x3080603070b4803091003020903030901050c0f07030f15020301060801090506010905030d09091b021504050a020301060f03030f030507050a030b06070c0f0515040305100f0e1002030a11070f02 84
    0x80b003c41411200c0255007003944070f1030080081c1115003402c80b4420250b207100354095050b03108440d600f9606420800c01c00d5059030290020f004c90031484402c9810464002a00518000f0907800a480400300c1038a0030040040c8500d18143c04500752074150f0455140000203003c010040c001c1c0c0d40034546410008255034418529400144001012109020480c520251140d04280100c1c6801402c00b01d14139114220300d2100d40c0ca01540390300500c0307100d0f05001303258100130700500200c50078002d8600c8500581d4090098501800300b00355102111891407070007409031500b000405080c517060600700140c058000302a100728040e142001324400c1a41800600320f0701c0390910080640e20180390100c0d10b409105080429640c05507003180c4889074031060700d0020b0050b448001c1c041c0d4004040e10018014541100c541c0040444c0007003242441d2420f0a400c142419100c1070301213502200f0480c01c4505c0d8000d40f041e84000400312803a119071615001c00d16582007030042e0007a00f00b0081210b1040c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 276851061 1250 276849811 276849907
    0x3020c0306071107050406030b040b040c0f090f050603011416020307060509071508241305040b04051b030c041d0706050a0801050a051804080405040903080603070b 72
    0x2900a003500c03003525050307001401c015109403c4048070b21680001040b981040e106001c2602e8004502040300d5455513036012044900510883da41d041d688400909003003450404006051a00004200040380c05e000800f120001000d203403280e03041407080500c207034110740b00c60f4008098544046c00d410100c0c0c0141d2540c4a405030003450a882c1200304203c3c5c00c004564101519600c00100c1e0204102c01401c840c2540240c90b240e080e8030300114182c070400f0040d0031320141a00040e24682071011412181c2c803c481080f101a10030903100c41c108403c1000038040c001215543d42c007004013240c1c2210110382d03545885481c050080b90f07201a02249900800501600c520164080f074482c45c1c6c992a0050240e00f01080c040049241d44c400400e503450b24223400c01c161540500440507611041045100b000d20291080e520050704110100319074455016076901940207403218212420a8020f1500d01035a55000c080e103d841400341c11480c603222080c003000d0004d0921003c1ca40c00040000c0c1c0d000c45 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 276852311 1250 276851061 276851083
    0x71101030e0f060411100503010909050c271f0302012706050408070f050d0303020d060810150801051302240304060f1503081b031308030403020307060e100c0302 71
    0x84030720740c01000b241c407000400c80e100d00c1c4148410600984841e061121017044100b85001149061006108105503135004c100a02d00400445108100b0507010074aa0b0303a00d00c07002e4507a00d40d072420031800f5518258110350040c42d0b1114a0f041e000e012046000000000d002c028100a599140c00d041118660442c0182210000318212030a6032188081c0180c1c2c071070301c43c42c42207020388903000816140758440d40c0101c0e4006800034418030141d42e0224029440450840005991088082028181080303405000801484000b031002840c5040015160840e400740d07055a0511082045041c40c026007030800c90b03810303900350084040310701034017145407403000d452404100e001c402c010170301c207030f9422200e003031023000f41c08015461401116051200c424000030781089020421220403a04203894004850300359415282002a650907a40c0c3c0c4141a80c040c1c05540d0021505100b5440d007031145400800072030822052200d40040414440c00203150f20702d0602a50344180c2e02494000e0001fa1000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 276853561 1250 276852311 276852313
    0x216080c061303080c0c100c0c0308070807150b040e010902031e10021801030f0b0108040818030105011503230105220c11011d060412110a0b0604050714071101030e 72
    0x41017a040403036525442590018401d881400c036030300525005210b400011034000c0184242e082c1181c403403221541c00054125a004c10411039080481c0c140255804254070010380070030702c41e003414100026103122547c6901603034503008030100181c0c1c00051103080b058070b643c5141494040c04507032034100040706540307881c1c45000240880c1c0c03001c0d03001c080b0301710001b00340c908206c2c40c102006001c0c11a0300645116011480e520049800f082c01326018108000f5030001162444044901281c213440082c1d01c801503400624542162458150080c0c3c61b81680c44110400c1088e0802030f1000303401410300c00d02d4001d59001c16940201c0c0d09052603608100428282801713054128075000b002c840705818101c0880d480c14078035034014480c00d00c008045001c0300004100d582c455442d54440d150110000701c00f80030b145240da070b0320040180315030b0018500500203401c06241c42800c0c40309450b13004100808000107801d64205101c00c031010f8038036680d0006001c03e4200c001a00590040c85040190002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 276854811 1250 276853561 276853567
    0x16020406050a0308031b040e13060209030a0c051f050a0e0a050a120512031501110c030601120b060607120813150606020106080d0206161209080a0216080c06130308 72
    0x600c440c040046000c6c10001407980340454104034109054000d41c0100d1502c8421140441c031a01180c2ca02e000ca994040e050040ca040d8203080017072300e40300140300110b4405042d420204a00e00d4a07c180c2c0424901c0c0000d4100d208d04035040040ca54460780d00d0b040140440b01500300035644078008200080c000c0a408980800c0c0c46164542000c1c0d45208222a903100d40c00b10f0040511500040e00d0203940b07950302d095500d0350ad1a0041d560344052032a10080b0b441b034403480c03110507078042182d00e00074141081c1089401e0003078103040c240c420300100030a0080768108484400605903003401c0c2030a02c15031038410740d40d40320120025081d0f814060064a00c40c0c88501000020720540d11140484030a50001c00003103a8642000d9200c0d91103008003000f40c1c2040c00064030004505070300c0c44041500385820a031742003001d440b12044507000907042d12141c0c4040707240e8039095010081e00312200032482480b144207140c240c40c103544611446480d070243d0800301d04603d4026100365840017541d400b0801c0b80d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 276856061 1250 276854811 276854813
    0x5030a090b0112120e1c05010e030d0903120b0607060f0e060702010f0605030714090606071b0e0711121b0a0b0702011805070603020f0d021602030f1216020406050a03 73
    0x140510440f1040c0e880710444e542c9411298080d004044c080e00025024410004500031040e60040c49400c05844a540761a015011610140010110303903040c200c0c002510f00c1c040c1401003072090303042c0e5801c001c1446d12a400c4002d585044c2554160741d4000c41c0841c0808200c0190400b03032641c1c490300700541c8651024881c00c590107400c03444081d4902d402c00c112480d55171003055921451449822000000c11039884100d01300201c8050380b121001d40101c0c41c00b64030b540c520700711180ca09146280d0b4002c41c3c3d02400141a1000f00d50b4202500d80b4001321102204104241c0301c5800044244204500007040000061062401d9003140700300070a4601004c1ca50901d180825401c0702c140005510300a40309506046030032b803000310990001c00400015041c402c041d8002d40c03040070700c00740c40b010510021450072414001402411540e203980c64030301400348149407400c0800c560035016500704070040c600540e000304c02e454805800300c00c0320024045030300201c1e0040001e50000350f008550004040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 276857311 1250 276856061 276856079
    0x4090c092409050f0303120106030b03120903060a0e19080424020d0e210a021002030f070f0f02030a030f0906090b1603031104120212071505030a090b01 67
    0x10080320141c840c00e10345810006035080c10814052548004164142024000f0b414010764000311040040d086038031f8500c00300c25103e02c00c482684160002a140d4800862a04090000b100c0317164030b10700040e0800508000007915044010541c002da0740d0b44640910300c145003080b200100c2d001c0020746120200c0c040c20220121b0f8014090840b82d00049030f1050900380c1c0301020020035034901d9000d010340000d881c004072403e0515010603688440c0592910142d41d50064590541e00640d5006116205c59881488440d2942d400c900c01036400a0000b0128003038060100c0d280c040e0b100150b0f1140c0350007031500c00710710b600121020f905840388c0300701c0604141c0c1000d02500004001d8942a02069035200104c2d21070b00e035070051070940c000c1400300d440000d03924015149007511a04020619032494800c07404590820360148280110f21000a17040d400c00e0b1900d110740c4103801001e4508a27040040000c140d144120ba00384c200007000000405003050b40d0b0200304000d40c07100900401c0d580d01c110310 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 276858561 1250 276857311 276857327
    0x60c06060905010632040e07030b06030a0e0c030a0c1203050c0307230303042609041103100902030c03040b130609060525020705060c070902040b070c08121c0204090c 73
    0x7a640c0c500c49155181c0c4814403030002203440c001c05c2c0945040d003000c041c0055000c01070031000525072682842c400e69514035010318466004120006034003035404110600d4442c0c690905800782c5c122031040d0000c074200f040241e0075101b201104e40d0b0310b80c125140482d040d218141c01c00c00c15000c0402c0000c1084010b4118040800700000c1e590701d01c1020420142d120310082c1c0d00248918080244070035024008408690003000d451822414100d51401080a580a040304501c0e207030800030412209074200c02500019007140c040440c11880c247c41a07024511001e031025040000c1c40002499102001d416401e540c2d07403068007400fa404180c90458003620050310385c03501021512010030030800d03558804070301e40e0343d01c0e600400701e6600d84420700c94954043d018101c1740e4003400c1008510201d050005000903c0714400542d6242c81905140010300000e0b0050040c5400000700b0410100a120548000d480c50000c4016804001c5101c03400904c1141d0010002078103244c00203680903080104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 276859811 1250 276858561 276858587
    0x31e0203070e09060415180f0c080a030c02310203010306050601030c080402012a0305130603060506070602030a0b041b02010e07080d0804080403080c101b09060c060609050106 77
    0x1c0307448082c0c9464610110400c1107034202d00320782c0404000340c007040400050300f0300009500000101d599003509000d005407101c90701030798400001c8202c201000300c0d0803c82c20041001401a2080c11095903008015520100c00a8896641ca58556030b07008802624a0340c0000c2c03041c00c0442144091035541c01a4009200503114685420300140d481c2d4020700446c011070005540d104401d41d1203a00640d940362012514180d902c920310001b00308a00e07281d07540660cc0e8007a0700e42a850741c2281500d910484020f0700b0030020181820810006502c0d0001641d0f47c4c2a1f03c4680540c80303596820001c00100741c4c15482d0b65005062000b841d408601c41c1ea03604014407840d50080c044141c070b01c4040f90b0340d902240b00c1c200c3ca03a40406036031805207100e4040310350050711507402c0d2440c00795a0786801e1096007003051280e000350003071103d2000d072100d24401c4044408140c03040c151000c400460103031086c0401c1c86400184143c12021004110050348100050321051301d04101d10758640b0030081c041c0345c0f8401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 276861061 1250 276859811 276859813
    0x90801050105030309090c2a010207020901050a05060316021c08040b0604050f0601030b0d0602030f0f010e07140306041d010506040b03011e090f1403030a1407080109020c07031e0203 80
    0xc0080740508004c8201c400041000c0c0410146445a601c1c1c240142d02c02c800c481a880f8102c4080781c4900081007401c04500b010300005a103800440c010000c114a049c1d000070311480841004029a8a41ea81500d52002d403241c0d0044840340903440980c20802d140e00c4c00c3e014042d80040c282070440d04244181e0040f40038082c015429034400d4144401c580040e07074400c80c010b4a00f0001850381d8469005a858818045c1000b82d0040b100d5841c58141d170000d941100d5903d81c04010000b00c1c1c24914109801010321800c0e94115003881c88015040059104804546210010000340c858980360840c880710401c035842d001d514407600440500030141038454612075030411402c0c105515050040c02540d10040182c2031231100c1c03a9800303900800c11800d003200c0703100004518401080703030014500502404140a540d492030a105481c0466094814a40141503000240b100507940b0980035815105094401a0b8456406100318546103465100a0240144808401c4c0030010010150312251086e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 276862311 1250 276861061 276861071
    0x1e0b010c080a03060e180a080c0304030204020301090c020c03030712180b070507152d1b08040602010b0a03120c0c082a04020f16081902010c0806010216030318090c090801 75
    0x40b000c2581045406c1c0b800740d0303620400300b020100303c4c00c0c00241a25808030702107a26080e900d90120301079810981c03100070405e036102030310308140e03406018042c07000310210042d40ca01a001e03600c0c07258100340310a07070030304000c1714101c41540300c549110010080c0501e8030035203883d4401c03441e01981e1781c605d500958070740080d00d07500c0c40c2c501c1c1d0080ca002c0b410b00f191b5401c0081030803010480200040e031400c0d805801c00241042419a0680500046202d98082c03c4060b54450a0880190035a144800c405001c1c0342c1b014010004101080c203111049103041c070340761441c1c2c9818100101d845019400000c05070240c0703060305121419854000d22210122581c03101e114041c241080124001e410310b0791680740c000c118800f41d051205001b595120311070b072201814064a64a401366107040642624050f039034401c100090349030000c0c50b4035485502440107110415110004112100a91000030f007400042d403040c4c880910818542405001d040f10704101046080c840142089004d00c110342d0b59500c2c0c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 276863561 1250 276862311 276862321
    0xc010f060b09031e1011031f050904081605070f050120030301170109050d030507080a0606020d030e0c090c0307080901022b09020a0b0910031e0b010c080a03060e 71
    0x14000c0d1400c07002e0003009003440110746910701140015288800c0305030b004150110b8400300b59441400f02100d01c20501c0e5899107048007007017030342c01009864041d000103101010005a07980c180c1c0e440c2d10551192045445681010704510074030000700d0018800d004250021a50f03103917440e4817008941003642c4900c400c0c079910804a40303491040c00c14485681007040144492014480e070180418400000017a0701d401640354542088030700c140785c50000b910b90003804000c0b540100b0058110311141c4081180e50b04d01103010b9520340d40d542040b801d140d16180040c00580061240c402211000f600200c00d03231810707003c6c0345e541e5401102d20002180d50180411004403051098603407c5245241001012036486403100c9052545884905080e403100304000060b2a946103000040c004100c2243d1070700701100400090700c881c40d0111080500d40fa510850041401e1400044511406400919174941e81e004861500031041c010b800f00000141d9441d01c580c1c1603001c042120782401c0c01048a45407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 276864811 1250 276863561 276863579
    0x130e01020c010b0f131512080904050106110a03080c22060f170c0706020d1e0b060c03041206090c060f08010f140918100209030c03010903050301032004020c010f06 72
    0x2400030882d42201c1d400015000001c0668841084803041b8018850410f64980485043d00200001203409400100e00c152050400c0c0c0901ca0141c01503040020803030070a15266591800c0743c0d00017408200a80000c10800a20031341101c528070981009101d000e88405140503442d02d0785e20039800041d015034400d0101912515080324401f4035003051a00f42d84401801ca0713035507041080d082d100c0d2a42040280000c10251241c040c064507401406560048002c0e11031040f00c41424090b0301601c0e0070860404800b9010040307030250303041c03a504000f42d0822814640c000785284c460042c40307004d82d04c202040c51900b02d402440c0c0c00c1d0040e600c800850785c03200d160b200703000814070072030b01901c803800035100c410720b850040c441c1e00c00000500b0304404000500e540b45002c88000c07420468170350004204400d07007014442c0c1802d00406038002d05c04082c8598004096110510014010781225891610702c04824500c062403d80c000300199220040f0042150003440e4103422400014905500003c401c0c1f8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 276866061 1250 276864811 276864829
    0x405060d1401050f130b182401140d020d0b0315100b070305191701060e090907050f1002010f0204060306080c0f0f040c1b0c06080106020723130e01020c010b 69
    0x40060102e0320504400c01001024018180d11b40d584203201c01c1800e482802150303c030a1250405002d483c0907079803504c00001011044100007410012205c4e000fa2000021504803038081c3c50b4540300507a10214000402c005020280c10690316010300000f414803001100346140c080c01c11008688800340c1d0f510300c07040c22031240381c8004001c9002402440d171058030650003002d225049023441d81000540c2030000c100884241c000f4004107500300c6070002141009251a6071001400009082c05070501000440e800004034a0781c0c86803010502400342c05100b03400c1040e00455800d825500c441e200d11016000e0101030290950f00d2003501c140700340078900003801501c2680042c2c148441c0301c0901c0c041c44040c01a00403540b00340022200c0724030355946200c2c41e460040d40100d0803105081d0406100806800041c0c6c010021035010410602c041c0000705040342c00d5801c0b040601c1001d115002c0450003251450300d0700e44040b4901200c03507000c05819001408031a00100080107104955001c0143d480 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 276867311 1250 276866061 276866089
    0x13060c05120a0e030709061404060518040302030f1303020f030606010c0b060303070f050c0a05010c031b060b04051e0a1107061109060c0703060b0a1206110405060d140105 75
    0x1d8800407007100c24000800042c03042029924000188070007480c04a89411059448281b105642d113204004a4030034150300482e04200b1035046c0221843c10000500042418000740301c118415030120b03003098000c004942c010910448915102c0609900540c28110303d840242c4c000d61591800c6180c52402145540c03160700161900e482c00d00c116100c41c00704403070040146415100801c480c002080c08003100724a031500c54801090440414401d00c1405c03c06580030506005401000324001f07070f000071440400030003101a03100d03940d5a6041c241c000d0000b1242158100d0316110900022400d240d00b580d220b800800e01c401d40a40382c07500b0103030854803600990400480203115843c00900c00e50440010211010740450420b0034203000207035554400211a401030344603000c1001045031500528580800480343c0211013407507c4084000000140c1d80204981d98980c07500d041003a910080c1c0300030744400340a19441e4a000c641d0000100500381140412500c8400001114070f4a040d6040c210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 276868561 1250 276867311 276867313
    0xd1b021c0c03082e0906031505010f060c050106170f1b03070501110109051519090308040602090102070807081b09090c090a0207080310091b021903140403060213060c05 74
    0x19910714541e2490315403104d604841c2c0c100c0001505461064240b840070242c00e03428000100c481c82c1d86020400013442030064007181d4201401007240303c400304404012200b25003800c0200341220314181e4010290764101c4646043c0940440c00b030410005503e20802c1d050314100c48445002550300784c0030145050340e40303506a01086050125501c6243e5804500d08414000300340e814040e61060305014031702c52454078100c02c010030084040144020324400e05a181c0080040303030030603280100480001000600400d800155198580c0d1003001820014207007642511030868980030080c0e00c0e04c141c824111b0b120b02c0410001c00d40380c81c2086003640070342c1c480030080c00748921040c14400b0300d500c010314080c80190309215000206200100452003000d8261000e116681000001c030102c5001000740d0414040b08001d0054081d00080c1c1c04111884403032a120710b1046c1480d003101c00f92419649e4050340c4001050000030400160003603c0315811031054180f6103074076243c0c111003044240c8409030032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 276869811 1250 276868561 276868577
    0x9010509071211030c2206080112050a0b01060e0f151902160b1306020109020d110310020f091f080f060d050109030804030e04020711060d1b021c0c03 66
    0x44075000c0e402c12035110004080226440c0c0c0c0342501a101c07034008445280441c5c50001d04da504c5052010300180009503a44403d03128a03041c404000d0a80f4014000c0b901921415440101801020040c41c00d059502c8040c004131580c6681c0002c020014150364a40200030801203002d444c03030954505d65808040006081c14000103444d030100f403003005019202940207000442000020703003907031880541038081c4072a0341d4a040c01c1c0c1080c0e000351258421030031649030003a150b005036122004038814a03005510042e0302510340e00003a00b0202012200c4038500d03c0050032080c41d031070b080090f00310000d0440e86081120440c400795240d44c092601a180000c5128001422041042c8005038000c4d001400012801d0416070790b280c05c4a402e000c091700172400080401041540c0101451244407040d03c0950030800141c0c1c8410b5003011080500340301d01004900350041c0c0540c2e611914820340d503188984000a131080d0040c2d180c8414103203001500c403c2013188000540a00c05019040d0362603a51044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 276871061 1250 276869811 276869821
    0x70e0a0e120310170309030610120f020a0b0706051b03040b0c0304031b050a0c061b02011202070c0f140d030c1e02060310080c03070b04060c080d11090f09010509 71
    0xa49540300038040607075404100b901142441114250407144d000080c002c642e543e00b0325003058131f8420002e024602c0d0b012143c000b4071a040b0446416407003607034840c4d40c008141e069840003c84058841e0080e54941030701040320410311485030005405006007011105064002810601041c40201e80261101014a02182c8040c500c0c00c0110307846400391504c4403207000003c00da502181404c890a0b0341a40c4801110f82c184021125003100070041c500b070922031b2906488461001e01c1009501a060140c3c180d0010f4600040745c045880d5103511a000748081d0f61034180e0222a40014043d18040f840c4c401c0003152541040c0d1010100a6019202c40d05a10032646d40e8032480c03616180f4030001c40d59503400c00700058035018055070042c0d10054541d11914241010703503140005100e440c1e482030348943c0c010064903039030342c08075815118a40b4021640300d600342448061031044c43d600c541620310344030700700c0ac0c060014005000704140403500031441c96240f5041100c0340c0c03802c2c010903034002040400702da = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 276872311 1250 276871061 276871093
    0xa0302090a0603080403230a110d03170103080712080705040512210405121c2d090509071d011209060509010b0f090709050120060702070e0a0e 63
    0x15071081103201c010984030307240d9880f55801c0e08268802c40320061015420303403203103c0d94109200c49061941c0100b03100700442e01d607150340084107050540502d00300c11285007031510030702e800b0182d810f100710b04e0415541c2d45d10300038580e9400580d054035001c132100b040141280c4035101003030080b6415664141407a0404042045100803a040c1101d148120355900d90b03940c0c0c0403035030002812880107019469915140c24004281194034540038a5044650180303074203d8a02065000002249408261417214001c001040c0e2008020059a5504000348802440e071021020003680c0d019514000152103443c0140e03070940b100f0b04100c50a4110400580b1154450305408880b03440e008000b150200c004d40304d690899400743c0d0b940000c0d94483d00800354500304004402d00108041d01c0e01078442c9006040103050a1030fa00075141000542403a02c948910f5145011400c50610020f507011401c095101030341d195602d100d000c03804444131001031070440c5240314042c458504000940070180564040c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 276873561 1250 276872311 276872329
    0x10e07030c170414010c0908031b0106050307180b0a0513050604060f090504020307051c030309050709050f10050307150302090a0b040e011a09010f0804210c03110a020a0302 76
    0x4108100e0b104401d0340c80c2900580d00d07001c0d50041034050b010141c481403460a42c2c50201c0c0101c01d1100c40d507802c002252000040b07a070b480034407041e2000c0300074240202c20f000d04880da10643e8148112500415480e50300801440d1790710710342c01d080001c8215841030007003103641071040d143e00c003132228000d08501c50b0f0364004a0b404800107100103139403520b80c44200a044841d8000c044029690810402103040c200102d00c090241120006042104013424922810711440001d080541350002d850130000b04100001c00392403091b400744000e10707000b444000c0040044130081941d10070544000346606001c600a01074450b03840a80c2408081c248040d8080d500840d40300b0741103920300900207050f42d005005440070340681c54030342c8902d526111f0101540022180c1e8040300203010002d281c11a0b1300102c030300f03030703040a5410b007848240d42d9424041180180c0240c0031800c103040304c031200b04aa910180034108035211740c0b60704a540300000300c1d4603922030010200a40005400c0401c3c40580340019031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 276874811 1250 276873561 276873581
    0x509010c05070b0d0608062a160206120f0709050321040b0403030905010f05030105091305030c0114091207120309020d0606091a101e02010e151b03010e0703 69
    0x31581c00b507030b40f10b04050080c1e015041e220101a5100c005000e120010702a2a41100c510301c54200001c4484034401d1003041d440382030030602e040c00240c01d4144000c14284c0f14415400030300c000e407a440401803440c20b80780d08840150902d1413220001e008140905412000c1e00c4020300285040c0c50700480b081d4800c40515182140004103000024420103000000d00281d40300390b450b042000e14280001d0101d9000201d03400600c8403d100521440c0c17280068594003021b00528056261202e060035800d61160b0707022003669500307240c0c1c407640c81210703e0f210320302035000c1a003110b000a17aa0381241410b4041c80000816403002c2c00700c00781a0030b1203a00a1050680002c000ea0b004445d507a40d030340115103043d400b2000041e00c0b440c6408840e0440340310b910100d1800d8540d500707141904940103000840150f40300c55180000705142c60310074800d500c615811303840c2e14201d8901203250701e00d210207207100722241c3c4010410f90ba00303075884011450560b4101da821140407051510307004030a5020b0806c50700c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 276876061 1250 276874811 276874813
    0x52205070c0b0c0a03050f15010f050f120402010e03030703020c0405061809010c1e050304060917040603050609070302092b0b0708060102070509010506070b0c070203030a170a050105010509010c05 86
    0xc80380007160800a540b40540380b0f00e00241e54610324081d0180582c0c00040c440c0115400d000c0802421214664904262900034a090800c003200140107450034000c2000480340614041500701d50303101038001a43c09039000342c0b80c002080c1c1100e0300b0180d881c8034444004005030000c07800ea03600c3e814180c000c541c1002000701015400490003d2007414000d04503085620381c1c8d1146030510b03d10350000c5102a8105050301000300c159806d110191241c8401f900083c05c0907520b001040610080f0403032080020001d4141c5c0d030382c4a80c0c8a070f004001c0c05c001ea4403944644a003401260900c0d0180c4211a651440034050ba0701c10540450001d4488180042c4074040078000b54103d80052142c0101a10074140c50311800d0103405d10200091801140750441400f90404600501890381d407182500d0100750b00615441c1c035690b524094007031901410320002c1d05448040b038440002e5810001540c0d02282e14140643c1540e0307000541000e5030828400e650201f5800c000d049125441514040e4800b0b000b50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 276877311 1250 276876061 276876077
    0x12010f0612020c070815160806010c031b021e13021e07080f04060906080a200702040209030d020a02011b02061905190e0411090f01051e13090605220507 67
    0x140d01908003c6c40340c0792408009028001c22207820644072002c10f500d182071501000791300e800800601022044a000303000d000c282010025003641c0a0f40d203402c102e6000c1c2c820f04c001d0b0304003c503641d16441500200c40c0b2031540c450340404421114425241179042501d012500308200407030158565001202c01c0e00c10b80e00402030455601280e80007400140250741c2d81201e210314006000b01011006000c200d040303410118481e02d170354106289a100a0380f0903071250381d01e40452000400a224001c20304d60580102e04407a00505d402003410b00740c1d035001ba2641224505941c0c0500441030740524001c0d4007040503c40301d500300c03107079018014144000e41026854514544007401145110f0046040080c040c4410003041d07042c40e0003241c0a030f070b14550101b41482080d0001403203002d1001400c41c1003010220f14810b44005000718400c03c9101e0107840c40d500e54255001100500e0107000700d01c091401d140e00024941801c1201e002c0000c0c0300401600c06407405440003003c1c080152008003005024 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 276878561 1250 276877311 276877319
    0x4050d0c170f07020906090709030605060f0a0905010603150b040b07030306031e1b030c030b13080f030108011d0c0d23030d050604090506070305092112010f0612020c07 74
    0x100010b01c480c1003004003054880752980b0400070310480040ca142e0207481c3d40b40030300c280160461120400d4992281021034941d4070300c03011407108011000380e6640000c0781c40f00040c0c0103005910480c160b0303010b42d40600c8003001250462408009038480c00940c21800c0000b005000b124002a0071094032a18001c200f05650352250503403500e1b9503901c1d0011200041e0542c04002c80007000b0410f001c80030418064181c070710f440301c3c04110003e100190404414000240b10f0300591a01c20b03182961000480380c550041c8034080d4100d810902501c00c0310340c6031030b0700f400702d502901100c0400034608000403e6944401d00500c0075606001d9401c03580c80c1c7c05001c3c040441c1020f207100116030b840c410002c40e00c650600c440c180660310050480360281d4905150040810750120304151700c880356080108490701d896a03403901c0c00701e40c1c450910348070641c00c81010704850804010038a281e00c1004441450740c03220ba10b00310b1002c541c41101c001c40c5515054200e802e6040e000740c000200040b0948203c1580c2e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 276879811 1250 276878561 276878603
    0x303060a03110f0d0b070206010501111908090402041509231c050d030906050a0203070203120405031204080403051b0604060c05030904020a081909030804020402031f15020f0604050d0c 81
    0x40c0301c811606170000904010703005034100181c0780181000d1030190005030b00441e03110744490301e1010101d400340142246900303016403041121006d800180c000c56442c0c0d0b6608000781030020700c003485e000062560000050400c100003a500058190340040c0480314245c60070001c0301189503043c1c0801281006031034020401c00d100e807900d0a14a03444c08070740105070740b4045040741d000030b100d60441b40c414010b201c009640001507a240c600040c0034409961680d040462540c0100c011942c6000c0c030320000c0004015903040034100f100d105004a9484078804085141c0c2c0d805000d0300960404001d0000f042454443c40300506a140500c090b80d16019503800810166031018103c0f001050021003406490700f05104100c950006081301040b400256541c010002c0402903c003034070898012000c0f03580074400309001c20482e00c6140c1000a81555508600d10700d8a1154200016000318001291404408030f0031904c91380c2d10401615030030317002d030038207482200e01460103a400c0010303a56001402ca038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 276881061 1250 276879811 276879829
    0xa1e110601180e010e2805030a0302040603270318081b0a0602150601120204170f070f0b12090c0603101a0702060318010b150c0f0303060a03110f 64
    0x208a00102c1e0302071982d866420140c3d140c0d01c081c40b215a00d00280360141d000d0104584642a0f401c0c80e1543d03010001400492481402d85005856400001101424543c00d80d00900841d112170701d05005854844103100402c54590301c8500c00d00400311018030000e0b00c03038012100e1941148c0c032054261358407003070f074a4030b13201e00b07a002c14884910300156000989403480c6504014030844c80104071500c4140282500444080d24140c144041400b01c0c460804041d0103440103410b12064240004551407003455071030803c410f5040c80e0b40665440840c007510401c1140c020b0303c0e46114900c0c50700d8950504c01e01d225000406030a014003610740c004601e55210380046d4010b90403059800b850768101066001030028a45643c1c840b010f0400c035100040e01c450090baa070001701c002040c0c142c802c4421380d0b5405405080d440f50b51001490400009018046000e44581c10360741040b101c0c2401c160034401e0340c80c8001d42d40f60707074000c42e001ca04000051501d40c500d01c10144c0030f00000d00a15011000c20380f41d80d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 276882311 1250 276881061 276881069
    0x10f0210020a0926070603020c010204120f0c2907020a0317190509092202030321060f010c08070c08030406080712050408040b0d090807260a1e110601 66
    0x10005402001041d0200c45098050207403076852113500f2042804076991030b81c280c030411080c50380118410861b030300c00398152001010006080c050b0394000b441c4c11b003103003079070780400316401d0880f001c0205036071060003124050340000c41c0d520301c0c410384469045601e541140c0300881e44840d0300e44009c00090040089a8504602d0004040d25a80d203481100100c01c1075204240401c00c040c00011002e6480ca03503c0341c0c01030469a90f048218209840842a000d4102c001035090300c0001011400300c91104001d101400e601c0d04400e02e0b40d101c400420001003c1c14166500185251482c43d0216410340c00605030680b04601c5a1076469030381e02e0f510f003160400d502a5021843d50000c020140b0f8004402408000450300200040c0c54141c0d20f152081c00340c2c2c01210020721000c20012201c2440754080d0b4880741c0c03c5107109446080070720b08441c41000e1038081400040e41740300300041c0c82040c1c2040d04c1d80c02009440700320a6140360f400e549050313103065450f142080303400c1c4130340c80c8440f1060140c14064 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 276883561 1250 276882311 276882317
    0xd020307060e01350402030f01050709060e0105090d02060f120408120a050412080c0c0f0c10080408030417090409030f02010e030a0504030b090c0a180b010914010f0210020a 76
    0x10344040800035160b00b1641c1c1303007008a640040c0c0304503200c0e1400790700325820003c941c1e108280380d03c490021138940700c84009100031642c83c1c6003e0045a1b50400000e10032201241d440044c4070000f10011601c5010745010181c104d4050106200186040000703040e0560381803c80500b0061903280c130220024094809954400c00040e45a00d100740c0510720035400061510244420704003030350741c4d50400104800d1842002501004504c008100300d00700c8803a070141d4000c991544645415150300ca180d903503c2c80380304594180c00c440c1c203503006112180c841c64101c1510741c25503440c2d0b158407106015482030f14454034030800503090951703560b11031040300714025510419050380e0b0400180c00c4402c1651134012a034001c0c07001b9841240c2c4032080354152580b12810301c0c0c40b616241120b61412117443d0040c1e0b8404082080411031030001880305044103103854003070241321315030001507402c80309600645072031001c020700740d110650140d01d41203107081451040300d02c006416000c8070100d0308400c075a0400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 276884811 1250 276883561 276883577
    0x717030f0109050402060703030c031503082802030406030c03060302040c0c0b010f0b090d0c17030d05070c021305060307090e16150906110f1005010501020d1107140d02030706 77
    0x145500c82861a805040c540508018506203500080c5040c0034600f0000c003059181c401d4156000d100340c001d0300c07800700f400829882241c4c585c604203025401c00c100d540203180503041110305000c9200391400c071a420640155207060f060440807000707040740c2c0058205054442d48000010384030743c0700f40540d01a6540e582070383d906135840c1c0b940c030352081170380500c0c0003d60b240000c4c0031a51681e001c4484520003140e100b04a45c0c200e00d003800d48a030482e0b1101180384062100a840064040000d02c4100c10804007005140d65030001501d04851041c3c02942010295400400384001c80e8001a040701000b0101c40203160f441001c42c0a440b0b60083ea1070040e0822000f031002c0c16401c100f01005043c19004c00c80b814200c0c190003c15800c9a441034200704541503103503140303261003400030103420140c1c6c0781981e4221744020981d4002d04403c2c85410300500c103041902030711511401010b190034143d03c025200745850043c2c41c107005240702d207039581d008000c5803074540103a40822452008101d030b80c94a0070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 276886061 1250 276884811 276884821
    0x1c0b0a091515050d170307050315030708060105190f1e060f0207180b03060403022a13020f0c010509030a08090d020604080309100603050f01060506030f13030e18011403030406050d050408071703 85
    0x81c212b07049040c49802580300120070f00c4039160100d4054151103054a04d0b5080c1c14120080c2e00c0c00402c03030307800405030b9013808034003081d04841000045d203090b910b40a00303903026a0301c5100301c6050060919160040c1c0200310306001c40c0a81c0c8490480800d4140004600440d0315000281400740940d030440142e805520148040440b81e462112500e103c03282c00d100201c04c074004100040889119184456400203107c21204a02c1040d41c0d17032800914000c01091400e25075240da80c1c5c2c03040d5030010110f2494400600c9031040014100c4281c2c000c0c0e8060856502e4654a11203250400340040115010301902c8041614843c0304000c001c1d030140c0018230414500307519840c02c44007181c0005003e41810400c020300c0804c403010543c0c20442014107941c0382042401c04562103902a80410b600141951528104651030402141600c40104e00101c82c244034104060b964411440358402042e410f0003c6040380306694007042e8010302032000f00c2c0ca411856520305016002c031031f404680304400842884 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 276887311 1250 276886061 276886081
    0x207050609070510050a0206010504090602130e0114152208030a030609060f030515090c0a0308030a0f021317070302060703050c19111c0b0a091515050d1703070503 72
    0x10040d85250301702180f82284c4100d00070740307605050082034000c0d911204070710204250b9038103d51069445111500700f0584507101c021710b01c4020702c2200c00307401d040c04070b0102900e0300400c603a065035003a100301850b240242038802070502001016261484281000141d4408284001c0c40022155a0002506d074140203048086500d1504140d4802043c00e0050000600c000381c00031a182d0244100da0003035941c0024545022040c2001640102225100000700711018001d507020f500381003030521aa80050242c0c0d0200e01034803a04e8020702818510420640307003c0c00f5805c6030341c47c680c400e44444907102d801091180c1d20a090031000201c0020b04203120f000180b010745400c15050910700108140341d101e0903000c500450045114009103170403c5070481d00d080b50000305a40c44164000300345820340c0341400074044a0016201c400c900d01c00621001d9240c844c0000c03904540d4040901182008140b001500500400321041007080381c920000c445850059803140502d0743d40d0a661f07107094081c2e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 276888561 1250 276887311 276887329
    0x1c0609062c06010504050d110d030903150515060a02100221160f03110712030c260708090f030c0c180f060108090a06050103081e030f01031502070506090705 69
    0x240c0a80d441d0505108242e81c1c0b04085500b100c000304ea03089292a6141011012001122140d644c4213210200f2181015004a004401c890185a10107020180300890703206aa80456100d00c1c219a5440040024a007000182c0022405441104c2004184d520341c88100d9102901e45138591204070400c80030086040000340e07100c50f03203030302c0318001141c215000349c011940c1054500602d5101c038440d854541c5032030180c034030164004860b04410050008060010b02011507510001070050324460f040e0414418484040c1980c520002d201c0e1352002c804960f1801e001d0101481402646812a6001000c00203815502072040141c0b20070000d84042001d03120b24400342c254014075140c10021201603510440da4040420700307106080d03a0322900c2c004e0510710880700080009240c08008400d00807034402500107008000c40822110b0304041e541206404100c0e451007505030703d58018400500c150344028252110b984001d1709040f0310780c1c0d5035410440225447ca960383d01880e82044a03141180c40c2c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 276889811 1250 276888561 276888629
    0x3060c0f2307051e0d14070f020d020907170a02040f09150e15100807020a02210a03020303010f050d0b07030b1305010311010305101d060d170c07090c051c060906 71
    0x4600c8030b042940406c0c20740c5005451003d065030100306a2501951903000c103020120364000c242034a5407070310080c00344c800c3c1c2040c0c4c494140000b401c07000a92031815842200c06482c0910080c3c10a507150052080c098584080305007030580002c4c800103904112100000d01603013040c00c44c01014158142444980904444010100b009000500c0821a00401c03030582464040e6080c800c208120011102c0200130008851464815071324004217050740032010318140c8091500380c01a0550f03a1040002d400c02c0c20401070903c1c82c51030003180c0030700e002e6841014030007c00b030400155103905140905c2260000d030b0094441c40b000840b10003607980d040c4240c0b0341c0284600c00f1a0791550500c40c81c504140750003194070361041451004106559114004001d41640c44407803001580800d507207108c100d03081140c01500783c5c401d0041c08191034000f0b00804d074000300c25036a1a030501d47d03942c2400344004030b46031600d0300039aa160340c00b0450b02d410b401150042c001096202c040e0011410120b509428003040c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 276891061 1250 276889811 276889817
    0x605060301060c141203040602030402151908090c1018051309020103200f1c0207062a2a050609010501050f090c04060509011e080103060c0f2307051e0d 67
    0x605d41005c60710580c0d4100350010f00060b01c0e9a41d601c0426a1401c0c203480d580c21141000c5912113140c80e030414501d80294441e5651503198842086640c1c1c7c032005d0481c9140d01c400b4440d551243d403032140c25100850381d03858014103c5650f80e603020500b00300d0f1628031041d22548520011041d942c04d800392540c07280d072401c150003103000c0b44aa00c3d8540c2c0144201e47c2803041c2e0000b0880c4400a12500c0e0003d1760340a51011595010546080b00050100e00b43d00c090750110010039038101d030341c5019919164241c0d80c5510091b83c18005c4000910000d0010090030308000d502c1e0754022460400c0064030a0450400005803541881c00b0003170300c8100b81400e1407240c108001000040031556043d6002c903001c1e4102140c680781c0b0200181c40008200750300c91418038142d13020740704e8290700c652a03030f04aa0040d05c00b0441c4001c1d45004840300d2214401c44000b14000e070044c001045040c0c01245403206116044030300703062565440908004804681220410844200d20040d4005004100110742142 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 276892311 1250 276891061 276891073
    0xc030e03030405070311040b0a0f03020111030a08010e0403050c010509060f01090c0e0d060b09240a0501020d0e03011d0304030614060d030309061407021b09060609040504060605060301060c14 84
    0x550f405683d40214000240410f0740030800754140c0c2c132035802000714070303800510302401d607500e442e032040051906120590000f44c0320801d0009643d4003004070b62445600d69905542c42e0309020b0380818102018004404002080040841a100a00c111401401d640f00601000e00b480c0d0100c6400f5031040c3c02030940c262801c40440c0e1000e0308008610385022080e541094124000d0a00c0c100405446c00301c6c5070048068030410200c12000c1015171560541d100c401804903c0310018001e1500d5a401200c1c0581d2020b011942c13014041c41c070f01425820010000309001401c016034446410503d0088169130703001290500810000703009108000340126440703840382c81c00000003282c200e44488080c0038940e44000a405206c415040b07641e5082c40707106025894103000304025519504001404680034031040b03031104510380f840409019600c002c2a41d4109016401003000518001d8402c41c3d080343d4640300043c598490318091030003000d132500c4640c0c000025041081d101c00105440c414140c000b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 276893561 1250 276892311 276892313
    0x1090b0f18030a05010c020d0221041403010b040e0708121801211503200a061107050d1109010b03070c03030b13050103140708010b06090609010c0b0a0c030e030304 72
    0x180ca801d200004400d03034030075455201080c00c000e00310801034210b5082220308080103400150140e03110f200c941c01c48007182c0c0302d5240782c5200c20701141040d042c607404000c104004e000d00c0c2c1d40b031407030200000e000103200e035280c0f00064200d070341c01907072210160001001002569030501403040c40050421681e4544108510000b080b00440b9030301606001007004a1010303071080040c0714016a1b4415000c10070301c2002c0d502070f00000c410384000c03911007d1350003c2c0c40d03042240c1c0b40707000c1410401034030b1204078030b0520b101070310444003800312010607100d1200005200c1c0c3d1504183e0b0251801120100d9a4192082c05d1000b074000582103502d181d00100140034030241c1c4090001a90f580501d000100e10110400092400c03501d849811400c605040c0040148010b201c00c01101d4190b075001c8900465991a085007a1400d01380150340c01401400044201c1c101200281315000d41454610046405075845109000c8180e8510001035030b40c2080c0e00ca6181c15120700700042500c2c100450031403800e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 276894811 1250 276893561 276893587
    0x309092d1512190c030602030a0b090a0e2a0a090506040b120c060d02070b0f0a0f090515040503040e090f0601060903051e1204060302070203010f0c0804060902220b01090b 75
    0xa5640c8102c4100c00c486050709201e130038003003400510f601c81002e6540e81408640080030b000034960340c9228000c5030f0041000080c086c800d400300d0540030b0000d4480012003402c0304c200c5405501d41c2800d20003503201d000d0318030394171040100d01821081e0000141801d10b503051008440c510f140305400b030b10728009616070070400010061221001112440c3e035031204070440e4006405a07401c001c22140483e000c1c8580c080300c3e4040d40d171042140074010032100303440b0068682901c6801c24060b00340e2300891203900e07002803e41000340d40103000f00d0031645800d5840c50a6560000111850180d030340020088030000001840a54010801442c02d04440703800e548902da1202c0c840d2180303006000c9603400d00001c0f00c0080c00f48401c5449112440c541f110f6994101501a601851040b8404d5282c011417964098031441003d1352001c42d03a03207070300300ba45d0703242c1d1407a00900c088174042c3d0b130001d00c00c901d5206900005448052050701031402065031405000050300c0702c48a5000350b804040184400103460324 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 276896061 1250 276894811 276894823
    0x90b010b03090109150b10080c04050f0607050610060e030d0801050409050703050601060908070b0c190303110d0f05100302010807030c090302060406050307080a06080309092d1512 79
    0x40d2061a9503881d00c030442e81e64010900b0f80e800070002c0c11202c41032034002c406580700c0c03240c0640c1134441c42000c2d5040b120458054200b122500100501448140490b050101402540401c058485407602c45107840c3c891408604440d242d038981070181090141c00c0d4012070603141448194010300c00e104518402070900c0c541400b44034001c03a500c106d01c40c103112081054000664002064451039612800020031941060281040c18898030000280001c80718088074980043c0501500441500c040c0c0e00f200c5540c000030a030101600d5441d00114448107600410b5003481d010400104443d499481c1c0381034030b10040200180110005040025136004082585d0148252034005090001c215050b030b03100040b50400785d00100046004645160040015802441161181c01c4142e8a520107403050303850074080e44076541c00a024882160510a1040c1e4018400301c60220031609a0461852407024113a100c00150074080705000104445440b0f9003c1c801041d111058101565500c00c0d90381c213 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 276897311 1250 276896061 276896069
    0x40b03010302100509040e03041d2512050f040218040b0705091302040b07050606101413080a050703120c080403120324030218161206050d05030c10090b01 68
    0x458404a1403602c5840342044a400304002081040180441060940e689d0418046c54001000c50300500c1014031042500910905954040d0841451658644204001c0403030180081c084100c1801200c005180070b80c0e48103050346003418146e844c0c070340100641286005c50a0b164485000180008120001c141c1c5038000d006080030740e40c3d143d4050210b50036a502a0b40340c10054408600854089d400800504c405030090017229038a4540f0401c000754004100400d00120b510b0401600d8000080c0000c0c1c000c520920704001070580d0340f0030030941040345c0c0182c100c03034036040380e01d0500400000c4004581c0c0b92101c0d1401049440143c0c1d41d103107462089002c0507000300321043d600d00d500341c80390b0044c080601b0701040c440c0011022030905500c1d1941404220301c1070441c404107486180f0800c10851042183c006040501c4521900540d0307140440d0340c40308102c035103a19000ca05030720780c3e440034842c0d24810001036a8500851060380d0404010358212284682066030035004240d42c1c00c1428156 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 276898561 1250 276897311 276897319
    0x10060b030619050d03021e0105060d11030106051c02100e01022a0604030c09050c0f09010509030f16240504030b0a06120b0103021c150c0c1a0912040b03010302 70
    0x6003580d030000808602c0c0700e520aa612403995900d01c4d08155020520784621a00280d5541c80044507540150984500300c6100d03403c9003841c20084040390400181c4d2580d1403010740001a01c41c3c4600210b00300030400c040c007190011000590340118102400703402c0380c94405140c4140c040b01e2b110b00003502c0e4503680c5615401d0b0504084903e1314490080007083c0d144030000e0400f640c903503692621040349040f03803266003c054580400922007000b4802201d901d8104607071220710b09004800151007980200c3c140540611172400180c251101c00c0054002c210400c1d503500f00307070b04d15120007103640d072481852000018821102c0d0680d404c0d00001501e0a9036071003180070040365559084a4001d040c00c0c0c2c030200d8417041c48090b41007448880400c00c2c0c1a00e000351451001040d100d6103501e00c08262040041450381c0018031041d280b82e00d64840401c044032442c00429501d610b40710041e00c40c1007200820300d2500c44c60248110074400704036143d802c400d191542c41c2410300d070000c00792440c081484082d000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 276899811 1250 276898561 276898579
    0x609140a0515060f0d060f15020f0703080313060501090f0c020708030304170d06090902040c02010b011e0302040305150a140c0d0b040902060c01051909080d0e01021902060910060b0306 81
    0x108040110565102c0e100081e030800002e595081c2c0710505c1180c4d441186513840082341030000c414404a807040d0844100d100600204e0f1030b45e03031383d4000359100414401c03410001007840c3c0b00007080b034000c07203008041804006c1340b400d00811180d4211313040300902405560000004000a1602100b907a0b0300c00e421210005101140c40640e80c540c0c0314401e0085445860300d20082a0003202d40d0046220320b0082c0d40c02c001c0503a05505c140e08072000400f40c2c60100e41100815041c3d41003520a015442c2011304d00135003025038941c0c580d4580342c600300e403114060b403119003042840003c2c3d20410310320000c10b084800f60b82c140304400c01418401d0b618080c07034fd0703611040c0b0188aa10740750080783d00c03560f01800d99580c482c142901c2c14005c0209a03480d0324941c03200244414108094090550b000c0c3d00448400e01c4d04a091403003100a1801c9002c80c20955004d10951803506410208902d0182d03c94024000b14603203980e0250030b00c030201050444891400c000cc1c401010154143c1c0e50042081e203821071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 276901061 1250 276899811 276899827
    0xf13020903010b1909150501082e060e03010e010204060f0f020c090108030c0f03090a060c110604030b0405060903130611070f08010b0102061b03060108070c060609140a051506 77
    0x8058100f07410003035013040040e81c2000c0d00840304502a402c94510800c1080b070450f4480303105280410501c11107001880032808100102d107404122000219a0143c908041441c0f00174240c0103620380d441480410405001214a418280500320041040700c00031854181841070281852100c050b101e410000400c03c081a15402004544d030440f0004181b11295030307641c000b0b0f907030705d90110041c441d090107050b0300d0a8020400109840382c0100080c0f00d01c0c061400c104007140d07401c00201058070015544c40b00ca0340d2039203802004002a5014600e50140d03444c250a200f8540074000c2c044040551003045100c050f29060303440041075070550300d004000804940d0304030749010116007181554842521001420110547c0070705074460081e000d6030100d50f50094101100b000702c008520b015801040000c0d5298426800c40f03a00010300d003045004c1c900b40b512150201c899a401004409581d601412511202c0701c144540c8032050345018029450304400f401c400ca003404003518050640400d11031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 276902311 1250 276901061 276901063
    0x2042105031c06050a0e150315070c060204150216080a110f0409060c090501090501081603020306030f1506130e1002030c0708070b010f05090915060103060b0a031401050f13020903 79
    0x140c028113000f0804d901450311050300748208601911310700c00b02d0404800400080c1800708241c0449518400380c0034041cad551010030794051000402c2251095400c21000c110101c0500365000070341156401018104500100c241890117160482c121642c446c401000028000b150070f11815907040d51908c0c5810384030004103010302100800204000e0628402100c2c0c968406882c41c1140d60036a5011003e6a83d0300c01540c40513401e0700c0c1c01c0d14045110380800c0095020341c00458100d1400303800c480942800ca030440c2e0804130380040c0300140d1a5403800f40402440c01820014a451090340100700640c4a000d03100d40e03400340c21150041281c0c02100050040124005a40074075401c480116603a0440340b030f014040003000d006251180400c42008035150404160091159510354020700010303e02e0352400c050004024085810035458203804655911002c028054050040e140800c5003034400820b40107407001600514007580003400c1e4101d81d135032130100f80c01028042c50401a56007008074042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 276903561 1250 276902311 276902321
    0x7060209030303040f02031e060406050402030a020a0816060302031302010c05071208030a0507030b061806040b1c1a0f01050f07020d050d020f0a030c03050306040608010e0102042105031c 82
    0x303039041c0008000c200600180450302c1d0001c1c0c0c400c8007030300c0711030f840c0d402070607821080b086c0311588940c400b400003000554141d00070794026000070700303e800c1e145640e40040da0302ca030650001d48864105420740c0c800799410042032800f405481c103040d030035480c0080f55610503a0f1000c50290400ca261202002401000e0240d04060140b42102c00c070303842c0d110700b402c1c2d14a9005440d160380c41840c0c40f00180380c65200303111b1000034541c028a01403501240c10070044588040c8040e640d80041e0070040094000130000003844075009080c0c000202504d00207500c0100c44004941c040308600801c2e00c00702c69607465000744810b44090800c0c3c2d840d104c4108000c0064080d0010080d00600034500b11810700c07c2c0020510441d0030310394201d51084104500d1592038070034462000380803500e5501d0110019000f44051544601c0182001030003e503281002d90070f440f01d04500f094070b658009020b20500796003d03c0b809400c43d000c498480c3c106400d0f85d0341503907441024000c8411a140000c41c1544491380d4000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 276904811 1250 276903561 276903577
    0x3050606071b0819050f0703110d03110312040b06180106030c091a070512040e06010c080d091110030e190f14030a0e0f090402040e15100f2306070602 66
    0x481d41038a902005040321284c031818281c840384a02000009400d10001c0c181086c0c80e44004c40c0c482d010540c4043c05205c0c05448030440074084d09420206500c1e80410140204c032554030b5050b03506090904140d05403840c0508800d00585000c80994582e03100c0b01c04031380c1101c22904d8002a05a04104122030842c400c1d0401180108405945055180720b0000360400a01030003c4d10120b842e002c854003098844c9106841e0092401c0c000990b4542c05850103401361402414007602d0900e94031803440480c2e44402c41281c3c0000c000d01c8112060410740d81d1781c44007010070b0504114290040384115512090312024940c00c0c00c80036184020085010160040103501c100101480d42450f10081d45940100310701a00049041d0790b04141031504504d520240741014020100940301d80d0203200103800210b102c500070380b19000b0f903052442c00c4260418442e00707506070b486006500f0300c0300e1102c042d035050b03101c00000103203000350640c0d143e81052420031090b4101c5640b681c482c060b00d002d20181c020012 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 276906061 1250 276904811 276904813
    0x9210632100b210907080c0609280303030c030b01080112020102210a03050a23060103111602030f0d140706090c06110d0206222112050703050606071b08 67
    0x80c20f86594408445215846105400c0030001c0396106101c1c81e03980d0100b8440e000c182d41c440c0e0071484803810240000c00da48080600008031888465016888103802642110340c031003910503040092503414070540d0744410300c41c40c003070117030030b0080700002c100b04c4c018003a80800c07000c3d04001104681c000c00001c0451201d00d05500c03040302040c803900390160444511400800d050100003400407980e44600780706142401900704118100104c0030001300c600a007400d0500d60380b4070310381c0b012076100000380000c4446c5d10085a0040704030b105250820b0f00e0ba2140c100170341e108889104009811144640010310f07504180342e2a5449818528060008410b02400340d44000c040440c80b181c0c13003030000b10003185801c00c8458804e840c03401240d49500031200c0f058181078007000d04001920b150309142c03040d4010725200ca018050740c001c1c1041c62030030050600104900e440e807008a16000d000309a403024603810100018074240010450621401c600180031790328029001145918031140f2030b0150807140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 276907311 1250 276906061 276906067
    0x50105180d1415010e10261006050a050609061213020901090501051002070303020c01050c100c03150b040819031106010308030603070801050910020a09210632100b 72
    0x501c0058882d510101072108050f04140041245a0b00d004001d0180c00d02c40c4290b030200c1e20b00412021034400100428175045514000b0b84030620b0f007048103035068182081d0004005140c6410803020480542c010f500030041401315002a542d1001a80c81d44003203004082c4041d40e5402c54150b00ca041004020341c44144100007040c107001d9917008034161001914102d1809400c00030684ea22612403100a00503404030001c0d06c1c141d44920003400c40301441008444070240c0c847d440c1e1094508030240c2c200000c2d9030f0340307102c0d2081101e0151200200824042a031906d03091000c82519418640c800081c0054155600300070544036030045082c42c01c407441501c1d110758403440c110800e80e0003680d0f0b00c1c1c424425004080745180f070602c00c46004810117001003072000b4903010300c0006034020001c242c0c1805150280090310150508141e80241107103000383c8601119407174a1002ca5401082c1e403d82220110120320310761030641c0c611000b020462403040b030955103480c0100c8a50784180c001084110303002c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 276908561 1250 276907311 276907343
    0xe120309010c0c0b03010902030402040e03091e15030103051006120c05100507140718020a08360a02040f020a0f18120501050906090d050301090f0216080c16050105180d 74
    0x19400786002b94070866041c001c6006010480d030307403401041d0070941c0c008400c0445604c002040c00c81c1400405000e000d40031004d12001e80300d40c803034100740d2041d03c150304001c0303001d01013407000d20030b040140c140c20505202c00c0405403106800250107016990003580c01a042ca0105070060043e50115135100040e000040d54580c01c8649a0225100d80545084028550000d42c81e0500a0f1200600181d1b41c20886640c0d000219512000c02c8180b04107003035071203080034010b5003040049001207010400070044107806105000c12a02e0150300c1d00390440c414403003019907a910101043d590b48507480c3c46210307000241580200341c05543e2043e02c2052500c1000d20401c50190006445030500400ba6209a51582c2c400e68590010160317610000300b0400050160310616405940e080424000060a08d00f2868401c00041c51030b0708159490313800820940800030041120041101e113400c03800b04410701c0d003000a0054007680710142481044d0600e03100c02c40e106c901d5182c003d1600700614180720124 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 276909811 1250 276908561 276908579
    0x17040305070621020a0e01020d081303080a0902031c090f0e0a0c1202130f0b071e0804030512040512010605031906020c060a0204030c0e0705030c09011115070e120309010c0c0b0301 79
    0x6e541d240e01c0c0580203c0451402c51400b0b85146403040f68030b001c5a0800340e49030345e411030320520000d14920780c00303540300d80c0e520258804110ba04080120060000e1a85603005800741001c0410f038007001d40b51900e01c10500010329034400301034101d060250042a0070f080c80034151590080044100c41081c0f0104591006100c070200080c00c94110b40c200b804020345591032017215106018000c1c00c2100494400f0312070b000241c007201030540c042e441080c107054495035101c0c1080302e5107441d0104080301040a12903440c202c41642c2c0d2070342e003450082180c10316181c04240c17a881036003010321411118000900078000c0303580440b2041320b03081082d21054940b500361030009402038081925058200e440c00701e501c0c06800c400500500c600c4d00c581c4d003103640c0c450004070301e0342c80089901e040103120801c400c84100200701c0c02010714143c1c25101801e1130070041c000e16001001c43d903644101b0841c1c001103040303040401207a80c008030a1030204100b42c0c090411a01a401d198004490340c10300100018240c40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 276911061 1250 276909811 276909827
    0x14120406060f060e1e0d0606060c0b0a0506031507021e01050411090907120c1d061f0903260313020f040b01080f0402041b080417040305070621020a 65
    0x880303602c00440083d101c0b1021540c840441101c0c40d00100c8450076075a00080680c00b08810200c0101003c00040d00b0380d95000942d10180d0100010038100912401000b01038402c40d9480b440b0008100f01c2458140c0000e607681081d1101d840c8005034100c0800c403407510911240704403aa408081d0002c290f1102c442a00820b4112016543c01024414241480c60030a0b4400c0c0980e81d0000140302c400e080401d8000c59504031207084849034404080082d1143c0c11565221107840c500e440410395280240034400c00d8050303541e1132007500000c4200d5000c4560014800029680c100e019044c1480c0040b074070801300303000303240c4100071060b01004000e0440041f0f101c5908542c42501d55246a00d941000d101c01d0b0fa02141e070150206075010002400410004c402c0d03540540010800b0469440f0310001ea040084086031140c00a1010001c03c814000800a0380d190703c0c0003000294681450f41d111030752501c0044c06400100a00c4800e0600796903400e01c450540b441118108554502c4003150141000e9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 276912311 1250 276911061 276911069
    0x206160f050717060121020a0b12150a060e1201050c0705011b0903080c010f0c050711060f03070513030203031902211608070b040605180606010509011412040606 71
    0x1109404001c02c1c0c80e1110403ca40a05400340c0041c44164200021001c81d4002c0e904120f904d010480e140c0c1c0096a9080ba1401c001e100c4482c0722a0790315410003803400782000007009480b443c6626406c00182d521000740ca04100c80709031506a02d05200e0a0018100240060050000d50300b0003083c001120340400051010f144200000c104010340312404a2042e032460a884d404100d9032032080003c64030160041140c107224200000d820300c2d40c01d42c0e85084030082c0c502c03500007950100d214010451074501410721050b04079842410280101110200741c031005094000f04540071410001317a694112080b4080c2da4014141c94a5105c24500d034a6031000040003c0018880c680b0f10f8230041240300e02d002c0d503103001c400805190580000700340c0c002240c4100101c03411340b000c210640104d0800d00c0799501407846a48041003034200403081c00c20030b420001002d62560070500c2800360a0381c00c50100d07540400c2c2820320301d080c12448110031429000d030b1440f5141d80385c82e0104020401c0b0301544000152 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 276913561 1250 276912311 276912313
    0x30f0d1716050a02010e06010b030702010b06041404021e0c030a0e1206070f0509040f14010501020721030e040509010501030b221b0b040f06090e1e040206160f05 71
    0x31402446000c0050201900c079509004500d03a01d000c2a2403003000107046880d014000865000c541806113450050264461502c0440c0801404911a8280950511060200c48807030a213804c006440600c14810640d40d407140740c0c0010610000440c0c7d1103246119007100d0b0410703031205e0529500c0758803548444884c00c00241012074001081c40c08184507580c422540d401010241d0b1a8902540d080141da4004028040140b142017050f030303071342d018510901d0088403010030054071100480c50380c0c24041c0c10040c1590803e00c4140711541040340200c0e420115880007503110102c0e801c00b6203111030f03554080c07500541040c040200c035900541049048034032030b400c210081e98a800c00000122065010801e8080b0728a000c0c501003012603040c0c07240c14022641221085903600e41110f05a402948900401d605444c810440755400544542c01400307e050802500d01d40140300042035a043e2050304100c4000700041001d540718001901c1a00c4e0aa441942082519003004d0742a80f881c81c40844031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 276914811 1250 276913561 276913577
    0x40c111501030b0a0504030c390306151a090109090c050304020f01021f0b03150910051303050901030507140d0f1a030604020120010609020a030f11090d0c05030f0d 72
    0x2036424904c20540301c1c0c0d400d0354a074007014406640342c03d0344802c6c00c100c02d60107a43e4504c089540279404482e94001100140b9001d40c5640781d8901002500e100402d801016420704070204040c030b50400d40310415a49004000741d940c101c580050710701d070f49640c0020707142528011a041c001500f20000354000e50003143c030221b0304542c2400499850b0420125407180c0c000d1507460382039104141e00480584400141650b139a00d84001601440980c01c0324002d089902c40c0382010b003002d20f54400d9030342100100104540210050b02c0141446c814841118105a07540000030844c40c811072280d5100c1c4204401d40d6900e000304207410000d81a1242d003090454608100348103075045803180c0218090025015040c01e65541d001034501201100003240840000d40648407800c000b849000301600220703a0044c0c0310480a100102218006441c60300554034000d071400c9a850040b00b0740f010f002c001c84002c14021894a89031001d0641c683c020342d09841043c44904900201264040c81c11201c0ea40b5540c1c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 276916061 1250 276914811 276914821
    0x10090305070f23030714060405030604050d0f021207030518090709170105012105031e1201080604020a1a07060e071e030b0712180501090c080714040c111501030b 71
    0x106090584440541c15804014200321b89010032008807400440280f05508255544c0c0102e810b03d0401c40e011611034000005030041180c05c400e8450b0403446510091043d40c0d1a59980306d0240300e005400740500030081040559020080c42c4640784210180c0f00c042107040c40c1c0c8003d040020a80a0031b60039000301e80360400301090521545048500c02c100e0b05035500382503641c20081c440c00c85c00c160342ca0b01040100680c20081005280c21204282810655410b0f107241c40129440040c2c0101001d90449420301c80035954407460401031b94080c00300c141e640941100d0100d0580318400c001414541050070b98030348990007080b00e000300ca00012540024000580c421040481c1900000300008180d20201d0301152150384070b00d4250540803400544e4001c00e041005407030b00c801c50200c034940c5d101d84400007000207a00c40c200003000a0001000c1481c10030721a1a5000e0341c8142d00d500540d6280c003211582c61098200a0b04020f844041e9141c8001e41c1100c1c0c030850b0004d01041d00c0c0d81c90b450f00415 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 276917311 1250 276916061 276916109
    0x9030206090f0d020a020411130308130b092d0d0f0501050106050c100b01090902030a0f0b0f0d0f0809181005060a2a02151e070209040210090305070f 66
    0x2c0704899007a40504511060b65080100238000c0441c7e1203005001030010300c0c030301c1422401c800d01035802a4003c544886201c02003080d103220b00d42188201d05d500384a0350303000d82c48088103440c02820340b60358003401e040c40154072034402114001c161340c0aa960b409150600c8040d102c00c12045000708000d1007140c0c3c84450540b183e01c00e0480d0000c00d544110441007005c00f8030340c0403407607200301403602803040340d41c80c003204090343c09c151101302ca2282d491402e00c040c2034183c420707900c0044050311144140902c4100241a40e054500c018041d0401001d568003008040320487d83e005100800b08404148075003407a090045080703801d10b20300d81d1680008151460010240c4000c49200da0b00c1240e6040c0303207500485050041c83c440070314a0b11621410b001a52030214800d00c944482c506039407181490f4125001c00d410300b00c0c0644140f1001c00080e00503031204e1892552042c1c0645c0c9a4180160795042203c10010a0340007804034092920b0202da08000d0960100c2101c0707001003d07055191400d4445 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 276918561 1250 276917311 276917323
    0x1e0e070e010501050705162301020106030201051e16060c02240103110d060903110705010c05070302040e1f05040c09020a080a0510080f01141f03020f0a030609030206090f 75
    0x100d881205110010041984183d004001c1980310380141c0302d0130380c11303c400050f200007e600030340a01c0c1319100e100c1000701c001080c200c0207440e00344028016a0315640010300144100d0210624a652000103a11000390318411078220807001d5500c450307484901d00701700c2c008008100d04d01e00103024040041c12804882c410100c0c50310a401080c1d24941d185644035020349805042d4180c100d4540d50548010804503c6020039190280e1204503282c28070380ca000e4140312041c0c0019040c08005980500030802c0018030700252a415580001d0400c03100342e00a1814040170003508604c58400340c4009008078903000903000d148962201328565403941d40c00002d0307001d4404000d0026000f540000c1e1620456040380ea0045440051644d80a886800003414030011507070450303090391030340100d10b0181035008609031f00600c0101c070f44042450411401c48000301d10300c1701900c0381810421075031150b56049120002554810401c110313a22503031401a480701012101200700340610f00100321420030110346 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 276919811 1250 276918561 276918569
    0x50a140613120e0103060b03091b0307080325020a03060f0606030209010503060405190903030203101208070803040c0f06030b04050609060f120a171321030c060f1e0e07 74
    0x20b051501000840101c4003880c03100d16460400d5210500000c01c0d885200c0154064144600541105940220403100035a5001400380c020f5005420401050b60003200740e8050207281000300307054030b543c101075440c000030307100d0080d6100308001400001c00c1200d80c4661179464032820b0034000680c1d6840b0540484c001d0720551804a0000c0002944c68502039002a40c0442921400c081ea080107080180484407005421404a0741c00800e101040c00c10a4400000b0042a442c1705d0880c11135a54940d081d01a01400909081020012400704130310002180040c2c913071001c0a4108c2076403031714024041d1420b80491400780d03145c54041496424680e05251040e00d02401201100d1101303002c0c490086900f555820890064401c1000040e000941410203200910305440d2078160804110b10204107941c0300c40b86101c078015a03000700761000891611071b140c040c02c5c00c115100203420030101400c008508030200c02d280405009100d1643c00e03e00e1200300c0080d500300002c88030002c01c16a2042c032402 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 276921061 1250 276919811 276919823
    0x9031b1c020105151009090c0c0c0509010501052203050d09050103140603061801020f0c150703140f0441010204050a0329160f0315060e030109050a140613 68
    0x88809150800c00d4101517494003a04d0001211555401034100302d840c0d0016a80001d01d4064144060148210740100541400c4405e20995450400042d01c0346c4584002e251a0302c1d10180c0084a20b8001d0108800a41e04075080c1c4811110f440d80090a03254180505804280341044444001010310b0001d441004050002d100503100c140b0001c10110200d2000300030b543d0204103e52114681c400a0000c4066a00040c8140036040d403140b4000000100b0250801d0302c0c2c50902040c83ca451552543c02512600040303c960301e070f0382032510440340c500309009281c040038000307022203500d000e02e10b00b0f02160907282082d4480451035084d0a034801c1e4801e00ba440007201d4001d00229030168408240020310705040b201c0014510810074145104680300494601e490703d01c441c9242e0444004142c90a0301e18042058805c0354120300b040301407074058032041164410350240c0d6510258044600700e50000c044a0100b000351501c55003030310030700d6000c000c0c50040601003882180070760302030070078558028 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 276922311 1250 276921061 276921091
    0x501270509030403081201080d02030f041a040305010e0f060c090f040209040b091015030c020a110a0b0c070f060810031103030d14040b151809031b1c020105 69
    0x40240080c00c000741000c901408100030000004801000910701c03110300d4103041515625283c0c0e4103043c4510034181c601950401c1114250042c1182c0c2194282e17070500d1440300030410000070b800700f00c2c061a0402442ca41c83c0c610350410240000401c4003610310f5000448403240e41d802c81020150081c0a00c072500a2240400701d115450960082c02960a001d0000074141c1014000244170f24000e40d0450756104404109004426481309041c0303040f54241001c1c41006011f000081d9103440307590002d000850861840c00b11644ca007402c00b03006003098010705441c3c280003900c094803820244104e035070903c0148130019007940180c502500c5000750000ca12640d07880c0d0b403200e007061007060884039418001080003406a5040b031107000f0a0503c80d020008580c0b500b481d1000c000381c0c4c0903084038000b00000103544900e60b076800600c40502d6921004034940c0c0c03915008a841c6000c0c480125044a041c01750f51004c444000030465140e4046555584210020310003c2c3d00b00c502c01c0c2e40840140ea541 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 276923561 1250 276922311 276922379
    0xe06090304080706230a09060f14160302010b270f070207060810080607080a0b0409050705060702040902090f0f16021c020c040906061a03011d090a080406050d0501 72
    0x7003c400081005d01d0003032280441200190340d8955111407a15030100345007140174003072140c3c01095020b0000072420030103400d125102011456000d00702c0401c00802d99989104100741c800c0d00914004c0301d000d48480c0501d2203012081d1044030442904164040100c000201c40c0c1c0c200e0036030140500f515801401d4028200b590407100f5402c02000c0d00c2002c0c0460380001000070040201500c90300b0142c0da001c210341031460945080d1205200010701c2241410552000301c0d0303012404408440c401c540580c3d8a00301407012401409000340040d50108010080051914000c1e441c030b442009a5000d80c42c00e03030b0301c41d400111980e00401a00c001a406442003003d10341400100172001502030044681c44245480024181c928103d41250a9611032608010080341501c44601003018400c48604545c10140c1c071010007a6100240d410005401021407101c01c424024807014075040203280d0342e11070315550041d203964400f04c0311801c81450100002024406804115010210401e00c400d0007076030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 276924811 1250 276923561 276923567
    0xb0a020d2a1b120203160305030106080a09020916090b0d050403110a0b04020d030306360c050f0f0705071502070f060210050a0e0a1104150501120c021c02010e06090304080706 77
    0x118482020942c4170800c07142d4002c20101c0358070036403148a03179071700c0340c3e20b60500344001c20303140d0041c200c1041786041c00c50315001a40c0d100c90340e550000c84a82d4060268020090440b4003c05c1c80d0300c280001400043d03030b040c0f000380940003540f15600075200c607001c000b001d0501c25550300010101901d19400c1d100403c005203814071a01590500070f1902041032615052003951701e9100807113030241c40c0d02c0100c82210034100c0c03600b00304443c001c03042d0401c9090b00c0403401408d5071040703201e103c41c030000000d82140c610b2103900540f044540c0003400c42c0ca0164680300100320481000b040e0b40c01610070603030001524024003542c8000c0d1075159020301105c010001001010740000b91064240075100d41c1c2c40c1001c60030030440c050303289002c3c113044042d82602c44144412214042c03040e403030504000030240200c2e60054015060051440b00c0040c0b400d40441d4224107100f403400d034450003c00368200450450340e05400c03d24840c1850070544403603440d04408660780e48100d2140c6003071600655020024580 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 276926061 1250 276924811 276924833
    0x120106050306030109150c17010b0a051312050304060311031009090c031b090510080a02060c0a0f0f050d02010e0606040e0106080703050f07210b0a020d2a1b 69
    0x102c050000700350b8044a80d42c100040404011a21116a0351800416a0341c0d100c0c28516603024418410452941800010300e421701c40e0259100034041c000030b01c1070200c02400061030007800d072000c2c031350005591854a50303101e5100c1d108060000303003042c0081c0501011401203a001d046d003a118000c040c0c1c034201103003000e024422001c3c0c070300e60509580080445c5220321140754007152185514411810b00c0c05207408c45401a09030501544240f40900c000c600001b006410f2540441b14540c40701141c0c0441031034980c101c0c000421075881c501c1484200005142405200f91203001911009416240121f00300c2d424a210940300d540b1070000305981d420b0944c801c1e412090040c0012540644901100f8a00012644100d0b0f02c0d03880b020805100c0841440108090607030303003480000b00c0e45690001044c0b41d10060f40a8030041081d1302181c24030304d46504a841d00051031105118403c4010703480740c03d0050300d003080d038020f600d88211820403510a1a04a0721606002c4030f6510104882c1c0f5038280003030b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 276927311 1250 276926061 276926071
    0x80309211305010f0e03070e010614091014040321030b010e090a020309120f0c1c12050a02160f060c050f07110d0510050103050705010e0102100f0209040c030f050c1201060503 77
    0x11000c200c17400e0481e03d040c0140405882c0500c0f5465403545080c0c0014003524400d03482180d031050901214045583c0c0020710054100b00f8580100c80e010799001e40c01d200e100356030000300480040da014442402d0b00c48a5240300040d152810003211400100546003a80703803804203940141c034203002444400041e405180c1050b118070440748403420104510183e030f40021b003021641080803590b164004400c014481100c880c91403803403d10092601d003d480791100b0b40140c840305072980009200c5000b03940c180c50703540810f1889140c4c911128240020700803080c1c0c80949000c0d09001101d0340645c050801c49401c04d0011a0341032420340561070300c01c08901194000d5520810540d28103020407000c0191346a00c41a448000541754911f10b40942f0302110366120505000701e1a281d010b01e40c2c2c02084030b801002c1050404121802d8511f90040284184144694132500d4012000f40c02c99141d4012000801c9240007045151980700c00c0003003034010743c9028900e000301e40006001c01807180014603082 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 276928561 1250 276927311 276927317
    0x10801171c110a03050405040609090b130812012402060c1b070504020403081224040209040e1f0b030c0a1502101d19031d0607080309211305010f 64
    0x40d0b0385400c146410020800800d41c00200080390600c1310703141520590006001909041103034401d40c0d0342e10880804000d00034214038100046d4036090260140482c0c1410f0221003001caa20f603150455682500f8100403508841c0c0381d80701c2d41100c0c03240000703403031402070102400c05c5086c1461542e041040b01106050504c150092040009090700c960000d04045e52040c600340b500c030b1000000300150900300410030302100342056000220381d6082031043d0350780324041d1000f682d40d11001d808200a440c82d0304001c100c501c100c40b0005440c52042c0032071100714902e150f061292580c06010143d4469070f410395150711100381c00741040342045034040b8104032111801030360280e00346c1d906a40100c031420810081020218150b110454005010581001e80418012145030505440c010410711402108402d24150760203031403a5a5140c5085c0d034045980b03c44519545e01d8840d840544031003641c4460510130b00c2c8440e0619026603010140c1d40c8042d4440e000407a160f18010045a182003503140000c24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 276929811 1250 276928561 276928577
    0x30c030f08010f17010f02030a02071704050a050d020315040803070210050408032a0703020d09060507030e1903061a0103150312030b04110a0e030c040e07031103150a0b010801171c 79
    0x4508201d0002d58482c143d603000050712940f603410040d210b00e335140e10000151604020502055491240043c15a84151404100700640e440403c4c5030001c00c01500c00d040c0101d00030882000484001184540c5a42e825507800210b04540e50301942e10958005112030300c240006804070800301c220f1302c0b18411f0305c10000ca041d81c000302e10200907030205006a0051b008140240a0303150807608140081189240c03892604409850080101d5840781e5540d100752170001c3c41d188400c81c0d0140c0d40e00950b41001c810400c140381c0001015900a0803007003d40401d09000c1d080c605040c6642502c821283c20840d020a01a50000c0840040401500c140d5019944184840c0d02c0c04100b4042c5c541e04c1d60a8035044000c007007003070806241185103912144210700303085031884003a40215014040740d85c00001440c4c5840d1242c0068182107078000031540c9013002c0b50402503120f07030325000403141c24400e03250700180341d0303d464078410340e03903011740824021341d00112403102c00300a90441d61800801c1c0c0d2601c050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 276931061 1250 276929811 276929831
    0xf020603090c0a030c03022409150910050301090e07060c110d0f0302010f0f02040b0f030606070605090312060402030c04060f022b080903090d0206031008030304030c030f08010f1701 80
    0x788080d00c1d081520b40c100111410300071810300016002c0000140488c03020761405a80181403244030b203a03d06401003603480003201c2400d4248040c2c80008074004c00a0500340c0c03c4040c010127030b80091248100c000d040600441c420074001c900b120a841da550303164104a0125222021009200540c41d81c02c07030303c42810702e00410071a02c0781c05101840b035800458480688400396059a4601c550181e8844c81044100840001d04c030464074005040c4840c41e8903596407400040543c0928440030788001d0400d410041c1060011005001c10191040004001d89a150620040b40400ca4502480041c100000c0c044c5500940f031100c0e020388188100d544d80100c41207907640404520310842c41070440203508490b51070300460f0f450380c00b998180045050080c440001040c04807170150290042c4000404680a001007100d04070151021600b141d5581c00c1074600286010450303101540040d10100040a000d4030800c13090b13040303401d4280c00314401e50400f5500c0c0802d00050034402420742d6a00380441c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 276932311 1250 276931061 276931069
    0x30905011b060f021b061005040f02040504060b0903061b09061606090b09010e03070b040305130906030803070e010c0203060a020313050615100f020304060815040920030a0f020603090c 81
    0x14031032043c8081c09a168450503c002c040310800703c4072401140c000b00108103000c5071103010b0f141110f0045030085462a019110003009120740d07048140c02c18205031001c03a000358440018a900402074013103a03a20383e103c00c020015503861504041808034100401f40c041c0c5420006809080b9008151103074020040d03880d00304403401c004046628428401c100241000700784501c485160104020f175103061940d1b41c600e1044180100b008040c040041070302100c04c403200400030b010300700031102040516141d04141c1400d800c101e0341030b4009120310052400a5100349443d10082d0ba010740281403d40340c2e013000402030b40006140303c1c404080d40010101050041000c43c0c0550303100c03400c0d1444021043d050010142c4610010700a02c10564500b03e5041c3d80041240d0442d841c9280850315920303042030300300c52010600710165006081001c0c0e4070a00caa0412042d0500e8a40000c0b4041120741506050f201c42a9880141424911003024409401d00d4001554414064025240748240c0c860000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 276933561 1250 276932311 276932321
    0x307050d0b0d1104050705042d1502060906060d0f1403090a0306020d050906070f0c020a120b060307061b03200d02030d0e01061505090a0f0801090201030605040207030905011b06 78
    0x2a00c2140e80f07440b044805040c540720391038201e1502d01d001c5240a05210801c81c1140c0c00c105501c40025071041e80c4443c1c0c6400c1c00c291005840461007204003c2c05080c0001d5948005032900e030824014030010802c18940102413064803a8000320151036002652211021055141001541400100403520320350f5131b80d0742c860000d140b03e10801a02c2d0b0540906d800119100100070791115071004040c0300745d030354000c00d10403049119440c0c522401052407010a4501d44aa4005943d11040e80e07071141c1003094078056503124200a4044900d61540c3c1d400c2110f502c0210b40100701c82c0508034170030a0110744070b003000300220041d02c0c179002d4041c00030340c1c0080d00c0e1440c00418600160804100b0001e012190f014850071080e550000307020180c141001c00303a1480c00036842030140100080c122076280c076560000d0004198000210807103070340d44c40c00d1901810326071030100d000a282000120702c070300e4036100362203072a909541e40c0c03071000f4103000040d140580800302d10504407038815400703000a0020701072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 276934811 1250 276933561 276933563
    0x18090213080c030601120b040326010e07081b0d090804090603051e070603050a0b0904060e0f0703050c060702010207030605040f06110307021b01031d060414030f0307050d0b0d 77
    0x2003410316150200076802c0540807100c4600c2500b00500400c400041c0c1601540d40c2d40d00111b0a03031305c50701c0303503d0f00361800301d1b041e6039044801c000c802c000303034150301e568a007241210030740d0300c03031600c42d0b41c449104807031084003102d090310307000420f101601142c2984005800e29445640b0005040801074951407840c0d0000d170f02403000192181814010404c040c0705543e0041821050181031311b014683d99615044207001b80d40405036a540001d82040103a00115551074015000f00d01c5803d207410200c002d0b0208007944032a078401c81c0c044802c800000074017401220741220141c04135085080c20030080e0741c0040001d90440c07154400100104005210341c5015512810110842c210989807180c191040c0b101000c4000c04140100108144c001c50001080140d44c030f2440744881c5680e005a005040d013404500d0003403030410300003150080019409005901500c480010052581e17002c40e03491040ca401030481c035505101184100d0302030405000c0728410000040355080030100842c0f108520343e54 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 276936061 1250 276934811 276934837
    0x170a0c20160e0405120f0406030213031a0f06010c110f12060708061c02030a020409172b05072a08120412050903030f0d2d0f1a01180902 60
    0x414002004001c01011015049041c617050404002d60307103078609401a48130348014541c00154400d000a000c1c210140550780c801d0502000000304c0948000d400c80440700c01301c100f0751100c080345107503001e20b00068200e80e0201703055011403803440910055440506d603050b004440c640d1000c0025000f8868280b00e0341c000c0ea548481842c10200300035009029403a0360b80404400091f00b00540c40c0840d417050400d4041d60045094a803a103811415802d58130518003440300d02007100c882041d455414100300e0800c140c00150081702c6080790208032035080e203050011900018080365550741c000103810b1116110070240d40048402d8407501100d40c484401c500c12441044204800c0201c10801d00c0706c40c0b040761030994204400000402d41c2c2e8030510240d020071260100f01d140030070403240c00c550010001a00813000b62190b41540c00d40071b01541200c3d01155041060341030911010b0b20a410944642d9141c0407000568a070064400304211000c03045250740c01c1c0000311b16094207000a15011020003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 276937311 1250 276936061 276936089
    0x4150c03020c090c120907090c0906020c06091f050c0303040605040b1e011a09040608010504020a0b0a09060c030e04111b01050c0d0b0a0305010507170a0c2016 70
    0xc5002400c0146000800f44140f07800000c0c80300e48104982614140c460440b01201e803038880e0b06155241ca0110b0303000c0000c1d9070424007190036007980540c190342121070a0302141c035422104420401980108001d49030444094924085024002c411510035440a42420762030003802c0c0300c6443c10b5500c00c407415075550b034071442031200300080400280e03070007035000c4440341901113094200a40c50b00184a03401079120152072207402c407421802150540070300140b0400c5101da88113001400b8200840f0107034401e10a0300400110369030003100300c8041d4082644d80d10141818038206446d8449151019070820850300b594802c0c0791503900ca55461008908a10740d1120303841001911500f60150060000f0390500050100400701c0c002071b00c0c1d0514400b50b000c540541c1c4080410a5245541c0c00a03040f51300340300900040c035801001c021418075070b03441c5d61501c40d900c0303144c00320907100300fa0041000101e0444140c05840b000301600388005802c4070554038400c007000c108a00d544483c2d00020312860507a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 276938561 1250 276937311 276937313
    0xd0206120c1e0c070e090c030a05070905010510020d202a06040320040e0601120c050909060a050a0b04021206030c0f0d0f030e04020703020c03010c0e2404150c 70
    0x1c030359045448181c0803414907100c43c100580e03071900c8580c403450300c1110305840483c540c0c1d201400107501c80f45016044504804150818960f03030003203071142c0c6101c0391a01d0008240ca0400034a07842d84035203d60000c0c0700c55035880c041128489429800e0f1001454403e4641400c1034050050024210f5803800099061403100d00c500c4c0103800150140d8031685003000100001184c1480d882c840c04a44100c1d841d42180e0310022402900303144d030039500305000d08400800d00b400c4c42c140020007180203003140300189898a0600064910541d05aa00c81e0f001c44000303504114660015036110880e114003003040c1003c0c80101703042c1d8022550003140c45014108028240c2801c011000c0074800459568074241c10b541c4c0070881c1c600f00003002034142540d00b14480107240c003130011314202c5000684210741d281e5450400039110a82d041d0554803d50030460841da249104ea045880c0c5503100501541440c828004e001c4403c40154210300380315142404002000103000c624864400b1041e101e0f68000009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 276939811 1250 276938561 276938587
    0x1d0109180c0806010801050a0b1e070b0702071d0105120115060504050913020d12180303091e0b0a030c09030c090203180a08391605041a0d0206120c 65
    0xf0700490400c600003004000c4e581e6041d01143c02c03a0503a2145075600c81c0880c035950303004050300f141e0156240c8000360000c00c100904000b90302c2403520303600f0303100f205869003aa80f02d050004041e10a1410b07038000140700914125003030814805c541800021454860039000d800f43c1c84035031010002c1500407401f0011070030484840b9601076050b000c1c42410f0700056001541e21098500080c250108a1510200e228020b050b02d01c2025400155144115581e01e001000801a4090076900b03050b41c000c2e110803885010001e10964241c008058100084800120028000d503480c0c281081018400000031a0354500800041d011906001d44e9a2905100501800b40381004900d095403106007064049401d12054419265003460f210310b0020040c00ca940e450b81c8200d40700341c03d0b2280b900042818007070001c2d81c40f148200010b02d03200d03202d903100d0421040315940303280072005541540b4203210915112142c42c01d903501c000c0ca0203041030507a107060300c00180101c4040e490710394001102020040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 276941061 1250 276939811 276939827
    0xd06030305090a091b0309021c060504030e090405070b0903151302010201110a0e0607080906030a05070801150905060307031409010b0109120206070f020111011e050601050403031d0109180c 83
    0x54505014004202c1c1c80080841034021506a0f000309540c51f9010350455584508841241810240c1034101c25103a09190008180542c3c04502046e10a5416820f50600284892060350080003a1000a150680740038842c0d100c0d48185a06002d0780603034242d114402c5150364000d2407070075081c80302c068162001a08580d044602c825040720305210b404070b025441300040516090584000340c0fa0405450804400d0190021039540174002104001c2d100e46568860341c80b84c0180e989008050340d88402405034290b00002100000d20700e84028003450a10800654000046240c002840c03c1ea080c1b42d5144600107480c660016510f80400e40ca066034040884d030080c1903032132402d421340026640007500611030814010080380c90503820b042960b007d82602e40302004140c0003881540351070200c8650803d074400b80a000c051921011030002e500c038000b038030300752545a11920842014205099103100c08e00c95194104a207449010407044030711540b24012801d03070000400c07000007811010f003104c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 276942311 1250 276941061 276941069
    0x30c060d05100b1e0a030603080301150e091504150503010c0203070b0f24010c0605011e15140d060b160605070c02030c1c1a010315020f09040b03030d06030305090a 72
    0x500a2210310818490f801c6100c1611024145d07485039120000c0d0050407240d40050100100440005401c0484d070a854508074404e40e070308030310248131108201034914140c540038200b01020300d07428000e0400354005c0184da203130244068142da0b62880001d096407115420200140c00c04074540c000c0042d202c0203240c000d465036502007240d140001e0400e01071031010b0304800c03030000d15400c00c1e12507034090142030b0300701900208180169a117076100c586491681082549410315840301c00204114226404010300842c0e903140e030035407807001140c54444d0304144010003002d56078050008040300810000c2029081c12140700071092201d06100c000c9a43c0104264280548081c0c0b030001030b503002c5a04004800201e034000072416901d00c411015084481e0010031030484650100c40d40100c000489040764400c08400c0001c4000300e0b010010390044201e1001007000c2800501c545181c5500801d0007000d000c0c0840b03007040c090090000903103007283d0040c1c0c04620002190b602d14109031158070054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 276943561 1250 276942311 276942329
    0xa2106060e06031e0a0b21060f041506060c020f01110a021003060803030c121b0301050609310c0905030a08180d03020c03061305061302030c060d0510 66
    0x15460500e0181c4000c07209103529101d510004002403092100081022080001840f510000c0c84c26011034002082031104d12440340100150452401400400105100060901401c0c103901d41601c44010707a000074008881c01203216610381c1c804c000504c5464010007681d0b40d00f207081d49080c014040c0c03403000c07a60303018100440d9860340d19940000080000e0100d034151018180c0c4100c0000407001082c00d600520380c180400800d1210880c0008050140c1d440c4504c541d80407078440c41030500c0d00001000d4550403d1105000401c00c03860144043d004401d0003414211100b01d4111198a16085034200d10501c20600c1100e45c2d11580d0f80c0c441c03000301e00d485051580e1868280b20001b9601c484034070006000381d90000310703e18401483c98075044110000307450010345050a20b0701a441d030002d01091402403003031000042c42040c0e01c00d1000d20003038110010b4241a21051a5410a00324070b0200360303098807452a501c0d82c181c4540c00140304060f00d5100000709800e0030307060f15030404816400081c0d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 276944811 1250 276943561 276943571
    0x8030a1107120c0203030405040c050d0e010b0109090c051306030f0617120306040608060f0a0507090302060a05130b030a020c1e1c0c05010f02030603010b10051c0e030a21 75
    0x600110180e00440314107060503d0707203081e944002440c1d0b104641211fa0414180304142c1c42040d004805002c94240d0900248402d9041c0d0704290700b2207107000d400c140011303174010041005101d20f60091542501c1890503c1c54901c440615600c042c1c0c0c10380c0080d001950356440c0c0392500409210f018054138803a151408180004c2c0380003a0789000d2003018030441c40c000400f103038040e925603114074000c00c12801501d80516041c01040b10001003103070081242c42c14980044c0b01a8403680f03c05007942c0c0c3c020310444c1004034003c4200c50350381004140945041003840040350205141020b940f00f159507030000f5940311001410347d8201140b0b030180100d414841054141101070206095207082c40300940f40310304824440f8120f400008c00d42d4050b2030741d40382c00c8000440c114250001e510548007500244800d01e40c0100b400342c00c80761404d40f840010014001c0c2040080300c0206142c000480350000f107003200c54080f6140c1581c2c0032581450103c0d00140b00c580c202034841c84541c201d09425042080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 276946061 1250 276944811 276944813
    0x9060f061710061b1a0405150402090408071103060a02090406060e180405250303140702091f080312040611040f03060b120d030e072310110a08030a1107 67
    0xc0ba40007a018240030320010b181c1a00f07140c6901c070946110b054202410308100c1d01c44a100c0c0042102c01e55040e9a1070140d2024141c070105601c0c4628016540900003111550391a160056190010780003181c20048100c40e0701916541086214003486d040310005a41e241205c003004210740362079000307105115841c4504552a505d0301e00054100c4aa0306400c0002d81d200e2802c00d042c01d101c01a18005245000d41c03c031012042e1810150907a4842d49402e100000d100c16514076034003070f40c800254040300d07003000261080040c80458003074405013400300c551151541111421908005014000114817408210a1081038020b01000071f2036102c10b81e25060803ca5480001a141e01000c2c0c0758680700e2800305040e440d044010600280340005955041c03244030402005445c5028201e003c80c0b08403000496003682c00b10800040000c94066529014158024021181e195403c240c042c0f040024000c06801c006004020707a440c03081c21866500c1c9440044001260051900030842c620180000c034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 276947311 1250 276946061 276946081
    0x4050c19050f101b061401062a0309050a120b0609011206020304050c040203011203030f0c020d030e07030c0b1c093203040b09030105160e10050409060f0617 69
    0x521a0001038034080f0b00301c543c908007501d95134076020f0003001c04800003000d0014848254400e50b41c0c030f070b2000702005080c1d9983d0350403240c8101440100200743c5046d2041410320368070118010759984a070402501c05a0b80e03c00148141c00b8542c441c2c2c0394038501110f02c200304164044029802141110110b840f9410700030102c4175168242c0d0020031065002001c02d06110040000c961240301c0200155601c0d070b11074070340180c0d85600140440c042800c12503602c4119020f400b0380a4155029030080880d501821001c81c060301d001003420015009000c0080041149810000c0281c1007004c6d2141c0d898549105c4411060443e280030592107107005510b800160304400c00710f02801c40ca2041c001000c20712100c0d02008280450500c1c541c1c4000034000904440380005081400e008800800040d514010000007000011107044c0018150480742c202c686400e0390340036a9400545400b07070810f070700d5058601c2140c103503810055141c0c485000801034254081c05c0c01c9814560341503c0341041c10011861 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 276948561 1250 276947311 276947329
    0x8060105010f1b03030902040b01022e020f0c07030209090c030709020a110a0c0503100e0d0f12240603090c05130b030a0f0209100311010309081204050c1905 69
    0xc1030420040782c680110035072150140d022003050301881407100e072056140c058020035680808038040c5003041e407100d0042d0f0001c117008050911140c080d12038031809a090f175104072003403948421215400e01240c0c49a406940151151502400080c40c40504500420220b504000c1980c00680d10924004d115a200480e07580d0448481d41e4000d616607404480c1500ca10032419045407492044210420622200122034000c69009809139084410520300080580e41c600311b005010f5807140d2110f002d010302c0b4040c0c40d10403584520f8502e2200d40007028400542c0c2e0f1070a10302c9a6400c2a00043c1104056501508010586400c0411216607a62b840b098134000c03500c5210700c540042c1017450400c0c45190004240b400d001001c0e510654081c0c5840171000d041c40740180d02510420300000d480e902000c124000740c0e0380140380d41340e0b81695032004601400c1050301c110761052007030012100c007125440780c2d14003e62080e00600410705404040c850010031100383d107940d89403c00420803140d2101004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 276949811 1250 276948561 276948569
    0x5030706050a0b09280623040b0607060504050c040e061b1b061503010204031e03030b10020303190606200102040b030c0d0c0314011e03020604090213050a080601 71
    0x407405950301e058000040440100d200d41068114041080040001d10a6400180039408695140840e5003104046071501d001c2c2c0801410b6800b050107544039072101080080c02c0040020401c00002c01c0840c1d1315400030702003250035644440c144400c002061100080400d42520100700601c1003d1040781d071160080c0c4124000500400e038040310b6189101240c4080780400c0c100c1d070700c0100b21191540e8804c000c5406a02180c800812881d003454113000715402c41f5080003422880b020a103c003126034045100c3e0403018990f9840d180701c800d44a01c010248100e1464000d9a1245090f092040c207202188503600c601501d884010301c107041d088100e5801c2c55403020f60341506106c000000d1740c024403c0340c1054652070004001c101d0060079001c018003565035640410300801c110260207a080d07aa8083c4026105903410005008000d0b800349040c00345421040c0b1031b156242d5070340104440740c2c843d070000500e0540000c0c1d90300104064000840003041d00361081c0140910b4050002c0d1146010b010f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 276951061 1250 276949811 276949823
    0x21506090f040818062a06040b0106050f0408010609020d0b01080115030c0c0b091c0804031409030c040603060f0b030c0607020609010c0506010e010501112a060729060904050307 78
    0x20008241480280130b0304050001420044d0b6403451409512241141c107051441d9401100b5003005400c8008505c040c000d542c403540d40412642864415106500224000346806805010000d095a400d0080300f0082c00c0c01e0348010381d10301e04403d41401351800541154148004040100b12486548002d200500501d1500180b40d652500049070000400c13103020b00217071018814005540c0000c50101d0340c2500f4606254003504c030b19002030302d40d58030450700039010641051814903c1d01c4d07000d006000d0fa43d80241500c405944080002e0200d03003a640003555002e990f990595200c00300e5118001002a0450003040058254030000340288642d40340240941302c041005215079029a00c01a01d00f90b0000a031400c07580c40d0b9a501210003000d11840c7d0000704e008040c140500000f1030254044e16450390708594002003454030f007080c100031231115600058100121008203065400303888000303c0c2040003403900380310105154002c401c080d00491140d48070714280000250004100c03902107030702c60 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 276952311 1250 276951061 276951067
    0x315220c0e0904120f140c03030a200711060705010212060a050d0b0c07061508030c010c0e1f260405070614041e050d080c070e060a060c1103010606021506090f0408 72
    0x440c040386c040d07002c401100748008010804044041001c80a1446843c01e032004100000310010b074007006c03003100d04030300201c00c000300031031008034280701c0e46500e0002000e00028034281180d0350701da00320781c012654030301955036002c03c0c840c007840c1644105000303100c00c9030710514070a01621044c4180102400300028000001403410030040c20ba0000d1076110141807041c0341195507104e90b00c0d120f03482110f84101551030401c00507000d80c001d041c55045840054844000200d604103140b0a03076010041c158103108030f0410000d0600800d0f051100c00e07104809a160310360416142061800300d030750700301100f40403049110544070200b24080d0745c110b9405000f4510801483d0300b0880603442035070407040d0014040c654010901804400400482d08008102c03150199104c103120113000059501d1540810070b40402c01c900e510501c03680305000d000d0302d0090340071007440d40040d007100c18071340c04503016030080c001500341185000c0b040340d40100203444141071460441141c451042004200920180d008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 276953561 1250 276952311 276952337
    0x7090e060a0909150b01050711060304060e060907061101092f06040b0306281a0409090b070f08010803030c0a0c050703150b040b060315220c0e090412 66
    0x1514000140240101003001e01c2036810020840c03030039030307050f5085942440b00c01c1010794807e4084600382e58202c0080d2580b0048030040101c141e101400560f191078a81c00c00060b001418048c3c0c500401302e01008044e10351174018042c0036050090140600d070b91420b8110702c08600c00045803c2030300f10b400c2012103002d8124a105070309281c3c070081036810030b8012030b0110b004e0050384011409440220b407900c9040c1410f01011200804052800c054a5404d000c00c0000d18407021844e2407151609203854100358031450850b0844040b078405540e01885036003070001c81e0790801030340200e10030b162810744006d60600700c01d2696807001501c0700103508400541032250510441440882d60f5108017a10071544d502d09164079584002d00d29242c81614251042189180c81c0c411440c4004018100340e0442d80d0307440050200b640c800110036003007200340f640281442032546080001091140000402e9000740708000d00c40d40301c842900780244000e9091001194450403002c0400341c1c645003110501c200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 276954811 1250 276953561 276953569
    0x70f06090c0e010b0414030d0c030e1c08220311060a050d020a020a05010b0301020c1509031306020a120c0206070b09031b0a120f051209070e070c02011707090e06 71
    0x110303480084001c0b00e4000204003462558020b008903a035a100401e803c144c51000c064a0301c0403d0380c41c0d03000c02d0442d1000c1e40004c1c0202510304110030002e0030410071403904100e85a1440650604840c8240c3c009159090343c03d00d0303003290302010060101100600d05556403070a1016508039900e1042c030f00070a104420f41d120b84103c5500310502c110a545440c00c1d0600603540d0014900d04856950900311031051a003414400d648000c6241d400400c1c44220048904003840805000103180e404104646019204861a01e000502030790780106100d850780d05107441c10341213103600002000308403c1c410f0050790701c10742500c00c45a08010310103190f03140c9004407495403083d0300c5024510b2007640b50038008031102207540021940268000c9192030300914080341c600045504840100b5002c3c844070103800740d6849001d9019150004071812162075a0300900c409130102c0d849000514000c40040440d42d0140d01c20304141d8403218403a0070790400303000107040b601c40da0203956804e0303d02c000012001d62b9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 276956061 1250 276954811 276954833
    0x9090a06030b13061d06070807020d02030a0302090609090906070e06030705030103060b1f0207030507080118080f1201090e0c01141b12040f21030509060a020c220e03070f0609 77
    0xf5200d8003a101170f05008074a80c807850100c41c840c0110343c010000603150380c0045003181400c640382d0702451034002c40d010258000e4101d03119150704031800388150b02403034455412030303805a83d8030001072600b885c0c4803000030100254008094000c44040c01800a02ea400c102903d0560f1741c800c0020501890100100c0c42580949a02032103101041104501098000c01c01c03100b642d007e41c050765802a105d141040c20303501007015084103190848035001c003050304600036181103c8010f010a00d41501201001c0142c502a00196041982c8080c1c513842603004000b41c2e81f8041007802e048030000620805117195011b6840302d10210391244040e4900c990f01401003125080d08e40d0f250b90b40b074a07160f200fa20181200c030700400c1a9880c1e90180e10420140c803c107010001a403596510707141503800c8080c828203800c1003c4940c1584110030124035940c0d14000c1c04180420300340003002184074040c03104c10942d40a008840c101c1d800402040700480c0265074940c03201908800085107030b00b52480c7c5056400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 276957311 1250 276956061 276956081
    0xa02060f12130b070f03291804020906060a05070c0608011d070206070e030705030105160201060e01082a060a0c0203060a1404110a0806040b04020f0603071707030b060f09090a06030b1306 82
    0x200300250f6007011040f47e81d9202d480c4009554402c111201042e280030054403c0d03501a6100c0c1810000030307224688600200618082d901d800f9040c01d450f60358000d0f00c44455005031000c20481d4006000d00301c1e201d6030307000c040104c0f501c2820b180d080010002e521444040cac00340c1c3c100309200351050001e84041240100408000e0001c000a20700200024881042c0d50114070040d401d146c400503184481c083c18a058807045000303020b028181e2504d5400200190124061490148660022680d02e1901900c645912500c42c4803850206e44101800c00304010f083c01e0003240350002a0000082a6038aa80d0242c0d0040d8103408011001d00081e4501e541c81d8844a071600c2070900300810003e1030004980102c0c030030364000c00d10036401400c1141c0d030f00040300d5050008001072540c0b0801803115440a401c0121030030001201041400421203960080300748000028000070700c01c0700750411003401d55200140c15407c111186c1075650b000c4121801500303110459081d100380d0404e00541ea070001d4005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 276958561 1250 276957311 276957341
    0xf293c061f05070b011502031b01060e180f0304080d0e060903030406090317040303080c090a1e0314030c070b0f1611011709030412050a02060f12130b070f03 69
    0x1c240091030003045540300c884221102c88803e000000d9020200c08554066202c40d0040c50130300c42c880490038180b20f44408458103035034031070b80002420b58128044a000707958405105014407010180680744c140000300300c1001c0da000308001c1148040100c0d5002c0d94076021b1078034641561051001072414000c0d946000c1c1d041c00002400140150045031480c200e03841090300080804d80c40d0030800ea580514030001d0b002c10b26200008690160040081c00c1500b8010000b4001c240c81e050b03e403100060b03212841d2150029040705205001201d02d4107510070749130b80c004603e0880c482e1015034960040d4480d45003414008101094030317030401010b54078041c401c490035040c484200d04195034861007003c0902d0104003000010b0074100b001d44c44183c071a2285c3c078001e525051900e0404010300c00d044006888900440d000b40e00107a942000806801c0b41000d62075071134005134890100d9000002d843d00a01d07005e0a82000005000c02c0d200303990081007420203110030201814150042c00d201c034015119 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 276959811 1250 276958561 276958609
    0xc050c01181d04020a0e0c07060b121c2705190b0c010f060801020313021c0204050c03160203040810050709080d0f120204050d0f293c06 60
    0x40c2c40d942081d01c0c4a1402100c2130803141b42d0b280740310185114141d80d103680b4100e00300424400300741e540e040181d02c1e1402821031001e44e107403c9002070502c2030f1264103001c440c0507640d0494985078440e040d103810014242d03404c2c0010856038802d0b60300b62000e01c00c56028604140781c0f0315815014100c204020400002419500d00c600d1108a00904025081e440202c0c039041003c514010144242c9103d16805034100c850f0940c244c080040c1c840d494880001d04100c010b804000584440c00b4050043d40d540554540340d00b45241c485d00c21044031a59001154070900081118000c0003036845000c2d00d0311500040c0d0358a03410703000c030303071400706508440c28501c5441000c0340555403140344403108450a680340c0320ba010090035507105034031407031092940c03140c0104c00030400300d204e07070000180c80c0c0e1060307941e00900d1154481a080a000101d011454801070404001c1035890084d032004480ca100001d003c011100340b00e140645540001520050f804000c0000d00329480700b00100c2500030005030a0b10b8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 276961061 1250 276959811 276959849
    0x906110309093909030706030e0c13020c030a09080d0c020105070f02030a080403080d060f05030a060e10050103080a1103030601270b040b090111010614090c0708030a020403030f0c050c0118 83
    0x1080d030240c0c200074080e11a6070740001f0380d0b921a00c200404420b95401170658002d1040801400240115190560642c20011012189000c00092001d0181074592201c2031f45410b03600c5042c44040d50030ba1081c40044040c40005030fa10100300e45030306a000045500e688018008249460140c030740040400034001008400d00400001900030010100c0003400440c3c3c44403801864282c0600c95150160700600036600000d0050700300d040c1c04d03050030003290242c0c0003120500c002d48000307a10075141c1020025401d0106988000d440440c601903c00452031401c140380020000072114601441080c6080e046545010034080c801000388100a101500c1e2500c070742480415512140700035001c10f2090b84112003a16040c0681e1040b40d40b00c00c411688900880c040c07112010307009005800c01c0c0410818580082c03140c01c0914010070940c4001a161411440d003c0d003c070025100500500c40e440c250800043c800081d25002c621003807030205080303110141520045052a0044c10000f03c00c031003100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 276962311 1250 276961061 276961171
    0x2090d03030902030105090c03100f1514030f070b0d110d05070f020c0a03020901140d050307050a020f0414010302010e0102101803080c07052119090611030909 70
    0x2c031980203c1c002c20841e02d640d840c666955950341856900341d003000b0680c40c1c040401340d20076000b0b0114043c011802580c030504224403c0c84a820040c2c4c040d641640c111034500b810094000224003d2000705901070820068280d0343c0601c5550b08602c5403241011034032024044c00f6103042495207032080c82941450310000d0813400c900003100006100d82010701c07440d071400d040200f048a40260409081c3c1c1d00f40306d141040c03041405100ea03006004014060000390003000244080380c041d401502400080748100052003214503101440340e4146118010b4100308042014112a4242000c0303003011003800040c2e092a070905042c6a006240010110240900311501140703030b44640d84400141c0d9940a24002700d015240300a00350b035100c09004460300003085801c401011a5440d041d080c400c07100c0508000340140046c140c0020a04a0100100c41d08040949039a0744502e0103103003030072007400114196010003007542c101800d100e4a014403480700151102c8007001c07000616940c81c21945030385 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 276963561 1250 276962311 276962321
    0x50d0b09100b15070f020d030c030311090616061d01060e090609030304120203070b010b0c0610080a030e041b0504060206150f010806011e0201060311061204031202090d0303 76
    0x900ea81e02890300e46003200c038241d00c240c5003075240c0207084000100490461401a4000c1c0c4d0040f160194986400d00140c0e541c16007840c010391003a234881110383c0c4180381c01010f503090096140c00403081070044141941c0da80c829104441100005035035408901d00703054019184440c5200c210200058100390407140c1074002100307550000c10740780415260140701e01d1b030707919003204c0080e0250000c1c400f03c0c0003c1c509410060b445900b0b81b04490809409072900000b4a100382d021011582c000110505030400c02e01115034400d072a000c1c046855803414000e070391601a0303002d00134204101c01ca50000180d03200d502c02100c881074402001711803608084080c00c550311901407640507200c1e840000310900f0682d1000c1d8410701740684507003446058000196245100030f003006042c444a081c00341e03801c0245801d000d05651044d40003194032072450402107580110b021800d40105000c100895207020742c1012240c015a242c0342c21032044c965644138100902070001d0680e03118000f211050189540f54000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 276964811 1250 276963561 276963571
    0x3020c040f0e011401050a0e1005190305010b0f100f03020c010c03050f0a0908040509131401150b070c06050901051309140a09120e030721030201050c1c0b0109050d0b 73
    0x8000d1100c01c00c684c021541424803036194070960300d9000340918036198881c0c2d50072444214016403203640b54000a540a90031800e2041507012a110420034000c09002e0f280b28010b054415030201107000d4003042400c000b000380360003480b1081a1400e11036200703a049600c402c50300c01c001c000c0803541c1c10004000d40070a40305000b403403142030045110448640306070455590b02500c072500c4c052410701400041a001890801c42c54101125000401c0184040c40407400801000080450064168004c178003016085680030120a02000d000203070744c03169420035200170b801d05d0340e00c458540340100d459201f0000c550030340c41420a400200c49016800c02d400c0a454241c03030b0400d0703940e016010300440c3c1c11f410016007100c00d80103400c50f005000e81341440c40703e200a015102c1903038031a1441c664a011007144d0000309445075104100b456420310035150081d205412080ca0305a492464a4030f182d040030401010595072180c506c4103030300940303050006000281c908822800c440c18030204508007110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 276966061 1250 276964811 276964813
    0x9030519060b10021009030306030f0c0f1203050405120309060f041401050c03120a0612050a02180f15040207120f0230030a06080f0607020c180a0903020c040f0e 71
    0x410b04058644041e448048116540c014025800314a181c0c0024215003403007902419540e000100106040c02c40c490b0b01180244400300f071851500300c0d440d00c900019840403481303840c1c81d4510000030ba806421141250320496078007a10480f01c060031825885100c0c000b6a000d00c00040038048094503402802c200c0340c40c4a448441d114a80c4015240c074869a9803a1045410800001544c083d2440180341c0180101000044c1e854031001c648060600c03044080d201c5500c40d10340b110031450158070100139408014524031003070a244010814605000c1c02c4001c0c0520710003451005916258166a81d0035003210030303614103c10480c4003804590750301c02c9020050049804000032400b60f07441c01c1410315640c482005030001c6165030404143c002602042034141c6a00000172200c0c01080080c4100c0310f907030050091800c0c2200040d2401c0b1016940500452034903018901404036075000c954441f094403000b040c2685185000c906000c2144080e80d4400e2070705491502e03d514551001080c0d41e403503c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 276967311 1250 276966061 276966071
    0x320040219080106020312190b0a140a0b07081b010b0618010e010206010803030a0c0509130203190b0913020301020d0e03040914010b041401020f0a200405060f010f0903051906 77
    0x541c4c00c0742c480c418156494407002000c0f01003074101c860412400040700800c2d00000e0b0440d102c3c8000303a11100c280c1d000b000721203000e44001005207408154600140030070240c03a454542c03d95183c105074000d41c000e6101c43c4010000c4210b10070400c1d009408100340040465903280d030110f295180c005905088140000d01920303007004a540000340d1903050740d10340b000450071551508020fa0180c0071840c00c09041081c14070545405840d10460703102d140608510141e168036101090045c04901030f020030400301d041a4404d030b01d0b921400d8042e40c212031800034041c41350380c00d800424064419038a00f403034070318900380044d980614040041c0c42034a030144002e01491a01d50302d100000c0c402130050200c1e10004100402c00d041075480400c00400040c019a0410b262141c2a241001c103000425941c000c1140403c01202802582d4221070703070400c40e410010ba0820a020829081d43c1c1004181444065255680014007550342c5100451f030110480e0b4031602e1101710b2505101d41114115003843c206 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 276968561 1250 276967311 276967319
    0x1b180c1309050a0f020705061b0c011b020105130309030308060a0509070909111321050f0307030207060f0509040905010209030f011b08010317030a0213090209030d020309060403200402190801 84
    0xd1700071035910300e8020005050b42d4542e8800c005c2c25500f020311501144100b00300f2038041140030702561249900840c960039001d801000b020b030a543d0004c040d40c0900181c14903c2d00001c1e017014550055075050300c2c0045640e520311012424442654005a81c0b013034540081254065200c58050282e6008242c00c0c0072160140d100e40c200c5010f80b0704880342101244c1c50501c00405c1c18203858101c4c0c101e52400003044c152070b488841c1000c110440d00d80b030701d4000040001c14036404200c00c00040c00c8a10b40440d02c40c1d00316030003c0084c0030f1200e410f841152181c0c070407018800250140d420107000201560346086000c90303628001c00d0041a4541c40c5180c280b102c8100d030b4003c240b0941283d4000c0394103001100850019402c541c4010f01c00071590703500380460000710a03070107080009017030100720040c1d840414004243c60540200c482600b194420010306426850342c40c15102100ea10000076502031a8034255400c105020941d8103810510115030003000c3c0154811030280da4030f0a40340c286060340c072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 276969811 1250 276968561 276968591
    0xf1a0f1909140d020105090f1c03020c0a06080c0a0201090206030a0b040501050609010c02060d090b040f0209092107060b1905120721050a02030607111b180c1309050a 73
    0xd4818981c3e0100c040d00301c05000d035000d00c000b8000d0500c01070001081c0d91502c00080c20044030219003d40382c1c01a240d44900b0540c042041001c02501143d9a8200c1d61070448010300c800c0005101c00142c010200d180512035000b5000150803a03801041aa100c0c41c060388500010408400a5031046e802c100c0005691b0502800f11008840181e40e2a414101d641d02070058552011540202c401d40c0e403081d06c0e020510680d88140200d1292440ba14245030303c1c0104810008003501a0400d81c02c1880c8400c4e491070781d1054801c030561341850894030360b106414400000c20510018581081d2604500040300d0340c60082c040c240c0d00c085407042c00d40b10043c5211070360b07001180a40090542039402071100d03c0480c54040030a28450740407108842816404a0b00300ae0b0305690450211f01c01c4114000282c00230700203030701443c5243c0007580c040340e4954001040b41c5070321203410003049420408a0690003151003140c0036101600c00400301c040d55620780c60300420007120b11094407450040180101a5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 276971061 1250 276969811 276969839
    0x3121514010f2a110102160e0a110f130e010311010302031003080a120501080a2a0b0c16090501030809100504090e060901050906010f1a0f1909 63
    0x416110142400c40c018001036880041001c105001c0c444000d2008040000002d0b06807031090240e2041200005246000411200f0140b030150654104407401100105c0400018007164002c4409141680f20300105130003c1000101a03040e6000014a00c0000b008080080901c2074040302051002c0740d4510900301c0320442800001c0c8601d00000000d11035620903005150413000e10f01450124996a5450321404d500c4031100030085800d46554201030040c1c0d01c40e240c0100500c40240070501c10603691245800038260080200b4038407141418102186031103490040d0621000d610707500e140c0d4080c0296110600c2440002e500c44900001c601420300e4000c050480b42e02041850610715203104109080c00b50300112400c02c801407000081c8219540152151008010301601650501e419418252034005000007001c0e40000010003650410304240c5040710680010810383c0d925040c01c1c0e11652140c0b1046581c210404200c441a106002641030241c0a187d10f401400966036012a9100c407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 276972311 1250 276971061 276971069
    0x250c0219062307030504060804150e060711010c02070905040c1a0403150c080a020c0109060c0c020310061a0c01060f0f0e090c060f0c0c09010803041809050a03030e030c0604031215 79
    0x83d43c2480101f0450780240a4a03800501c50b286152808811110300b808840807007400c1103141e4010018001e8403900002c0c3d26940c407000200900202445420103555100c152007504a03d0355039200003824001d0000c0b07880301070402d903103080d940c2051a1562400a403c00c0c00b058560000f42040042c42c04004d1092001886241c0c031001056034501d45a98000d4120101c0380c0c01c0c5540f0390482c5000135a403440741d040905c1c0241c484060f0b604450040c9443c1c151440e4080d8070b051b10b07250707043c00020800c80030182039086140070f0030b035071f205038a24090240186a1107202028000300000c03450419111466095030fa144181c0c1178243e0740e80041540e903100e2400c1198201300104200400e00c0300040003420b980042c0c0e0100c07602005100b001c80c500140990190003580c2011409110440d40010503607001003c658092022000e035880307190f207503542000c3c000c0074140e0300c100020900d0070900c1910843c07001d80040c4c580c5850981000f9003000000b520000640c4d10b40041e62490502c003a202005071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 276973561 1250 276972311 276972317
    0x5040c050403050f0318010c031707030f0b0d110906060f180112150312090f1d06061c05060109031b0602010605191505040f030302010603030206250c021906230703 72
    0x5100d46c04d00550305002617050641c2041000241c00503000850110740340507525954002171408115a1400c3c01c40d0300124000307201c0c2801510080201d25040360a0f0f4035900c2c21030380c0036041c0d01c406000504510440e00030f02120702000c60b211441c00c0d035070b10b01c50f400c0e1a001c0e2248281c03201946141d42c101d82c1c0b201159640355594100a0000c2248101542510211030501030051380c0c496018400303541403a803110a054650007903c440325203813004901d800c4501600c0542c00d2480041c210b10380c1480e0349945061699490b03000441c10b80c03040902000442d00100440d08071094142c041104003514051840558203208001505042a403100040c4003044035600d10710606080d0342c00d00310360b0128410030400100307220100d50a418003181c1e00c01540710790000202240765281c068140711005002e5105100643c01c84401c0740d543c0c4011001d04401c9140200c81c020b92840055000e018562442c618800c45d0b00e404600700c0c3d00140e42d03000c00d1119860203000c4500044a54102c0d214807a801800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 276974811 1250 276973561 276973597
    0x40f090206160203010b0a0e0105030706030c2703060207060e0708030a1b061d0303010807090c120203190e07051201050c12040305090d151b0509011805040c050403050f03 75
    0x10307115164102c20034680f00500110345243c0400005110343c005400c000e01131014000100001e1804124140041207641000e2005c98200030021b800c5c450000f885015050405d1810720450f5011b80341c11703004d5035020340c0c21901c85405003400c1c0010404108140c440d407180b0400810790f208000255001c03d02c00e540c511540c6a8454882598100b0600c41180c40913125034000703002200076004000440c55000041d6200d40c9807103400c5c2d150a00942c40311252a00c0c16112441c02c035409800602050004900581e407030b202c80220910004501c41104291031626001800011000c202c20048407400c842210840803846000d6003242c03800d4032001c028900401540f600300b41c09002039513016009041c41414004104040ba0000c2c00c80e0000f11503048144a400d40d600c00c00d40700f200844920b200580c000c81c82e01c0140074009104d1544414107001c4680d0151024140d1240110040d0802610502c240c120611000e05950810700048585000345144108284400010b03507400503445203110070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 276976061 1250 276974811 276974827
    0x10f051e0306010801090323030a09150905010c110106180c020a0b0a06030212030307020d1209020d0c0801050106170106030506060f03090606010f02070b0405090a02090a060e040f090206 82
    0x401062095010040100650001035955030610500340280355120002c01c1e180c1e882e00e4002d000101e50001c0e1a8201c0410040e0b80d004292501501d43c42403d00400080b40700c140d0822403d80c0c540c80000700d60060810010008100c4190020503858085840b40d81d1104039040ca014203aa0203030042c500740700510101400d03211300075004051a481c20740156802e03080d80ba1100d40c854501128586051074807040100f04500380207031413000c408032031005141503082c8480000e4603141c10b9484942004603900344030403446484d92118031002c2d40200001354216451820030010441441100c009520303203c00015614001e0081e03002032100c280c10118660b0038510240e0081002038001900180d00b40201c824950f4040000e6001c0e2000b000204401e00e041c000061507840c4200c070840440d0000202000000010030070703035050754402c40708a00282c0d1900c4591000303000e40c0d078145070b10410403172000600e1a04602840d603c2003042d18240154440d60f4041c0c410b5900a4000a420442c1081014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 276977311 1250 276976061 276976069
    0x1712070201030207290604050c03040b0601020f101d070305070303050310050406030f020a0b090d03031a0a0f080106090902060913060905010609050111240403180b070201020d08010f05 81
    0x8040244141001030034020382c1c2d11180c0744076005060001c03a12800c015034031a0340301c00403006036000d039003103074244041e140030600440c25000281c001400c1c000c854011440c168000c0c003180100c15602400c40e038540000032800000303051412114444407859841075885908013041d10700070f0b130b5086002403110500c0c5581c22100d030b0340000c1280f0321400210101066a40e80d43c014032009602030b00004e8003004140c01040740c00a0160b00100800008001c028460340303400e02d40e1921244c06041c0081c84500d0824160b5008000f0b152095004d03001910101d01c2c0340c0d401980e101034400200c0200149078a4008542c21101003004c041d520280c28412241146071a00c0ca00303035140c11130390300071852541e91548442900d5007070700018007140b138881041c0819644403410000071002140100140c1031031001d18001c0fa21900300000301c9000d01800242894050301c0803840fa03882141c49040c40903641c0548046503004244100c0c010b004d0521801c1d660fa1080c110705040e240c3d41d200c41c103180b515213002c01c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 276978417 1106 276977311 276977317
    0x90c0c060a0c20010f09030207081c0c0b13020a08010506130603111c121d01170f070c0602040b030a0e2107030c02040e161712 56
    0x5001c16500480c075015551074400504441c50f152006a809840d400d00051201c50400180d44101640003501c0c004507000382d000d81b0303460a2000071540c0e0080c00c0c00b4910002070200c03035402c3c0202d5926010941c1012604540c0085d01703605d60701084109456501a01c001d0359140c0421645003030254562640b207080d00001c0014a0540e0303101e0840c0b10010499030300072100808810000e0f11035105014007690004400c0e0310b08500351780c00502da2480c6500310f0108a440d07541c038800c00d5004554003003142c0981420340c003850b1740301982041c250344024065400c10580414100124480344000c10142c0a050f0880c1e94925100000f0000c0d2000d440c000a005d03480000e90700748910105048a840628016030182d0319825400e0842e0030136840d0303501030341c0700c1c2c0f4010151040803000608189560002c0c2c03502102d0f1aa240d01c600500c60094030f0302c0f916500038048042c00d0f03148000003 = true := by decide +kernel

theorem cover : BRFrame.Cov 276798561 276978417 := by
  have h0 := BRFrame.cov_init 276798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 276798561 ≤ n) (h2 : n < 276978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
