-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1015
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:50:41.659505+00:00
-- url     : https://prove2.me/submissions/5ba635ac-1dcf-47e7-a39f-3a38e5a03c7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 182374100 ≤ n < 182553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 182375350 1250 182374100 182374111
    0x3051c060305030c0d0504080d03050c210f0f0f060603040203010603061b09080a03020309091f030308071107150e0d0203060403080f01120b070f020a0c0f082e09020d0614 75
    0x40340340c0007a211176004800740c03425964031500030850341406202c02c4000c3d16004d000418503510402030740350581c007500c0751200131070103441c0402c1c071604184490300f11900c5d0042011040c08107210038444a0782868102036000f28045500760303240e44981c00001c0c010001540010b11151074412804031006036007140f000c06100c40e03220310510642c1d4416031501c42042000040045c1c104110780041880d0850034a5000a00c40c084092000340718900340003102c04580040c0d0110b0b20030300c204000300358499104415007003404003420a09180c40076880c01b003442c500001091042040e29042a40c5800c5900025940c00074115402801d0504014000140503200c103005c08900341c0001c00c20f40500843e40c41c286038810a40310700e0f07030742d0108102c5140001030b500d20b086014180140f00803542d0991040c014000401d80c0b034003070701e1a100d4443e140c150032403010341c03244011490f90b842c1c05003404072403004070752582e4020650110501c00035030703100f03d0381c0801092076140124803810000d18440051040c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 182376600 1250 182375350 182375353
    0x80c0a08030903030405041806050405010605040c03150e090a0503040b070c2405070c051e01030b01021f02280504230609101b060e01050f0c0703051c060305030c 71
    0x11619803504584910901d0709098040e442048200814100743e882100c1702c401203580c6200302011940c61130250344081da0300781c91681d101c10041c0510301e0903124485049201c1d081c20010f5a0106411860003e01c078850b03070440c1c0c0100b0700000c440d41d4060140a0026034000705403079880d5110741e81b03000e16402c40d0105070341500e4800c1c0e0104842d00314007261b20000c4900108144040803100301200d2a0b400801c00329801c03481c40c2000034145d15845100f10101d00c070138003880e0380c100d4540c00040488000004641c11588030210210780440481c42000f40c102203950056a220121645010a00886054040001220710360700e0005580039000e003003541d612028800000c01000039946622800c05103407a8000020000811545841c003000c00000c101800c0040600c100002030307000801c1d6928040d115180c840032a441080f1080c4145540882100160012801c0c8902595198018008010203124000983c02075156410101c6070142030807201c03c3c4113043d01d0380780003034880c1c00c118458000d6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 182377850 1250 182376600 182376619
    0x40e01080f060106080c0a0203071202010c1112270901120606080d050301090b1203030109091401060b070f060b03070b0d150303120c0c0b040b070f0e0f210601080c 72
    0x9500d80452850f04842d041c1c2d541007055114100102c9035940f00c8401c1000307512082040e80c000582c14420043c040040c0d0b000029880c11401020f400b0034140034510f00540c04c40110441c42d09480b80c26500d104859552024100200c1c500c07980410000c21b005d00c2d802071550000007020f001c0c5a80c4030400b05d2007130109000080d41c0d80c1c10b0b00e6861f00c03159070b0f100210f5810300061004900359440148904001003c08080004004035a0300310b602c01e07041181c58944904545080c085c0d06220f5840c41d0035600000c2050520f8091880d03c54041d41100401051002c1105070600c5440d4002168900c001000d443c085540d902c0036581c180d00c02240144054140a48101804a040048421a0b806842d070416941c1040061f000520601d501074051000c908061404a00103a81d42c5100358030a100502070785c00d00900107820102502c402e4801c00001c015900450344508800c0118500152002c84a41c1d4071070100071101d078481e41c6181c000e40300f5070000281030f090000717418004c40000c0d01c02402 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 182379100 1250 182377850 182377873
    0x5130509120304020a030305070206280f0504050d08070c08060108010b010906031407030c110313060e0603070c12091502060601080606040617090c060a0201051902030f040b070e030102040e0108 85
    0x700c9000071140030354003141010081000c24001d000418441c0d00c024070103031605200c0014000100148290822001b0042c20712a0595270414410400b1920750b00340b990805151400042d0741c0348a9010003000d410011802c00c007002400c0d100c03903026050000540e600742d0385600c2900d00820000c002d060015401950009119000744160381102c040b80c00d20a0569030380c3e540c00d030050f00700301c210034040007444805000d1440092000e40802c000e4110301c0782400c1e142c034100500c0e545000554600c40d10007007045c001c1c9290024071030200380b0790056045121884880083d124001c07141d00003803041c031101081442e8664003190903441000240c82e5820b0540760b00d010700c080390056008510110351203d60b00150641f04000c4c4a9120441c4811074414a800c940401d50715009580c001d000340c0c1d11042442492026940c0e9151201c946e03203c11070461500f4031203c61000d502500180c600103480c00840c0c200d0b03200b0300c14800c241c20098020b40d0780795503510717141c21882c00902c00c804060264840404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 182380350 1250 182379100 182379133
    0xd020f0307090c140702011e121410080706020a06091a0c07060f11220b04230904030c080702030c041b0e0303030f240901090204170d02030a0e040605130509 69
    0x805d1560103030b5a282ca4100f55038201c640501c844101102400104c0b00d0b040403102d002c2c000c8000c0c03809044002c410f00e0420304801808940e1540007404030360440791050095540c000ba22a0030f40e5046000402c24485a0030702200070704800301c540394050600e03010003500d00110402032415611a41c010042c54402e4103012040307500d00740302d030f088451040001c1040100160001c0c00003845d0030300d030030f10820f55a82c9801815801035001344c01382a8010081c0d50086203102c501844104169030305006031905550081c101400d50200502c09200801d4120039501c00300301c00b04402c000034108200b5041c0c404100003ea000041418000030015000b2004508000c0b041d60300170344402030600c3d12500c6e000392117180401c00c58440300e604040c0d01d56000c0c03103aa0310904c80d402031101c0e03c00103940754280003074103018041500c0c880c40745030300c405248200c0b584d0000846403804e0940c54034990080c80c160000d405040e05501041c1d014403031440c01d900d003140d1540103034040e00d50203003280c1180032000b4069 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 182381600 1250 182380350 182380357
    0x106050301170a03080606070602040801020d090507081506010305150a0b04051c0809040b0d15020a0806030307021e030a0f0605060102060106140904020304020117040b090607030213050d020f0307090c14 89
    0x84c00900c604001c00c2d2641407a60180c10003034842d8501608190325013401900326000340d403001c14025228110707442880070034030404d000f80201034041c2400c9100783c20505070110380a814241059513a2001440a0902407000c1010b07400041ca55070005595514807201500b150103070720310401329400090300540b0b0300700d65030014075032000180d03003000d8a03002000001d142c2c0000311500000080c0c00c2e80c002030707603d4a04041440c0c440b2070061f150445003e0050840d5001810749010758130410030300b80580d9030307002d81d90b044002c417412070b03030940790004d01003410030088901c01030113001c7c00d00c0d0400c10000241c201d07510481007a800c55220303a03603c0e00e0460f18001ca0740c0300c900c01070404014042180c1402c0e002540e00a0040c10b2031034640e070000c0b00d05c280c6020101c605644100d450010702514040c18401d181c1c018410745030940c2425181d0485e6405891544500c41c460a220f070610402c54481103520103000c0c50082c2602c42c2240d9620917000a048201d10440000b14140710310154140c886c6e007603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 182382850 1250 182381600 182381603
    0x60207060e0901050d0206121311042901030605060703030920010507060902010504030804080606101412090a0503040b040603320a060503060109060314031905071a0106050301170a 79
    0x1034842c0da440c01040c02036200018400b66000001000b2160845400d10380c40e88c064201e8140c0c0d54040481c81c1086000021004851b40c411410590010b5569003060000f138103081002c841e2203e058800c6005030001c00050b44001e80007000460ba42081c190140c0c081d0f06214040e0011003009a40d401f14803800f1806821014040f4038144041070125000368000720840348181000f40c5820b031251078910960b0090351180030346074000742c200301040c28403440c1c60824403500d007403c05048a4455411075a8064400c0c00c0400d5028407000408501c2c0070007400100390b0f000015a542c0d60f0300d401c0310a034582d115014030b03004030b81003030030307c0803100079006040d0362a441800c0b10f038030000f02a140384500711401920411100e9103c260101e12980c0c180150340c000c001c08031000030345510f10328006032000c1175014600c15a0f0028004400b2140c41040400b01601e404d00c3d0440d030340d07034039498012400d04a10740c6041e00042c0701d500110f1041c3d0404000c6060320003d48103144c10784088071880743e60b6041c0400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 182384100 1250 182382850 182382859
    0x50f0c0a0e161d0a150f020c0901170a0b07050309060702070b0d0f0207060614040b09090c1c050a0302150c0715020c0309120604110307060c030e060903010c0801060207060e 76
    0x700c0546503480ba000000c001400081c0d030210b0003e00d0400503014680c107802c29849251901015144c3c5604a40e50100b440054005082c20720340c1e580004000071070500c515901c085040b004140035800034004c1001b0030350300c001071005d030741850030000303007240c0084607020124070400020500d8a40005072240443d03a08104480c038000140320224007420500250098090302400310100294441c001d03100600b043c5e46c1900f28100e0358904000c01d407145941210700890380c03801406002400400c502542c010305480c60100440f000d4140050116482000382003402808510403c266000c00ea00085401c038004140d01921350140501030f5200d6000001d2100688080110749145583c0240054480c80c00540c0d00300b801100c00f260030200e200801030300c1074000307904110400030b640d2200c0c00c0380c0d0415001840703081d040c00806000d044264602038203010400782c106a1703540c5d03600201d0301d000c1e10180081c800c2c40c0c00030f480600068028010000036019425010a0b41d0388282e60000000c2c00040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 182385350 1250 182384100 182384131
    0x80f040303020904140a050703050a1a06090f060d02070b07031b08061306030b06100207060c080f07020409050102030702100209011709010207050303070f02070f0f090b0409050f0c0a0e 81
    0x203500341c00030740c81030318051303085502c1d00ca4044280b54a450803a1150100117004100c0307180100c001022100c005108100561820018131a42480380e00d60080400c8181c8602c0e03501c115401c0010802ca071265541980b001c00065808100c0500d40c01914110b4130408003082d0035151250144c0958a8664010002e03d000c1d21807a0744091040843d181c2007500940b0309a04040400c3c8603c0c20745000e50402c0c1d5584010b031051154074100581142213201039803010b41001030414400070f00741c12213000d001d00030f1a00401d1100580d8620b404494465500410400c1860420301c1c01344d011b50811280720b80035005040c0b0039007601000e8001c81d222100140c1d1064880c40801a561420402c00b82074602c440d0740c01c0c050b21000030010030003180100150307201d400e107800405000926000441d0440e91000340c46281c10012440ca191801d400d8401c8514003180c1066980003040c02041e20600c094020301c9016905580e0078004554440940820307110030724110380ba40c11104c03a00304142c40c00c2d1003a09919 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 182386600 1250 182385350 182385353
    0x80105091b01030b011b030c060507021506060a08040b19151509052103091e03070801020c0d0c1e060507170c03070f020f0a032f0a02040c0909050f16080f04 69
    0x6c2c03130405030103100c0e04003800707078101d01d0301e98404840003158124050303444076030748040c40325010300c20380ea0000c3e04443c55840c00051800050262001610040c0b10b070004901080d681591070684844040a0040402c001f140ca0418826010414440c1e127100116000d0280c2c0f60500c2040308009555015000d0300900001d018142041c0b200101030250602081c402c820307803a031714482d580001014003140460103402405c01c041c140319040e403200c00260300c10000f90030961404a41040c96001a0620031800341d91400c0c1540759001d041000802c5c400d010210000b005059803000340516090341e180702c0b08070112000350400080a44410114210510000d0071151090081c05064105441580d202c41544400342e89000c0010300c0c05c501184a046003e00040350484850103511000004030440e104d0701100076440d00403101d0068080c64444428190385030207044200018a40420100301501c0c1450300b8003c5100c040e650611030140030000000035034030514500d4010a00d0044009554aa5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 182387850 1250 182386600 182386637
    0x20a0f020c0a0605311d19090305040b0304030305090115031e020a050a0b03090c100c12030608070f17060903040603180210080403020f190f0c080105091b01030b01 72
    0x101c5c501132020225001c0f40040100c020048106402c43c50b80e0003c0b04506005603250114440c00c00b62000d4070b460410081ca14018415010380d40310102c40c00900412035003800c07142841113030401d90b2000703c00402d01c010180d05074045481442e225008115000607140001028015440050305c0141c41d0358124444803a001c0c81044442d00c0145900e500a6444010860840140d03000781007c00d008010448030341414400302c83c90b240e084401d0f400384942c2104c0034142503a945400740150320104161403946010794020409020403c08803001c071903445241d00d5442d030307031402009440c0d0303078202d12881c0e01a4001181d0b070040028030040c600f02802d08204a001703004e004000201d071803210030f120000d41c4550100b8165012566168035003031a240c24041c5c03800140c0c80d060011036010b40f607484051101d403210741422b11740c0322120f5102e0031058240b2503500e08694102c072101d5440c0c41e040c4160000005490b9403800102e46c030345113002001e24019011248802000c0380030911009103a07140100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 182389100 1250 182387850 182387857
    0x606030709110c07030c23150912011b020f060c030606070312060e0f090a050304060507050304170c030d02070506030114190e01210f02060c0f10020a0f020c0a0605 72
    0x100b049003041c1c0c0100010346401c00c03d42c02500c00074080301043c040e21003801c041400101151110302080d2254401055081850444502401c040440c486074031b50746020400401c000284020302440c2c418105411fa43c021500502004d071003051f18803400e592001c01c0503071050408040740c82c2180c1d140c0060000941c0540801c0342004801ea01411141401e8071880c0e01516107480780c2200e616103540d0324280d150000d05400f410b07030720100082c40003d10000c111030a40d11a444c1164481c2d42901d40645940901d401059407864031150341e074450000003030f00704030010046017110310040b00d94034240c2e02e40401740246600710301c6c02c10041c0205411001d4042c43c101000c0c041b1650100410f905040c4500f20350045200351a550b00100175403100094000c1d84215011000900700760140d56540420209013402800740310080f0307840407014410f2111819000282080c2c80c00343c003003011248003d50005c070a12000c03850ba001ca40c04083d10002d541c81042d2800703031020b95aa030070003009403450340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 182390350 1250 182389100 182389121
    0x40201050d05150f0303070203101e29090f010e0415050a0b011101020c03040e0c12040302010902131107032a031112120a15030f0b04020405090606030709 68
    0x4020040d04000000c0c030b100b0584550082c54403422814034480070020f060034070f1050584a40e0042c07010a0150f0780220b900100d00186010000350455000141c0c03400388641e4a2410340249003500c01c1a0044400050720003440c51940c4524242001030704110a4030b809490250320400c1440052103212268081ea581050054002d03803800031003102c4040941d04210340081166844030740c7d030742d025600800b1a00c0c211030004000d50408452403490340c2d50b4040c0b03200c0d10080c6111000070415417001d99040b41c40190b41001404003070f184c01c1c20042d000c1c16503d0707400c902905949802102a2b46948100303490500f03800000d610b4181356840866001c9a12901c41c1c10824185000d689507041d151210080188640c0b1006150039411048030b04140c0d24107100e41258004002d01414441c4145585074850b456010000d20105c501402403000111f540004009880c1d050212081c440d03113002d02c520441c030845040c04280c0d1241d0700251541c40649040e505641300e030700c0234480812075420022142 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 182391600 1250 182390350 182390357
    0x6020901020a15141b0a051c020c0a0b0c030103030c02010818061503062512090b01030605040506060d020319021210022701171905040b01080d03090503030609040201 73
    0x60b00d140c50f1580403200318190703d000250b8407810002c1c54000c2c20b184a42c001411011078810382210700c0c6100345449010b18171010450009040296922000c00680d9204941d000c215150800500f510755143d2240c02c0a03164007200300d000a004034170007011241640d070b043e51134850081d501d50054900d0b05002e01142c031010000c0d0b0161503949003c01403030f48581d0114400900b0705001d40245800d0081c00f40c8000c40040030b05800610100c1d001c00c101e0000301c40d503d060400d0546800c1c41c140100140100100802001b000000612100d40c000740c1c01180510300742c58890300c815040202c15070403618001c3d05900f006924042400314460300410701400580b503001c120781080411800c001000214409250340801d41c0d120208448074440c01000103c0f0203241510303c440c0c0082c10780600c20314403003882030a40001803001080500403150414801400740814109840d068090f040240580748a5100b414400a07105120b0301411b003a15030000091071468840b2014084074000080050303050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 182392850 1250 182391600 182391613
    0x1218010e040f0209010f021b010f090f0b09010f02030304030c031d150a0201060f180c0e30030406090e0709050d030905090f1e09070b04080f0d090e040602090102 71
    0x80d101c070700441a00100303060005954641a00024007130b280b014010a04541c01220700000b100c00c41002030103003403006d081201802e02000e03403c44002e0182c0d0400c1c8483c00c40807400040200c0c070a4064000e01c1c41c262140f40d9820030040301280d03203004c21140070700001d00215150000c20701940d070401ea016040b400e503164090040011941e00c20a003021013031a50000506140e20640c207124040140c46515500c5ca0940e26007440038081c6c040405810280070365486171106091b00030703608018400e1014060703002e002d06c1000d60f0440600005d03404c05040301c18260070150800c0220840d4251120754031802e41b10b60802c2d20030b100900006041c0b1042c40304c122000f01b12030317a03051410740d61f09110b81c0c0d4141426061105101e00444050104007060340c21a01707110404444c0c900141010100540c043c82c00d43c0c42c80f004502e4039010303a20400e50402c0019001c83d16072030208113003d04e0b84000086440030401140700312104501403140c0c0e6070482d115400b040001c0c2c1260010803c019051040b00c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 182394100 1250 182392850 182392877
    0xf0605031204180605031203060118031208090f03040303030b03100617010e1b01030902010201060528140a0b030a060b0d090b0a2c070305030706060501020f121801 72
    0x40c100389100d001d400108042000c020841c0c1414101c400740c0300380d0340d00340486850040840d54400ba0002e200136100008000104164815222075425502c42d0715480103090382c030b0a00009202085501000090f101400035010b0b41d030016445548400c000021803600f85503031400c070001d14004403801c0d4140a9188401503c039154040c49001d840800d508540c00700400c4186421980d410b2105841e07074002a1b140c1075181052200101100020300340403170f1584203880100d0040c160341c0c00055000d60030002400741d500c1488061010038014044129006882d48110564914290b085640c000da0020301808229a82005142c211544800110b420b40d168110002e00350400c80d440c5500c0c0740d44a14803c2400140640c65030021009a0104200100802a81413100f1074041d0416003a604200c0c0d03a066039000c2041500958000c401d890304e071070851400d000a40080e1080c1801407040000544854001060409400040c843c06920b0941d5070300011451a001c180420305112500c59001c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 182395350 1250 182394100 182394103
    0xa030c0b0c160f170109020d170d0501061d01081506070302070806011d01060810050603090a02130e1227010e04020c010504050d1b02060f0708040305071809150f060503 74
    0x10060300703061056026040c104014002c51401904d003848003030b0304081442005d40c541c0c00c1075114480c1c000300044003180b41c40b810008580324075aa900d28079450300c4000610540d002e40d01c124400345150610100d80810300045407400400e9500500544044102600d249001d000403c03600d8440d00688480c0c5030380e819103c1c10b00c00709a1080141044a85085000b40b0032040003a01403c0707a4209141a81054507050344203a83c42c1c0151390003900300202043d03800d0000c1200041035a40102060b0032400c2d0641400f024100e0241d0581c0d26100349034043c866201280251460302d42075042c44080d0001c4042600d060035071824403035060140e40100000c00d512903000404015002ca800815a800c0525104d8a4030703115021510400c80e451034090412511240305240c49a01280d0461b01e40c503419401220074031a4060007866801c00080001c2040004070b00708046640c02520b0109001071f01d84550103898801100030541c0711500d10b454052281540500a40317a020640050031940b51000b0a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 182396600 1250 182395350 182395393
    0xb010b040f0b0d15171018170906070602070c0602010e101a091f050108130201080a02090a030b040501060905040206070b180111120105030d080408160b0106080906060a030c0b0c 78
    0x11a50060095880c0c503921200b01b100004076951008108004101e066040140e1300005030300402140800166000c90100780054800f412002008603030b840c422450990b0013980401411034200354035440000c1c0301401807182e01d051038441c00c00b0700034422241c440c0c035004203862030704030181c9034400d80680500e898280505228035000078a0359015000504015800100b681c4224104041402041503070036900d40c1c1c0c26045a42801c00003183e07140c56410034042d002d41e010564202c003580c0400010f1150002c601e0340107900900c001c00c401a29003080c41c090340c0003149c000e50040f104100071000200080803865000810b5941030702540d1585540301d09541031070500f220b049501143d1f161f179100c080e021143c01080200c0040c44820311800000d0041d42d4005c0002d0891607010445205a01c0160500e0f660035a1000004c9800e60f143c143c09020010203942e02541842030350000f403880e09210100354143c94008164400003454540502865800410764003424000d40d01801d082d4081c0c1c6500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 182397850 1250 182396600 182396609
    0x1080415200304210f1809020f1e12150609180709061b030f0c0501020a170c1204021012090f050609030f04120606030f030c0b010b040f0b0d15 63
    0xa0030390380d0406040c1914030008041c00804001e80f1468034050145e006405400401046e04143c140c1d140c02c03100b01000000c540d4400f0041c1400040d284680b000000010520075241c85005640c629140051041d2130107800000540040b610000c5088841145001015000c000f404140303002c18100219000c401000d80c02e0b00d55036010001c0c48035682d080084500940400e207890044200030300403000c034030651020046c00703000b07000358036401c03071446111f000241071381140086d9600d144c01c90000384880c80004031100f00e000703402c010690404206040310900031001001400f192660307001c00040d400386442e00d1043c814960311040c008070703450061b4000ca0b800390120a00065090420f941002c01c01000c60b20702d0b0700304004100884100200323079020755050b0140c042e203417100c3d0300d05807005042a401c0506001c0801c1c10070b204041c0d120040d0304d03400d0712501e00d601581e43c1e21a050b00035802a03001d6055003548c1020f00b400480c18440162016680410002c00e020511300d440c0c6c151521036400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 182399100 1250 182397850 182397911
    0x109060501090e030703050909040204090b01061806140d0b01121118040506100c030e04020c1f020a0906120f0e07060815090135030d0e0102070201080415 68
    0x100311040d903038410340000c4034806002c3c518040ea00d903801046423182c481c00902c2000c2c1500850103544a07a4000b4100350351182d400180d55841d410302a2248040003d040100c8d520b00c0b001003071180c400e503d041c401a40010304241090b480c02c8910001e0007400e030916041000000e0a0410000b650003880d425091427020786a41e04195030300b1312955071104034a14012401c0400740039040c1c0300c0c560810740b0b0030350b031746005400e4110f2494111800803544e43c081d0340c0709001040c00340031504049510000b140b05507003000081e254a2041c4001d0b4041c02929202041c12001d00700004c6002c0c1c20124103404030300100180000103840c049045500304041018513500801d41070150a80050105403c0751801c00e00e0844441c0072400038140e500140180481d08080d003803c10400c1c5506048140169926010038500c5440502c1e80d41da00d42003441c80c400d03a40e00f0111039442c00c2d1410310861b01c00c42d070181c0d98024255190780341c0607800d0f10178001039108660ba442020086085c201100c1020801000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 182400350 1250 182399100 182399111
    0x50c03070f091109180c16060501061d150c0a0f0807030f0c0203121809010e062e0e150309060a061d0105011b0501150e011a0a20010906 60
    0x2444030115000c038040781c00e50b40c1c0c00700160203059481d4035174801400950b079140b9170b10383d030348400c15800760060b03102c0139204250943d01030082201c0c9801c800d041e038500d50740b0850046060900b01c4800001e03444501e0704403c41000346070345500c4240080244002e071343c0c221001451907640c7d4000881c0724000c00d94940c038001ca00e9508042d4414420481e010727581c41c010f81151420b0300041d407a403811780f51006e21804006180040401101036040e030a40b00184420340310b694a548100c03005008458052151010054821100c441100001e142c21030344200700d8041c4030807140039515002421070440e800b081c0b64007001d1000e0071007402140300307c1010313003d060107050030144107080d115260001011104016040001d03481000e09450464a0900c4d001c00701c3d0701e44441c400712246c848800a0311950030801c40c403406c03000d0300c05c40070300300c481c0c400800c6251381e40c0c1c4002600a284035198004110070400120010911904220450125403c81181c2108a9041045c00c44404100403254203444a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 182401600 1250 182400350 182400359
    0x30b0904084f080c04090c0b070b15061309051b0703051c02070201020627030c061f150e0301021c0c020c060f09040f020904090503030f0901060e0103060207050c03070f 74
    0x207480140000001c001401c08043c1400300c0d080c0c40c1c0c6113a000c80d50041e9510742c0004140201c00c03c06000400b0300c203003030341c1c0c2e1201c40b0308180c00080021070b0b030390016844001c0eaa803407500b0b06c0d030201da00c14481c2a00b51500541005050009840d001d02140c03545180c075940c2c495109001c0c0700600c0b12601c6616106d98032040342d20340c4001901c0c081824940a84103015540151b40c0108a4552100c3c000810707003400304d61411400465103248014002c00e00c004500180d00041c0059404e0142d0341e40e0f00d40c0a030b140c50803c110384030756045008540c06d1400c01e4031201c5186000d66124040300320010000350a140a2145071b0000140406840701496251102102c40c69010b1090a1a2800542e010741c506004040300322040d220b02001140902c1d51803d40780c44540321603058414031390005000780182d40e03130390504c2a078a400566407100400c000c040414407603d4140308850403150700d01420641a07103191513a4000b904103403015909c9018208100705907136410710044005e45002c2ca1000000c6041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 182402850 1250 182401600 182401717
    0xf05130b04020a0c140a0c090203071806030606021e0a0308090c040903030c0f0329031002030f010f0e01030b0c03090a0c030308160516080c0a050312060907030b090408 74
    0x5005d1002c0ca2074111501d09404189090b51220035240c01c01310160b134030340b605c0100f11600f4500c2905150075645c07500c00841d030568943c00c00022142a03908039003e442036480034000c3c002e0700215000840d8808220705000a006000d5a5401014030302660303c0341e13840c00085030036108100e800320000fa584030400701c0915080360001084100b2842c0800088a000c081007078005403500078070350800c1820000e2020380d80c0400c1080d0510310340e400f056449042c50b0502080480b0280580440301c003841d03801041c0c402e006a01d590483e40c02001c080c059880d03014541c0340c9540003510f2004280161128000481c041c2c0c2007a100541c03103583d88013024501007145110b0358203000f55505c00c0090400c1114040075207003c21201e01a00001176541d01c4c400d0f907074480c0c90141140d10050007804040b44800e108408001101e1140300207480e01d04260340c9042c41101112a802d2203140d0010725440400e020940c0440505802801c1e40607103051209481c0c101303185005421001134003d070024461140c041803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 182404100 1250 182402850 182402873
    0x60f070827090f0912070c0501080601020f0d0e010302040302030d0e130c020c06090105120a02030103020102010c03111206041d010e0705010906090303050322050a1b0f05130b04020a0c 81
    0x300c0401c0c08180301c401000501070510140140325280b20076008038002280a10444045034902500f1540c2c90640d4074200900340c856101d9580403600c0305001680550001c604080485140c801800007200d003802d0640340b0725503100701c0504165081c08084010784081002d210300c802c0c5621113602180c0c100c01004040701c1401d07401c40801d070808022107619500000d505500d80d008503480c1c1d0300c500802004032198080e0403944400100d208041c000741c0142e590041d07058a0003079000703108041c1040015000e9a40d28295501c1c05041080b81001d030340344040c8019000f41c001440410fa806a02801c0000d120800070540b5945c1d550781d4a5900d01d08040101d14003c00c000c1c00c001801501d8100c01500f1100c503880081d09000e8000002098882c640641120501402c20319001200083c1082d41e520010080200c4039a06c596415245031008103400310b080b2000e00c61401c44513800d0006010702d0024100e48446039644a44210400d66111b0014000d05002c0303903100d80d00da103100e041003003040c1ea = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 182405350 1250 182404100 182404147
    0x30f2101060509030706212301121104020901030b060d151505031603140f04140105221a040602070c0f0503030708072406080706020f0a02040b060f0708 67
    0x3010030841e43c081c0c6000c50b600c07040f541c003820400e0801885140000d03250288414102046281c041200842c0f404609903110045004040020582e02d649401000c41c401d55406026425030302a850418540b640040202030f03818036000c582d07060503401141036500300e00c0d00c5c00c84050300c40103059650b20746001c1c44802407045001c036542d40c1d1072510001d025444050444985501b0174209511118000e070810300707682c0409030440146140c1019007801c0c80a055900700c4040c01c00304038210b1241c1c01401410300503440e0650500300c00004162102c041d44034241c040b2942044007942d42d00d00240e02103024403890150b0005aa10451460111902440750308941c281460700340b403d11107510000151034655600c90a4641d980c540e80c10980c070401c010342000841e0350140c2c40400d10b4001250002c0e02140d5503130040f10121034407140266100e44400c003a403862940088004000361500d038114202d0003502812646c5070840c0f807507412480b5401518140d51240c0c000492902403403011883c0003606 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 182406600 1250 182405350 182405357
    0x305030a02100b0901030f21170a0510050f0a031a0103050f0a0804090908090d1a060301181b0f12020906010306180b120a151a01020d03020a02030f210106 68
    0x7035243d20b00040781c04006000c05404a00344020b070400b0003100200003070905158070003041c02090b807200300500c44a000d1031800d0b0b80038505d4011031600d440e10702920b8003c03400c55a408142d1420481032103040d040035400300b58002c1e94000c0020100c0c1007441103810700001440608499030460074074928102d184120211198426542000401e11240583e000c3c0e803070406c80070030010211706004545004030240941c0c0601040c007204204405060500c4400040555000d803580c0da00d81054205c4904e802105160740d560001b03240001d01c2c5c00c9401502303046101e130300c02000d0f894464a552000705038028683d02542d060f200c0081d450000358042d4881001d10341402502d083c03201da03d00e070440901c1c6c7c0d134181c0742d110181d071f0640f507a40d14429007610042004942c82c62503103081640050007298558600145040c0c0c50004003401e40f0519503851806030004e00403a420280124000e40c4103c0044045000910240f1031120700d0346e00034900350384840850a40480b00380c42440c0e109c901a4048001e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 182407850 1250 182406600 182406611
    0xa0f023f030103051902010504050907020c1e030d0c0606031b0303030501081908130b031003020405010905040203151f03140606030c100e040f06030b090613050a0f030c020306010305030a0210 84
    0x14800045070b005d440d0b00030071804405007107880140d030203000d142c00040c0e21482210420911a9000030711040c0c00e81e0072a44480302c03056030106002c8030885110025090340011544c11100ca01441001014920030a0001143c41e500c0d264103041042603003074040c41e102884001c005142d494025540036041c07510140005da41620901551480c1240780100810f60201f010214511500b440d1001007104415140e641d20f003140000800c0022400102c2c882c9182034004284030004d4420144255070140091019040c0c2c90301100e280c1c0c034000d102007145214850400d281d4200700b20f210004501c144a0028892080c0c1801401c0000003841c043c000d5100c0d0070f180704644e403018005082c84c0054141140c2d0b00c3c60140101c0c000c3d0064154010102d81003000020030456801401403007000080151038080d2208429020754030309610000e030441e032241007140b0200e90000c4000340013500c01c5c1000c10b20841c040c2e011a0400038240c4c0140e071207420120740c003031100350140a02006101801001c010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 182409100 1250 182407850 182407853
    0x13020a091a04090614070504080a030e0d05251205030f070c18020901080609040b04020907050405040513051203280b042307050a020307150b18060f0108010b0a0f023f030103 76
    0xb0fa075507240ae8050108030b6180c1d141d12040e1603d03245960340300d4002d000d0702e900d4150310424001c69000284400d64428050b0710015146282950380458540d0002c013031481e00324040d0840380c09801c040c0041d0327504c002094000400451440502d12801a402805a203602410001500007038008200c00d0054214208100028032005c144a51296040303902c1b42142c1c40d8104216114043c580101c0c3d00b151400080c000802600d059505050f4417607400c8900303400451800324118001a01c03100703007600304418005201d20321407003041d0103510180c00010b00311462000080c151000000030540824607034408100481410625681c003c0340c4e424400e01c0d204802000a5a9118440700944401e100d14200f4084c0710a5820403045940c00421626415039041501004400c003651580d201c3d500304d41c82e0040350350085880c0c0b070480b413929105504100030b0300b43c1a10000142c280300401c50149041d441c4082550101d14448004c1003101d0080c1c0d034000c030201103401001c0d41d4242000400c240700400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 182410350 1250 182409100 182409103
    0x30c050a050f041d0a080705011a1c0203120403060b03012703050304140604080d050f01031a1003020a08030c060c190f020f060a0b0913020a091a0409061407050408 72
    0x621032000c1d00c00050b4106151110b1084804c2d80084001d03601410040f07001707002181c0c001d850b446004d440200090070740d001c0606201c80250034503070740010403650214420000000c4161030340740050184c40c2e000f10a419205041c5e40319420071240182d0300d4100f192503041c24881d003000b1000800490204100c0c00c0038504440007400401002c005c3d0010025040003925082c0b013a1907012a0215002ea09151800c65a1a000800c8040b901c80c034203030002d411242c4110016040341d07040701e21241e00840181c401c10064400a0102e210901580d100000507110004400020300082c4091500d81d001103001c91700b4120040c0c6030120403041841505c4200b05c03c0301942d502090a4181500180e03424102030b03003040c1148079040540d010307100070090100300d136070000450040c044440d0f00d42a940c25800c000000d052642c060340200f030541c0180a0608594000d80003801010311039401a1806800581034881e48502110b0071500d5618a90710000e00306c00d660380141e01400c1c040d0400c0e0400c0850fa = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 182411600 1250 182410350 182410369
    0x120b0303161a01080d1b0f0210110607050405030c0a140f03071502071406030f04060e0c030703050d0912110d02120118021513170712030306030c050a05 67
    0xc200503502118071420016865070b50035805000706031107211503948642d0151680c0c110540715001c03504007000d03140300207000512111200e40c00222040741c10300a400703110402108401060501001d02c41c10414510100102803160320740341e660a80d100c2c2054107140c00d00c441211128040c1b101310b8824054042059140703d801401500d1500340000f8800010345030410380c3d03000d415200c041e20b030801c00c2c050303000c90b1010a5400000c1d549101c0305c01082807140921040f40c0352481520400d01240000320240c010400003205901125100000b0100181c00c15a25034011a0140c1c0514411401c80d9080f51a0310018141203400000c2c4812580740d03081d904540781c5c0c03003c1c844d00d01c5c403040d0021551528602290030044030f0080040b1071401c1c101407038010154500f680300b41c00041c42c1002000c0500100c1e4100c01c010032040480610300340c0c0124445150321144d5042c4c3c0a00080850008060840b009059000e550b010440c01c0c65800d1400940950341c000c00d01030650464148060703200ea40701c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 182412850 1250 182411600 182411617
    0x80609061f0f05060702010201060f09090b1302130e0c0303040e250c0803060a03080415020705040519050c0702030609060106030b04090201050307182c2406030901060306061203120b0303 82
    0x44030b80c0d403817403440100c2c014040c603008040001e50880011071a02100e0340071400780c0e44181c0d98540309448100c41980300b580a0b4000a500130601208642d18900580118610043d01e0b000c440740700e945000000c0c29034000e038104461000f258800c00c45034200c00200700d061409a8074543c4038042c500c2c01e0041c0b151442030f502030001c00c400008211681c440485480040da000002d41d07844036160010202d1620300a1138142c0180325a15000c2000d1801d4843c0c1800341031200740d0a02000c0070042e43c03002410b0001c00d401c4a0b84002c2c00003001503201804010701c1051908043e000540c149007003c1c0841c0c80e03682c141c0c1d003e145000c00210050340c100017181d801104d5400c0070025400311001032081c1c0d10403a0016008102c4002a480b10741c00d4202c0c2c4020000a0b000320903070307039070784100588410100502ea42e604845401c000b0449a08014004541002c501d500115481d07840743c40300c0c4144d070340903400350548069684035a810b2607413144242e0001c800d10300e010302c03040842c0c1001075aa409140301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 182414100 1250 182412850 182412859
    0x40b18040809040606120c0f120c02030d0c08040b100303120209061303140709020c030307030209180403091505031e06060d0504050c0a0807060225080609061f0f05 72
    0x21405201168081d00c1c002c14006006000c0562103190007004051441035101080381045080302145000d8a81c060501071a651902070000c0000444030182c00028040410b6000030009440040281d000302d101c0d06899840c1c00040341818601500380d904c00515075048890705250520019030300a4141c0303017102c8801d00250722044510001a503503c18441c40c801c01000c89100001000420003258800803001001d031441240d941e06588103074802d048941c21550401c1001405190199001e4516100090030020140c51001c00b03040aa4200b9a42540403492111040245405d950204403031100f545c9030040c107605080300d00e00481013489415002125070200010125112081a101507a411754004d004600341428003036181e40440307011a0007200e0a40d0f02145034900041d249003269000d5000b8092200804201c0704000300c8a6101040321200e118001080d00082000c03501404409016221506120540d0301040da025214900100424a01041802526080b00086410664 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 182415350 1250 182414100 182414149
    0x3070b060a12050105041e11040c05041e080606120a060506061c050a05070e090408031b0d02090102011413030804050a1b030507060507080304350d0b040b 68
    0x300041e603248103035002003280208464009041c0304054000502490044050401d0581c44087e2580c040845a50141856000380a1a041030a040e4420001840c903880e0103420183c55400d00d102040c000c2c0643d01c07e5907120710b414452600207004d00d41d04040d080700d10b000c16207a80342e4860f0f2108850840500095960000110a0f464031003c50780b000c3c5125001c41c0200c0c25103400507001706825608541f0702c82c60100010200e1303000b2400540d950304014100727003040e503856a60000a41c8000c040a90903542650060300d188011000b4100708480c14030301580b00d1204000080c215450341e54150180403c60081c0b045a91145015040e074035054034149039907548608041c2d240480500d00141104103510003c54800b101e80480c05c180c0b4820400d8038092640c43c0380071106802135038005490360318100301003000514111411405800b178104040003004450340a043e07000c900c00c554a5030024000360420006000d48182e07222040100e4082010b40804004180310408101c41e17203609120f01d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 182416600 1250 182415350 182415361
    0xe100501120f0212120a02070303180f0315020706060603091a0f01090b041104060e1002030301030803180109020306150f0301050103210512070203040f090c230904020f040509011703070b 82
    0x240505450105e6080301350795076540600d802507a6914920090300010443c034003154050f11540c50440488498119a80310035043d5250b071114105003c90060b4400d82c00c01104000070420301a420040007203440c0000c1d180b44604000841040b00040d20240380070840c10070090410985105066801154001880d0841d0720045001003080700d41c02c0420325800f06000601c5a0301c42c07907401124001341d07522040d85c882e074201070b0703624002070000404250341800000c0b011f80903c00c1480420340704000119400055801007030a10b08290b40c1c6068040c1c140742903010342e08003a42d805200e034805400801a56145880b108484a4100480901540c0c0d143c030481241d03202d0005d0f0344500c18200180081c0b420a6400a0b541c0e9000d4402c1c060003008200000407244424400c4507481502da8540307212445a8190040802c06a4191540803039000d2040c5800f0340c80c0ca101502d480740003281c4e10755443d800c2c10100080120149d100c0d00030864140c00907a00001c3c0442500c0349258400d24002258030340 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 182417850 1250 182416600 182416603
    0x1f030605040204030f06110304120f09050405070801080601080f07090c031409030306030613110d08040f060203130905070906081306111225051c0e100501120f0212 72
    0x5500a41c1d2060000c10040300b8040d8034464403003031504c500c0c010003c24821907603107001c80c0400c440c0604194100404411140e008070b00b8640c082129241404c842611200024201c074825104540020542e00040c8803d8004014082c050700c0705800a02610400c44d800f2a59101c85000345001e0607129952a40c4850107a00002a0842c4601d110001c519164046964a4208450040c400d116074070206940601c0c00e2121004d05401060301440c800303107c010304c40150103c3e40c0c2150310060400000601c0490018030202502c420350107503645052030b1010074410103a0b030700020b090510740740030301050340e40094107042251070758107001d03425541d142e04481c0d0000c0d10220103440f1340d0604400c0040b410140b002000710203008414401c4035140c03544400500c4144060407150402ca003d0b41a004a0013400a03114107858411000a01d0088141c14000d95800e5559070040398450081d0326071006150040c58007409203411283c101081c00d4a61202c900301000010340240c298084410b8401c40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 182419100 1250 182417850 182417861
    0x20c07030210020607030f060b070f020d02030304090617060705041203030e0712061401050f040e0c030f0d1d0906010e0402130b0d2018010c0f0516141f03 68
    0x10010704642c0240c1c2e91200194558104a811100291401240101314112031045900340e5650010103818101c1540e241b00c58a16000d0341a6440421060382d01d00603501000200060840c0c8140415500c0c502242c101440c0842c1c940481140c218408000c8229403010a0700e0803924030140d00c00200c0411308044c0e004001c1e04440441c50b000701a40070900d0304040000002c450710a90081150b2144c852103060000401e02503594045a110301d225401d00c1c0c140c02c21414030703050364240c4d05000000030000c0d140a40f290b10603841c03a001142c3d03020300c0d203400900300c02c0b0061050314980c07600c1c0039100000d11001401000035041c0040441a00c403d81c54550513a41e00d4001c1c80c0651611548070f150341c0d007803a0081c80e500d504180c24103004032441c0214805940c002d000104080c4c0c2403c001c010254610894402418100141c0b4080f050119055140f01c8840c14014809810106440c1c403600c16000183d40100802d00c07500140344195446250602002900030102c0a60208081208501801 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 182420350 1250 182419100 182419103
    0x3061b021c141303030e0f22050705121015021903050d0204030b0708040606170c0607020d0203060a0b010906080402010e09091606120506010206010b0f03070c060e160b0c070603020c0703 82
    0x2204000481010f4006d405044804011100300c0510040c10301042442c03602006400000d0b000303052600b4510455410694124500b4149141030104406c2c415843c94401c803071100c800c07020403004002e030521603581d481545190b07201800750203000e03050916aa0450385002000c0140c001015407240c0415410b0314041e551224811a0354240100c0040c4121000c2d00d00b070342e80300d00d010400a00c0080d00040101000c40311005054004115030070064642c021903404d0381c00440c0f4618500042c0c1d001e010302482403141d101d00142d0084c80400040c04d01115802c0442480344c0c042c240070150b07070000510328070404100c504408550b0340b001d1042c1040300c649012444000e01d9400450500d40100b05100030324050300342040741d507403004012a034030340c000c0c855a46002e07810041e604091488000660380715819007804682c1c00c486941c5c0c101190520382c101c002d42e81004110b07070400604940d60740d00412f600da0515049c01c1440c03100a444043c2803241d03009255000641402d0f405c410b104150055 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 182421600 1250 182420350 182420377
    0x30507030c0c1205070905070909091e1a0a11040b09040b120c041a100f0314041a100308030c09041b0c120f0f0e0105070c03061b021c14 60
    0x343c0c0e01d40089001c11115407044440c0d00448001080e015424810a403145400d5500e107038059180c400769500030580b1502c2078995102882d1041144240036480074141886902a00d031402c1c0c0800e15400d0ba4030020b803203107034140c0c1040054019030001754203403001d40305520f4125541d0040180041e00802c0a00352040c0c1003685e0404c0450f80c01804500410001015241440565160415056604503030327914241d10902000980101c80e101d900702113030b01d4a02c0e080002d40740000d000d60303904050044404444850b50502081c007020300c070164040d0812103074840e04940a0640ea10024240001032082007400800301d0503588646c0c0da0303041000105025180c4030b050b201880c80081a40c1648002510a034a60504403030350701c0e00c43d103811940384216903500d8030b0b4800d5071a81254541e0304080964108901400b0940219001d148001c005521400c00050030788080076034a0390088600700e003e4195000b202994081503408609040450342515008100861100b03402c451409000c200d880301 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 182422850 1250 182421600 182421623
    0x70f0c0b0705070b25020708210c0f060a0e060f0a0e0c04020c03131a0403022710030302060106020a02011d01020f03070302010605041508150a0209190f050f030703030507030c 77
    0xb141d4801c0545003452030184d030341c0c02c5519024107907a40c1c7d541d8404d02095512075401c800751084020302c1490850041030300301d481c011070200b445150511502d680c0105401c00d40500c0510803140c481c50240000007805040a8501035034035481211004120707882d041e03142c4100b12101c920502285c18480401441191542d0311041e01d00c0d525000b1050912440000810224805216003111051414412002450182141e0a005200c101009804003040080e80611070b0860448481403003072250080c079841c0342d0310350b040003450310006034011030a46d041450b0000140c0da1210b207030303404040008034291440c40c400300100c1c03500c01001c07100b030030602004c00c8800c201581900010120381d0101c50901280454a224100300310213485074142d140c1c44088038003580031014040e95488540168018204031580d404602d00e108a010701a400031081c642c14851412440d0003c0094a41540d5486e00054030102296551000d03000c0a001e006002c22020304240c841e03044458040c0c7d0003c20b03540c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 182424100 1250 182422850 182422861
    0x2030c06270909100b0f19031406010806070c0602120c0307020709060f06030b150a0503010e01052d03070e070c0c0905070e1203070804090b100e0109050f0307080f0c0306070f0c0b0705070b 83
    0x1220344180411500c01641d055030082740b840009140c1d050325005005004541c07a2003078140c6c4c54480b101000c40c0d4041e000e0043e01d082110303022640344540b40c0748040c10354030b1412140003801c190043e0055114646400c40c00d0040103403590035101645c13543d0030001134a40d030110010301124480103560074050000a51031101a80c007001860494240c28603e00c0303182d80720000c000c0e0203080140c994240204074100b00c415600314420040081d0005804d64400d9501c03641e400c1c0c0d0881c0201c031840c0110f00607440500c00c00201012940003807403001c0c000c010342d0800d2000281001e00c0039005a104040a084a0601000c140b08031000140c5c406000c9075a00e43d180c1808010b0809500f40911408407591075001c81402004109050a4141e5460503541d040c00c04000140c030015400b1034061082031030208480b001041041100c8005200900f8003020510030503140c8070004108400303b180d4003911a6505422070b40c0903407459889084010150f885020450307903401540e0000c1d150110b10707001e200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 182425350 1250 182424100 182424139
    0x9020307020f0f0f03030c030a14090d020f0606150a020708061003030e040b010e04020a090e0903071e030c030e0d120e010905180606030402030c06270909100b0f 71
    0x800e19072402c0181c6440100400030140c4983c024071000075160803c10000d100410346000a542c401c00c023600c002070711039900307a6444c078800048460811580c0202c6c4104802034041042c040762000c441b00811540c6030081c08645076014190414202c0140402c070010198024820480985a130034100c4040e032500206000c10200d5030701c401d0340842c040742040185810301c2c1c012503580c1c83c1d068460340c2e2200c2080007481b000358001e00d81c8404000e900e07400480d0036510646910b004e40080c10040d81c03100030030b0a00c190000302d0384001d619601041d48480001a41040801c07500b04d416060503144040400081204004d070040c0080003000b01d5014881070b15003200d1401311403102030f80c0d0b42070405d40314801d00901c2d000030160380000d034943d0000103240d85070201c0156071103407001e0207071203568000300c010411541028001d080b04109840c03000803099200610400350346030031104004c5ca824949072442e210101600c040c13a00e00e0301d400145442e6150301d406034819a00c09403040900d001c200d107100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 182426600 1250 182425350 182425363
    0x902030607020a0c0b0f1804180b01090b090f16170106021e0607020a0f0c03020a0b03070e010507030804020d1a0c13050a36050c09040b030106141002070902030702 72
    0x100c601484c030b1540428041103010a9030b84030b007448000c0741d10701040d000084910941002c5402c4e80107841c2e03450030010b5150807204603101071250ba050320340355040400c0c1c503007541c80090560b0f000300180030402803ca6114004a904140703c001c100101c00200d210498100b2031001d0810448404c14000242059000403018a44001004441906118618400d80b0b518007904d0754401a48800e0408001c0355411000703000d245c0c450850805195a00c3e070102e111070005a12511035035102200b005030042d00500081c00d61442440c3c501c0c50405a0b90b0060080301000e807000e170042c1c910fa01c410080100e08617a8808001c4540300710340c002d203014910006140e000d45041035a15408940001e06420410861b01c150342c0043d03a030440c00300709680129004e001c00c4010120130346c2d9005a11020a03d02d1055900850900c12620344c0d039507040051005032010500030030f000382e02d000020001e5060044424620a0044614aa1010107000120b141c42038030b8100c0d402e224400014000090340000300c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 182427850 1250 182426600 182426603
    0x30906041701140c0912100c020d18030206030a052e05031207050601300b0609010e1303080c12010801061a0c0309040506180a0501061805180a0902030607020a 70
    0x1e0040f03003030350300d030f0441c0c400307019980304024440900680520303140560040c0000114481101c110302840c158480558903084044030258010149601107240d00c20070081050341d2085400080070310f5503010034045c0c07000420b0240419030354404100000e4030500074003e120b10b00b0724007080e044488170b20202981244d1080324483d200316100c82c401c2c025003074142c6015981200203445140c1c40c21401124801400240c91a000b0458498a030510280424200914000d140d0786103a40380440502c204c440301070b00702c2812503000900300882404050f5191140c5603051410300882e484071244c0300c0a40c010442840c5c5240352080020a14840560140046404601000500301a0a0340d0340d81d0070700c00ca01798a0000e4004001c10080f40c00c1076007085800600203051401068a400c40203d032006054a8020030f0325192001041001c0e400800e920090240e108108041c0380b80c900003a011240c0e1011610340c000c920000036441324669400003041a1b0086c0548282e450014402501c80513180d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 182429100 1250 182427850 182427853
    0x3060803180a06020714130b09040f05070b04150c052406090f070503010e070e040f0e1b03030409050a0b04060f061103070c030b0a0e030a0c060e01090c170309060417 73
    0x1e0008042c0c0c8002007120460380e11645c0703a8074800c004004d07c100d5003240701c40ca0b200170361501e985080765100c1c006018810380c0992844000d038402e501e419420021940e0008401c0282803200303210010004040200c0000d9a06001074031034086d1400504148031220741c442c50244c80418040d240e04c042c40350a1107003100b258920055643e2107085c11440b4001d036100400200240014803040303504000b00c6810202034108450140c01c100000303001e442d6080e1400007803d032103075406c5420180800c010808140c1c901e940b55111034501001c25680d010300e1090031310207612500810009212075004648992010f0014000d89490b480e006940b12030500c030742c0000038030024619100c0b8201000380c07501c03240d010502c3d003102480c40d11040d003855405802e080199a648042440d11001080200034001468880302d621101c0c60415108031995481d0b03500030f40e418004190001420300c00714400740e0307800700301c942d800044441c6120314501803180302903000711001501041280d180b81a07200d40783d03490700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 182430350 1250 182429100 182429119
    0x1c1407050c1525030e0607050a0605040f0302010c08040201021209040b0a060e0a0b07020310020304060b03060403090609061716050403060501080c13090201020c2701120606080312070e010306080318 87
    0x10060688500f410030040d0008980c0c4503103985e24540782000b48001c6009100300c07082c448854440130112a01520308581200d1000e80c20000c00d502130140407031303141003414401c40c03518003a00040d4070b80141074124403807410005041801996944d010307e001001c00361003081c2d240e480c1c80c0c010784000303001d100262298100b40c90004071030b8610001c956910764007401425038580b1152511000e90005441245c0103900c5145030a40c68504208851083c3e02075500d15031154031345100505140e03c1c81c1c1111080100c1c88615011190100c46220b8101c1003d1845417000f807400c410885d1280a140c000a120900707281c00002c6200000451b1040b40c40d04a5000704c0700c199000110040b99107611000780903811040c4070040520b07012100c0c01c44d0a0041286003840c0318a00040007813400241c10104e10f0400e01c0c0c1001090003918400c81020b4a1494010351174817407656035141202c00001c020800700002038032203443c580d1003074010b440240b410b042280c0e21909015901c500305001c1220960083c0c5219 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 182431600 1250 182430350 182430397
    0x6051e010b030a0e1218060f0706060e071d1c0f140c0a0501020a060f060b040602010905060702012306150d09260906130305030a08091c1407050c15 65
    0x705e4041c0c2a1120801020310b807011071a80c04400760b0741c0300c41843c0c0c4880c00f030141c603200b00e080750010a2614450b510000340705080241c251030700000a01120100b010365a14030503074002100c08420300c181c040783c840015030315042c4049000d0405507402000c0024a0300d14204101104441170030206800703007034075030348400c06c814050000c081c1d12469005030b005207035090224003694041001140340e05000300e00c881e01d80c1483d94096005512900050399643c16100034080305009440e0400c0b000d01c004d2210283c070104d00c1841c0c11203842800082c0c0041d01c00b050b100d5594030206d84445180f40d42d480d1700e8180301c95042c3d0040c490f000050303d211300341cdc90040b518a0003a41602440071220603034142815142c1c1c051240ea600300c1c14118940882480000c004900108041c0c48401a036684040242c6840c00000e404d10b0205140e0074001d48611a21001c82a000031950500189809405449003070398144145030121140070282c014048030f805c804406842001800d6807001440c80000304c0e000c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 182432850 1250 182431600 182431603
    0xb0301111e13060305071e020c0a05060910080a0216030c0b060102150109020c03040807080d09091e0906020702301912110709060e010512060406051e010b030a0e 71
    0x34900e40b0849003425850921074140260f0040da08003085207400042240a644080003c1000ba501500941e00850041c0414540313041d46001038403040c1c414905084234540407a030040d0300f07024404180144080020101c1003154183e51034003882c44011000c0c0081b5080107801480d4104069404242d80700c00143c895000143c101040c05100580f101282c1ca04282080250000140d100603070108008c000340a0740104140b1014240c1d50003e4011894401300180c041c100562090442a042816481205510f044075031494104180d000c6088401031805100911441c08002e500010b68080460b4250052161315040a8007100c404500064070000540d104080d15014006618862010000954208840c1107699160620401c0c0301c29540f003ca0400e0403c0d0040d104480e82c8281c20050035141400c003d00500307080e01d005280101c8080007030388520000b0805001e041c0c0314404070b80030b0094a080d004106500b95842d101030b5840d01040e401075402034400382c0c1080d007019200c0008820 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 182434100 1250 182432850 182432857
    0x1b03010b09132c070515090103150e130f05030703030b030d090509010b0a0908060703020310150203030601030908130b030406060503010c170403050f1912051b07060b0301111e 77
    0x41c3d81c240809071a0b6010110075000c1400201c8005402404000541e94490060220241100031250b030340b04c1100c1c0c0c00040450340203802030b04040c001c180007041886641c00c207841c0c1001c3c0d152450540e504450808846d10b00203140000c120b8440010000d05065040d480000003050490650300e03030038000d41003100e003121540240c41d0304c0310100004000b200405c2c001400c6001e21400c16186440d56408820f08191084420b6800300340c00000700070324201c0e04825040902000040e01200d000130310700003541d0303000040c440307810315031341c9c4009071705000d81e40d020303526520a490710f600031341a1541d501d41d615400580e021605941000c07008130340b500e81030060041310021942c44480d6044000403805040350050029018400100100035220341060000e10640400b1035040c821500d080400512000100200180d09417402040c48821a0080d0450035000c03c1001c1480e254a200d042c110000e00007500c038180d042d840c0045c0000306031034040c0070b48810802807030b440342d41c10341d41d4a00010300e21 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 182435350 1250 182434100 182434121
    0x9020a0807051809060d020306180610062708010e070302040e010603050606060711030a0b01031a0f0601030b03070f1e0603060803090402160f142509051b03010b0913 73
    0x110450428030312404d080c00050b0780071000510b0001c140301e054020a080c08020350300e000c3e4880c0b141c0d070700310b500ca10104149a007058042040002c03035407400c031005080250321100410200101c010340c6004061608051002d46030b118000c000494002d54031a40e546918842280107a040588400341c800c03040c07090f001143c0d00200906259030380c0c1001c100d2a980000c4045031105844202d1200b603403420049180400d10403000400d565040d400c2c110b08007600004e425569510f02801c000349a4022454035800c00c0080c240401d8801d40794001904060b40741c1c00c1500519051280020000b61089050025510300c5010500e885d40f50f400850035174980d03001304401503008126109050030190b008000100f0b041000c89490704042d2344020164009110940300c1044040b802c0101a0081c13080511a441000b21614501a1748010510704881882410b0340140d0b00d00000d0394a002c1382c5002d05011400013101a035960310340c4113041264005200c0c2c3c90180d580c1c0446c40e115a2058400e203003140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 182436600 1250 182435350 182435377
    0x15140a0c0302091f180602010603030e04020c1b03010633020303040506040b18030c0a0209012903090111040617060904020d060f1b0509040b0a1508060103020f0409020a080705 77
    0x604441d0350305400c2c441072060391405c008410050b005540507040d40070000e40020f600100c0c44524500b00180b0548062a801c0e12803441003007401d280200004802c000c1d400702c15082000303480020002401000168400001c030340d0143c800c2d8011230500040d404c880051681099021288024200d03030368003084800411690284003c02e01040e000c0048550000014441034000f18110060714110b411251070300f48103501c160034074821403800c240d507103014225a015450b4001441c102445510490002120081030004003003070300c0c203000303401004010240070222a9a1a03917a00d0003080389002940f42d117040304101000c18000e20b0060700180c020bc0d00240452183d8030140c48490040100a469189444c0d6900701407407114860b00020081300704c1b5845840d00d5040714800d0100743e944038a0035500c03810342004184038141ca00356003540d0710703ca03528111010741d603104016030003031064840c020700003000441c001a030b2070701c0c64000f840103110316035554686840b44442601c944c018040d4103d041c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 182437850 1250 182436600 182436619
    0x10e0105090d021c1d1309060506100210020c1005070801061202040605030711070e010b0d050a020705190f020d0b01080d020706231204080703081b1615140a0c030209 73
    0x80c4179001c0c0c4020303c0c0d00158540d808070002e00011b401102d9182040b01c901c0d881d1022030701800351501c10306600c040156210b60003642410002900c6120f403c60703131046685c0c0854401c0c0c0c4240308101c401158404c0030400c003d0b07803c1543d0701070583e040034810701002131600d000819400a5a009950485d40103171100d6045846201080d02c00480013183d0f041e00d071080c148000751804059074610f000b0003400e00e4065844503081c0c0710740e0646900911109145004110210000f41c00041c164004909640e003155250020300d012210100c840002039800303100c0106d4603092100c00c134402812903004c10b04540115074044001d03600da2100c1c0c0701f84400300e072030850182c02e80280780d00404442480024113525080c03c1b0622019100340513181a648035401207503a000300b51f004940ca07a01308101240e10444840400c1d5080505d2085441401d410030605e115101040141d0450b010003640300c080038003244600c520324204490088910006c00d505050101001c03900a200b101c030312210180000c4031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 182439100 1250 182437850 182437903
    0x10180216030e03150a23010e010e0402030a0503030901050a0e0c010801030b0a0f06120507051c06020a0e0904050606010f0906081b0f040305210f03061011010e0105090d02 75
    0x280c402d00300510b00c0d054003d403965100f0300c29410301c2e200c2c450040700900203a80640401c101060f0748840fa10030448440c05001844103d10340c040250440700c01c85500686542e43d80b02003814000c0942000b0510721000c424403002000c10340085100b415907800070451490b01100155450840044045c0441d03500030040c0b0124204000300b03623200070014008108203105020001c00c23030700c0541c02010082481d0345007104021003031000c200184411076480c4d501c140142ca1100752020000c5000300000e90003e00c8548035070090b80d0380d0080c00c8004243c00344130b15060420540313481040719024002881451051b20040c020301452064034165510482a03030b0f00d0700c005c0c0c4100301e46028901d25501042c0f2540c000352a00c8002032015600c60307400f41c0701469442c003085407802c48044108441500c140900c214085851040d00d5100004840145020310421420381d0040483c83c03103074841d5400c3c030210018580b01504800c0c05011000121a002507015804036160200e900510f04040c04d00050080d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 182440350 1250 182439100 182439107
    0xf250308030f09031e0d051f29040914060301020c1e121306020105060904020609090403030617010c02070504110a080408040506031e130c1a070b1018021603 69
    0x2540300c903d220440345441d81002d0484140c0380016295980110000342e000c02030307070003802401c0e008110340710b05243c2d060170040e11504010550240c1900b244540440c0c9020035015985103480c06c1c20a4242c03035440d501c580c1e83c440500454404032642c10300e40808074625080520869221300b0903840a0300b0444103e4820b26458000303242c0c0c4400c00d101c2c44084c40716008115000b00240f400c0081032076000d40c50010042c2c00d5a5004245520515055042101684070141210403000045909100070785e1146015001050590003ca4a20892034200540c94a0541c4a42220951a0215408903565804100595a10103640b008000090281d00702040c0141980c0743c01502c07400a15007880d40760740104980b071300112607070b207c2840da041444141a8008003001c0d00045400d0020111002540701c0312600506807007a00c18000d082580c0e0145880d03070b0000d46011551100201c44031382441da9074014550054060030003951850703041d0300710b1608107108030751002d698468007a181c0145034600380c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 182441600 1250 182440350 182440381
    0x30703031428080f0a0501030330090c0f0905040206160314120a05160207031212020c0604020910230f0d1209050a0b031303020c030f25030803 63
    0x404500901c5042402249800c920b0070710808180e074442c1c0700351802c00c5500d035034682c01070040a15103140c5001800420350000d40c00700d081420700300041004507100d987c4601c1e68020f402e200c01e01494400c01104011442c05020301b128515400c40042d1902c410722102215029030b8000c0d4842003c101c0001c429941020010800b400b034145100c00002070403540400f0703403005070b88400d5944044200022202c1922900d1340044060a5003a90091100d00180d42c1c6c1c84c1900010b00803c2c141e5103005056481030481030032800303c81100355112400d02e0301c03403a903409042c0d4049100d5180b500c0064203c80b1803000c188e04a03683c010043d4a0041d04548a185d403803040082d1070340048104d40d5403001a201e070038030403580501c00c010300388210b403c0c41e40050041d0b0180e00310611440748044200013000c2000d05594000d110304003001c041c03134414070381030380f0b80040c80344919014000c01c01d2030204031201040038912501280000c00c1508280d41c805680940c032400b00920348441800800d00e982c45200300d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 182442850 1250 182441600 182441617
    0xb15130b01020c150403171306050304120c1b060203070c0605030907030f03030914060f010b0a09031b0f0b0a030606090315090f06060b0a0e0604030c172b02010b0307030314 76
    0x1110302e0701b80c176503d54080341c11030400c0e0001802c01c00220b80c03551101598a0b8001000c031450b100b401c0d41004c1e901e402900c0e20140c0a1000c112243c080e51040c0700d40410781200004640c24014001955488042e4490b080100c0980d5203286466001505600920407207225913000000741c2015403c41d50b613440084a064010342c101555810744600140f18001c0707540741c4a09110082525140040146c40042d805800000c030017030060160f851103642224180d0144ea90056840e4908034240600d1030303c3c943c499112641610112000045440d151401130001c500d80307581c180951a01c40c102520342101502c0000e1401540e54070004201c0c2250b846150745a104c0c0e59140d501507401d03103404055406580106150300e90009074a0f40c2603800141d1202d031850103607902800c02d80346071504060400d9602c26030300090002442002071072428840b02080526900203c26050346560140d00c0541c000102607000d50310303082100d1070629000413000216076040d84d0b10302c0303000c403041090480c0740c021411 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 182444100 1250 182442850 182442889
    0x109120804051006060509090a0614041a0d0c0f080304030c031101050c151e0606031315020d060e0612070521010603080d06050901080307030e06070b15130b01020c 72
    0x321035003d00d41c1d006040040400b41e6035240c42c2c2002d501008881500501903000480c87c01c1003c0081081c2c450070007514900c1218000b0704035501a208605046003c3d05490344408207540150412900038441001d50b480001030308401c0d81c40d00c0400c0c0c0e4030b02c1107000150070186d011030104005084142c41c1001003c0614000b82000311030f811162511195014641d002041034040209081943e24280700d03440e20745881151606040340850502c0c4000f504a110f10700105111000340710240c1030b5900410f43d0f8010843d0785000032030340400200524042d2002c103c00d0307070012a1036840c052035852140035501024000951402c0c040200100c6600068071000d00c014541c0c40146000b889440011402a81300310b540751075199401085980035003000740305898481c0103020094001055964040d450300b84641c2103031552000603111f001d0140004c203031014030340c2040078203440d0300dc420000c02c071b09407420081501d50404c40c40c03d80303000350707103150042c0d00c608403000c0e251070b120700d0801d1095288803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 182445350 1250 182444100 182444113
    0x1a0405043b0a06150b030a0615020102070c1e031401050106020d0e18060a0f0311040501090c02030313030e1e100801050d02011209120c05070503010b06120402042a030e010912080405 80
    0x551500e80041f82c0c00345420360f480c10104134039860402400f41c20901d0b84021850324403e075a50b551032050501542092a110b4203038044190140406600070315007001b1080300000900c1c034418040e0000740a000010b0042002003120302d8002d800360784114100504a600e030112501490a4a100c01030066900840c1d8150001d29060000e80c80f102440c043d4082d280440c1782001400142da03010391000071007503d0302d20269259507000c0140c0e0b81182f400d041800d000d80b0a4281100c00c2049008802d40c800c0c06507003c0382074840049846100110140c036441701030005a141600d180c803091080c55005159011103000540c414142248103403007000700040c00f1a0301d6118142c1d44101c2540440c0410392142c00030060090410451000b420b04400901c427241d0070700086034250246824190407214064045001c540c3d03260001100003002d400b4000300b43d0306907008401c00420420078100421300c2e02c0e1802e2908d09060185d0315040c1d400c102c814a21203840e0a04640c3c1c800d0060059030f0a0003040d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 182446600 1250 182445350 182445359
    0x8071202070203070e1008010e030a0f081803210601030608070501050a140a02060f1f090207150911040e1b010807020f07030c060807030e071a0405043b0a0615 70
    0x9601721070250461600c4078068908208081c0e084803009882e01c9081d03402031021444541c0e000c250700448000c0c0349420046602c2e0f00c1039401101615520700e070020b010101d208004119894011400410403034020001a1154001074080312410f02a1074141c1d04040300074005540244c00500750300c030a501c1c184c402c03040d240021500e41c0d000182143c2c01a001242440510140007210580100c8095426406044100078540b03100700300f84681101c454012401e0802e015007140c1c2c49190811111003840311302c0c07407850811422016550500c0c4641d00e0701c0107212045c7c0c4001440c51032070701d202d2a2200d580e62044011341d4500002010300c400c41c0300d50440144100e00c01c0c4004401103100714121500d8070b06214010706481d1008044c8800c240c43c01066030110100060004219501d81c1c41d07480705028a00030b0066103100d1500500e80180c10448a600e2443c0248408500e07154142a080c0b030207412002582c40a02801e040020207174450501034002c9021079010a00da1011000c5c42400560348 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 182447850 1250 182446600 182446619
    0xc120902010e040c0e1206040204060503120316120e06011502070302010203030a050604060506070f0218070c030f050408070e100b0703020d03050c2514060105060d05041b0f0303030c0807120207020307 88
    0x903031004010507005030b1f050000f1400c0c18007409000c1c20044015050f042112a00c0c08450300000b0710345140340414400380600e0600a140712142120b00c42d81c2882001104100150b48250a1103502c0c1504029522921202c0c4041507c030305590f4168007a43c95a00c9034074002c070142001801565221f5650100010190f94040c02044801e100e010025110f02c1d40c0d004200d0b2803500b164904103043c262750300f040401c0340c2c000220350031039a01d4280b9100014014000315550700668118a400d40b01d10040800c0034107100e00079610450b0049010010a03031580071030700c064001e40c00010007590040c0c40c08410180640c100b541d100420080541c24000301009031707800420403c1c000d003100301c0c040003000103000c2d0100840303100c0121000189510351520340815454071030582e2400051365034402080810a40c500c00d007090075610400e40d510191201280c24103444248000c0700400e14095901c1b00450050054500c24900c50302c40c2003a8a11038a1494041e51003014126410b000e00040860403045 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 182449100 1250 182447850 182447869
    0x7021c0503181507080a090f02012102030109060512030a0503010513020d0c05030613091509020a0801060b090306150d03030908070506040c05031006080309240a030c120902010e040c0e 81
    0x14080709a03065810104000f17042603001902e80310803e4100710b108070115200380031544034558280303807030602000081000d085007090441107070f2019000200000c0c0c00d80d0030f030f000841038650888452000b1034296252555a200c0d1490003004107205000400640c54041c002a0026a0541c0c0c09413a0401512404045500305200301c00810000f109000890a042c0b02e402c02818204404114130701d41900c42d048a00c9a8104403400a511001c055085407684400c1300001c0500400a0046039200e80c404442c640154080600a2040c2070003d581190744044107003038114054019886030702140c904401904040c4000d40b0301d100100440400140c080008610031030007031038070490702d50034001054203108040008180c070a0502a0a0044040100846e100b000c0704441c0c0841d41d01e0307840038101400040c803100c011655000f10f075110b40d554050f00600c24100a81da5000303030250030540d024007250130751038010740080d20f01d031040d40715424146d004554074111400c2030140502c03601e001504640 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 182450350 1250 182449100 182449123
    0x5010810031b0b0a12050114090a021324030e160b1e0d0b041b020c04021e03070e030601170d0f0212040b09030c03010b010c060f0615050703020607021c050318 70
    0x1074424a4841584450b441084e02500b44506000d908d03050200004140041c0a002d04003c103500143d101e122100e036600715001001502c1c96035109002c440300070245c500602024038003190a21816611201c030104907182c200c01c1c880656401a41401c0d04d8940030341021760600004400300c00301c11104900c0002401e039204494401240b21035401045c801036030b10351590b8035407001d44010a0390105801048051a00701c0a5600507145c0040003405032500307800d0090190000400002d005045070f0203001d1010380c1c00d0580885400e40d0380d92218840c26848003007910300507001800d07060481489180d8640e03458200348112040e4081030352025420750b00580c03001400410000320071085041c00d0058030031404084008000ca9103103040043c1492a50000c0142416a50300446002d00c1055028134050100150002011070b00d0000c0503041d41d2015109070054800c3c1c4002585881c40003446091455100400c1c5d00054005c940030b60703d80d04003400101035841c000d2240e101c0d0500c20050441c066 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 182451600 1250 182450350 182450357
    0x1030804030f230a0201111f02130e0c210403050a0c1103010c0c0c0b0424030204080601091a0a0506160201090b0307020618030403020a0e151305010f05010810031b0b0a 74
    0x43c2c01d4800501104502c0040c01c1d6645c0080c00e00e6a6909a01680505600300401c009641c620180cad40b100d9006c00143c2040500c1c8c200a0140111807071800c000d4032b00000b04c84c50088002d2144101040701c200202c5005001403c01c100d4030901501c6403c10700019403084601810004039140020b003510390090442d000101075100c20414020f42401540083c030880400e1440c00f803c000c00e503101440c0e00c4a001580c81e0940091718802442a0704840061032400c00780d490b2540c40b00c0300300c2c024040800c0c0c07004407001c0d81c0c0e010902b1440c00c3e03241d00d012107800030305451600c4226500f60034004031521003070b0706001002c01e0000d20440c00000940c41141030380e004c0c244a20302120701d1203a1003804c5103c40a554000d0001b800180c1781c20340f860003591500c40c3c1c8190300c1c0d600c2464000e4000242c030720303003078020007414402c0703034075104c03540259060b207440c1110b5420007070b00d442c01140c0d000b0080b20b014041c0c10fa140340801c01f02d240140303030341450021400c28544654031012810321030741c840810039000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 182452850 1250 182451600 182451613
    0x7080403030c0204020c0f031e0403050d0c03020703050105010b0711061c05060402040306050109090b01080f2508101506140d050402010215040812070801050d12050c100615030501030804030f23 85
    0xa44270391210100500c03910701c00300380c206411a2156a03541e043c000382d190502524054a9041c18002c02c002002164000000c0c8219038503001d04a066030414502110160844412002c461400400307503200fa24a003500348030f00020405800c00038140240030550090380c20040031010074205e00850340a00008a004035004205141c466219201603001c044036801107645070010080c080307000004240e035144441082e1246070881c05824520fa030103a2098842e00290603000140380d0001c0c2800c1d201e0f1120100450303550b1100355841d05103000e991120190030840307000c42c8070070740c1c0c001070b0454018811111001b10324056801030744c00030b4a00f0344904002103201c01d400888510034584c089120302d4022001d500d08000b2480030511a10f000380306032000c0b8241402580300e0001d0f0f511080d8104200c0d600150034102080041580d40682c02800404400c5070010a0103030040904803980400d0b41071a161540c0c81e001010306042200316050200c0c110506481c1003a140f4100300201003401a048 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 182454100 1250 182452850 182452867
    0x30c030f0212180109050703080a02101d1b1003150f180605101b0f020604170601090506010903080708091503070807020606030624030d08010e010b07080403030c0204020c0f03 77
    0x2101014800b54985c1c1000c1588000800208042007101c0d44441d4240e1503c44400f4242e052481ca00740c8414514039140d1803485502505d502c07010b1640ba5482618440f494428001204140d444d4249421aa05481094025102e40d21010600b160700985521181e142e0880d01c605030001d521000b52142c060340e62040302c000d940b180c20b0040908a840038519004454003a01210301d100c0a4800010804035800030b1260b0b8409069465600515007a0356039103900740c1a00014007000c0c0542c0b01d200d988000320b000c151a00c42d09002d10416118061000d01e1561000c0c03043e440390f00200e410071428046400103484494064030b440910340801d9850b49848640184000002032480046601410520207183c5012410396040860850724200c184406208640c20040d407450154261003120035411019a121005605a80c0e51030203000c0103036a94403003c1ca45008a41002e08017103010002040024022454114201c0c4041e001505185d080984227091015100d11002c103034100013400b81 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 182455350 1250 182454100 182454121
    0x3161806031101270e2203080402010c020f030604050610081b041e090f02010e030309150a02151006030c020604150c0e06120412090f090207061d250303050307030c030f0212 76
    0x12064100111030b904560501d4800400c4842c0180018bc1484042c200d40802d540b244001c1554403140a802c81d800b901b800d10304103580e210103c40068a040b0158004156108003280721003601079100300b581400c00101d020400103100031042a00e9280e4202445081c241c202c0c0200013030140542402111201540005000548070783d91041c0710b50020030001c40c0300d58400c050100c00c41d01c54801c0984490040605a1a050a9007021694101d1010410004c21104c1c00c480065614603034040c414442030070340c00d07070341c58406990003055030b20b02a101c088003035110382c4030048081031807070700008009036500401e1440e07000f40c0900d0559103081081205006050001083c651220300d02880344614082d00d41151110b58040d010801383c00040d0740c0300384800c5802c001c985880001d61032540880980025640f408a0001103100c0c40d0f8600581c01040b480342c081c001103d82540702e5138515034800d1421002401d4030107000c0c0c14036a840c48101586506031029000d030750340400408980382480d00810703 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 182456600 1250 182455350 182455381
    0x70201140406051b0106050307121103031204082203060c0f09120201080405120324010e090105040507091502013612050903161806031101270e 63
    0x2030100e660100020080254040f08803884407200c115200d0707681e040f007510b05025100715402554148541c0e0008a510f1000203041c0f50705611030400e00c0b00d810f03404030a050b224000c5442100f00705500000240118103054010224801c4980c03035500054a407000004021000f904241e40440e528918a0310f00fa411952400c4000018100101d6980c42c0211410507100c1c07814000381006000d50200d0100074081102c0305141c10740aa08945a103401515000355480d00c00312103500345c0b10001030350500d5011b60f5000024100180c58442039038240f03410721018181c09000a000c0104080001070f0307010603610701c801070030050f40c004140780c15200da003480000c2d1400e048022803686a80c00224180d640b04c140c1410640c04507040c0078501c20300b0f60030ba495000740400290140142030388441d5444606088109890785c030803080340080703103041d800c0b802c84405010040405c440d0960b81c200560103201030180403000700c200007070075007420b030782031300c102021540300012250070001800740c000c5501c2810f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 182457850 1250 182456600 182456627
    0x4030206071103011b031a1c150f150b04031a0408071202030408070f121101020f030a080109060e0609070e0415090506100804080f07030306090207050a0204060b040f1a1b03070201 79
    0x802c10070b5140c01002982612200d54040c04203041748c6503000400c02500d1040303900900c202e0040100c506034020040c00745c5440000d05400450f40803020400c554440140d40541350030a00703085031f00712505041c1c0c00390100588240c0743c9180c1403148100060000740b1410036900940c0c0555150303482c1001c818644109600010001210001d0501803149140892040c0301c4d080740034a11418a1540141c0c10075500d14604c41c000e01000554985c1aa04501040d04039036504908005481e90340d442810b101d041903850561100041e4042444948161660040e841c0d00030400140c0700a01e400e02020a4441d5100100540e1108200300c02032034003a00f482c0c4201c185013031080040c941aa6802c00c3d80c881e000c52400e00700380116100c01814801d61122024104c846400c40d0380f00031030305140307580d1501c0040072440365040a80101c0c1040da004140c408a4003c090b50518460410812018611001d01180d8031498248940c69800034040712001c0300c4040d2001a5a58180314000180781080c0b03040b6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 182459100 1250 182457850 182457881
    0xd0f0605070e0d150b101e0804020f1207050406090f06080a030c0611070204020703080a0f020a05041211060a0c0b060d0209040f1a0c13140604030206071103011b03 72
    0x201210503120b008041040c0c40e80301c004c08140c1c1c800441d150700240b040703158031900454260f41940d425900051420024038405291034001c40440008030f40310542118000d40084841038410824104030100100031544001958200381e2240041800c4032941e500c4248401c3d160b9401200e00b0400b846524094102c41c4080c3c0600381054030043c0405600711070080146981e060108007404018040d24a4160b005205541e16240342c100240004400e403800c2150034030744a21003c004080e8803c0300e40c0030034540c982504291402d080c800b10b00c401041c0075202403c0440c42881950f440b00000d00f4418440e40300c80c0c2e13020300c2e5418907100180000340150700138128840c146000d692010903441e81310340c0c040a891504083d5190403410100307080b0190183d144182c080c00000c40c0441c01808110304460344000e080d80d501c02034400c03514034503100e268100c50b04200910150804400401d10280101d0000400c02c10f40300210382162016611490341018041c40c11845c19818002d11802890519 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 182460350 1250 182459100 182459117
    0x40c09050f0d0b040206070f08030403030c020105090606090106110307020a03050a1b0b070f05150702071401081e09150c07030e0d022214090c0306100602030a0513050d0f060507 78
    0x1d9034040c141d0700113000603201d4100424042c04000c0c002c41310140707041d40404020f86034100b9280c00340103846491102000765007004000f0300007860011302c1d1813060000900c0100940d28066080d505480184600c1c50207000420603c009038880980090055201e60010301082009081c4011000c9800c004500c21040d451003c0000c070788010b098a100c00e4002da080384114030382c0d180041c5008545191040003103507410400851a4005c225201203d98003513042062507040401150786040031a24803240440d140c070201d400c40032000302c1c9584044d440003100c100c003444d07682641c403016046900003200340e000180c3c4000c02d6480004262010b07000d55200c89008043c3e400074845140c000400c214082d1b071401032908440c1240c2152800d502c0b040010021400c1c400b0406440d2030307419407428020304c60b400c0803448010301448003400729800c540c0907504001215a00720350300d0380a50840001e8007031164000c2440c1c0d844800020b00f15104000e201e400301d106207403440035540c006001200748000c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 182461600 1250 182460350 182460353
    0x304150f050a0f141b0601030605090109081605030f12060a051c030e2103070605101a0304020303070c150f020d0504060e031c0f020610030c060305090705040c09050f0d 74
    0x45440040400c00341894411002090741800260140c01717104600061201c005509046003c201541640d00034002032209a4540c0f01d95401c1e5a0070a400602c011400c00050010300361850800c0030180c428030680c0c0c0f91000d14038107000b941d045140380c442c5078164401032084500d001d400b103000400c4160340380010944c50350700f00303184000c1c040c0300a002d1145600e0081001e80d0f46003951040342002c140c1c0302c0042080701c002c0741d80d66000000d04540342c82c0b070a00441d030900e48280d07007641104e55070800800001025010704910340c1000d8022038042c40107102c42c0000800e020003036005041c003a4848404590660f100800b880e000704880019500450600790555511100b02d41c01c0d102c6e01e041402ea04203509010034601010032011114074207001c0710300c00580c0e500960b404134902955084400360b4817211030324800e11490b41700040c00c2581d4460108003e074026040564001d609100340d903480d0b55501c0c04034054410020840000a0a10070284a2840d085507076103401c0c107042d25a0b40c2035041a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 182462850 1250 182461600 182461607
    0x14010206010b0d180606081005010b1305010c0302010f0c030506100311090f01120e2409061308070507030b010602010c0201020f0912031e09040e010506090a0b120304150f050a 77
    0x154511504480e407614031000c1e11942e0300800c80c404c0741e4010801c2000c19980da0310345031600351540001c84050b08220000035002042410745103101e1740403124001541c503210043d20141e020301403c505554030355044400d0350038207200364588100343c3d40380461946884010450480084070b40d0314185450610040c601107807100c1035a151110603203440b001e850071040107840203031070360801c40900c9007001c0c00c181c00e110002c107070300202c1242c9041d041041103c48440c104260002c481d001542d511100004560320107064019000c43d00608046140603400c0e2070f01801d1240039081618000340110040040c50fa0903c40d0307800380c921900c001c504103c0303101c0410010b482003078592881032072401c010f2000c800083c0210380e008240350414001c2c5284c403a02159454000030304051190303207054034042c016001030091034404c240042c4001031036507a01d1039070001485031070103064121005010445019000304014006403040e001003e0b44040d081d803004000840c01d200c0881005024010401050b40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 182464100 1250 182462850 182462857
    0xb18030d020a110112090c170f06131a0f04050f0c09010e0604060b0408010c020d09031e111806032419020909071206050307121104180c14010206010b 66
    0x1070080030307510341e00c0d00390004170b0b43c4125551800c1c82c020300e060348400800401e182c1640403203048041d0b00707960031381e410012920385c1d4410346082407682189000a404100511100e103a1900c15000d2021103038003075200e941e0140d01120401c0f001844e4600380800d2207001c02c11241c8407103c240040010b400094046404090184600c0e8880c030f076008045900d0b651690850310203003003061046904c482d6242d0603c0e0107440c000801c500580942c507980c02003c0e200c1e030f41c0b580aa0f03400903001d407501841140030f010560321400080d104141e486210300790302d076541126030034039000000c01c41c10b16040402c10542011348440394450140c0c0081b000b030081e6417500510036030180d90811400b14180685502e0000ba2107418900c503805440941004031654000340308810804c0350182c100b142c1a121005d06644031380a002c0c081c01c1402d56103506001503041002a00050800f82000c00ca6044107100c0c40000300c6200803c454130300c211401480b00889100090f000b90383d0910040c1803a5141c0680c041680c030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 182465350 1250 182464100 182464103
    0x270f0303060b03011514091915030510061d0301020a0f0810030c0608040c0819050124120201050409180b090303010605180d0b01090e100b03151306060b18030d020a 72
    0x100c4002020b4140410005443d191f44000d07000e85103141100a0360a402035080c099600214043c004082c01d03a8481c0c880c05129140c00703018801c80300d0074900240e651100d035000c018040a00c400041d449900c1c280040e2034110304e2600c6405d1014080d550143c41c44000921030000940100c0b008c002040c03611629004a03030b0f003030a000100e52584d0500c140000c503160403001c024030420724003004020703100031050391a034002e034000c001c0c0e54002211400b07a40c1d060700b80d00940044510040c0080c3c90091a41000c0c80d2050428a282035030706c00340102134811240007142c041d403240007a00203103c00004403542c00080040518915810138501401034000e4070a5003040900180c100421a111480c458110720b402606400c15581e417451201c003c0d0000303018500841c001c4c01100b540329034242c015101880402400382003d22500c00116030300800051070443c2c0c41020500301c401059203031180c2c00c040c0c9a050490756440000544070444035480740d45160003035200248a12410703070b01282c605440c0707 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 182466600 1250 182465350 182465357
    0x3062712050f16080301060e01080f0403050a020a0b09030301080706050301030b0a02090a03080c060702070609050105030f070320130e0f0f0604020405030312090d14030a270f0303060b030115 84
    0x2180012010301c00350042d40306180c03c1500f1101904140014031000d1812126942d40c1d40ca400e0035048011180d00e04169002e801d0703a0091800328000a019001070800d4005030f00c11903d0201c1c00352034201400d141525403c01030380000005200108043c440e25000c0c000b14180303a891949165980c1c03900ca40007c00031440d0980c0030030755582c02d5941440b40b90007542c11090302d2f0b0700c1e5040149600d849a00603101000903110350080054418061407810701240c505844441c01c5540c1c207522400d410f40001e1050b003c040ea00c404c02e0140045140240c94000290800b06464140c0c07450b811300c05913007035046000311101d410304012070192070018903030340114585440d10701d80d10303050007040280c01990080d584c1400081141d00d200d11200d0080392040c2140000ca9018045c0e00e1410344410000b0b107000301c0013510800c00555008030302d8100c480702801c0c002641c0a1244500790300c2d00c14850041d030444000c20f1a0301d034981856810b00606020304245440c03107145500d081e42c9140c02c2006498048e060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 182467850 1250 182466600 182466607
    0x10050a0215090c0d030e040509010614090c1207050a02070806130f030c2a0f0b09010525030305040b06031606030b01020703020a032303090a0317130306271205 70
    0xb1541404400d066078005458001e00e0681480d01909002c0d0030b000050185142000155101005000d0141111504412940c180a908050000d8400001d04882c03407400200705055826881140380351081403650756054407a1503001c0300074105003c0c3e92121000e540840c06200c410913807041a880110792081c0e4281c1e2031103ca00d0190f0360080c110401074901060550301041c281c0c4100a150244400e0484640380c484d00d07400703185450003003401401c5040c1d005204210407540200300a20500a1141041c510b0700000b14030103c5145422100320f000a4840e0306200030007616907200307600a50105e0207450841c00c9402e9070b000b40c8031035104000803d91600906035059000780440d801441d000703031031100d00c55100d0610101c980788412140d0342c40801100c1c01c03141c0d0140841175030840c6400a020081a40c51903c400c840304200c2c000d01e60600c0b40400c94524900c011034413010041d4840c0314045407102000c01c40140001c0c0e03051410701c20b044503401110004e00000e42101d00c03211319040c034940303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 182469100 1250 182467850 182467861
    0x31202121306150b030105010207090203090d03020c0712050a0c120308190204080601170607090e1b0d0203070314090a0c030602030c09061b070506090603041101050c070608040210050a0215 83
    0x15051950400031611081c00010070555044c90045041e64020303022034070220359644503401244400c4601202e01c0e0070400209402034401d400070801414000102c0716201e0302e800480d2064411503004880681c01020b49000300240d040141000342000106c50320050300c035031000792000400810b40410702414000c1101d100d021541990054000502140c9480d07846060444000b001e040010440c0d2095500140b42c8030311504030081070f41d49420806069449030820030b041e15603682080904104107010808040b080e500c05144a520f181d0703030101e2204218000c0700314506000c0c1c003140709908112000804036028042034002c581d03010030b0040c0d881d5179000402050340150120356030701c18000142c00060242c0c42c1039410f41515401c0503a0200755031034007004410300c1081c43d0f06030404c000f40009800708000c80800ca00406060518500d0300390384c0103569080c050700c1c2d042607000c1170301c12080c0000c0d030070711039007125040b41c079810443e01d03014154401039a40c165074140e007007191014500080c2c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 182470350 1250 182469100 182469113
    0x20702130c02060601030b370b04061d040204030b0c03062b0209180a1a0a0501060f0509030c04050a0608010501120308040b1503030a030507020f07031713080a0303090312021213 78
    0x288504220300400d0fa0110b4001c144041810b06410014148e01380640481c15000420848003281c0c1ca9440307500010316004540d03c0060181e6618075070090303003400000042204804450303ca9030314205140ea1702d1500c881000360b5041c0c8030f10600703010506400c4803090301114080c523a01546e01121381000030f035190302c40001e00d425407100e40c100728098102c0c1c83d000c04c000041001000c400042e0048903682e03514101c0c0003210700901c10b400c0099090b0f0040c081450086000b0060380d000a0156140800d900c4040740c10b40c1c6c415190041080d9841c0f4040090391000c4c424a405061b09850801540c101d54500824800d00948054035260104021403012200003c0002c102c038805020b503a12020745130000b900605040f50340b0400341c000d0802c5009841c0307011a07100c06407a846503840c8600103624105001a0b04017400b0105075000c00000460217050810910f04024440e59002ca805030b1549402002c241c9020310242c1041d00600c41140010a00001558070803503c0005000801d61424102d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 182471600 1250 182470350 182470369
    0x1015090e150411040801090308010602010c02060f0a02130f05011713240e061b03041205310524040308070f0602070507080d09080c0607020d0b0703020702130c02060601030b 76
    0x24059000004c0c005450036064004001c41400ba03210241a0703079880d8000d07400d0b100c4440e4542d005801803000183c4481480e1192500540054001820000d4100d120492808a504401e000b1f402034002000250381c8200072a69100c00484040040d040c4503122441c090307806034001f03114522404c119480200b101e45015050314442030f0038410b44030700d80038035500e440094070805000700c00d00c020004c80c1e02d589000c5030b008552001080e0300c040d80d002c0301294030782c009414140794680d0003840e8100000f40080078100c10030b101d0090007002d9251504001854500d130fa540c000e2903000224075102d50811030150380031241c001000030707a40c0b02c0c14070b410306c1c0e0b00410b41402000c4e41c0c4041500d80074003600140e00d000747e900400890341101803030382c4240c0750180c051198040303641c0f080b0114005070811501030082c540c40542100c810110650b1003203181e0800f200c1617030000b0790105044096150449140c0c0071107086120401c1403004500000b0340300e0100818846c141929641035260700e80303030840348 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 182472850 1250 182471600 182471621
    0x90b010c11010302090a0902041e03030806010f200609060a06061b0501090f080310060513090b060c030c1c0306030f02010c031101020d02040608060f03070e041a1015090e1504 77
    0x1c4410076910b40c01f264000f5085400b91000658060448400400c3c4007812001038a81585601c12580da600c8011680d1500e908036030400c002101c8021044038111441031036100c620040586a14901004680d00d0200010038401c900b40c240b2a04001190b00282030b000c1d0044400107041e101d010341c3c2000e031b0142041c01c0c80286424218680901400b5440d00611b00500c140c03030310403402940c0c44c3d00c02c48039070060100c86c1b000c002c2416004c00c051445940301060200001d00a2414030011545076411900203005140300c64011a100b12990842c414240c0480c2200e8102080341a007903856503401c00300d45000c0281404513561440003031500a100c442c001072010402954ac0e00340d580c6c0094003a40040c440d940114501d000441e41500d4407800042c0300c2807014000f0f00c00d00e890500c480c1000311019100b1380e000d405d034141001005401d501c1b0107220f500450744c5403c601c1d01d4442c10240902c2d804c01402e0070081c81100920242101031200788d004003800d40c100d5100118000090002d00700441ba = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 182474100 1250 182472850 182472859
    0x20312070509040e01060f12050703060c08060910082e090c0f1403030a0804021903030206150d05060c090a08060a051e040c060804110d0f020a090b010c1101030209 72
    0x10440e5103948403006001c903100075a0103200c000c81d60392005007a28041e014004001c1c60000d410f01c50050640c00c1601c03602d0043c01200c680650341e4a07107a040f14001c0000f000014400b5003040350742e0610b40b0a0036000100c2401c01d004042c40c107001c031502e54038584810150b62079014011074400881d03d41e451040300c00b41c2c10401c0004458075004654000c9442001c81301300800380001ba031418898180c850152006c0c024505e02540402c048650140041080342c1c003048800d201111801401d00040c003862282e0020106418015110003101d0224602144210300044045000032070100700d0540000d051051941c0f1404110001002e503030058022004900c252400c0000a4440340c00460040140c2d80303401100300110360704024524402c40c1e010f8424442e0100400c072062150442c0d60f0f1080c0034801c0d900c070000c44000041c4c800d001040080c1c44440000009401707515111500d2002040c684100b00100506813002800e0503154003c0985080880c40400c042e6900a404031540d2440041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 182475350 1250 182474100 182474137
    0x4110307030603030201060b0f070b090a0f0c1a09030d0828140c0405100503040305250302010b100c0311010e060c0d060504060b04091d2410030317070203 68
    0x200010010300c41c0b0f200640044d07080c0300c0001540b80301e040881c4d00491050940398a013104540307031f4000c140809461141d0714814808541c02044510004002452099501ca070030680351000d00302c40440701c1680b22a5400301001429103540e03000810115801c0c07141001e104954072000681c0301041c03030411440300f080010907591687d28046c0e21081c40307081801c00014664a50429240302401a4051150041d068001c0000c0c00c5000f4001385138000c3c4203240184c0303000d69044401d813504e6182c002d03e00e00a548500c0740320070903030217025070b1100100c00e5481865242e0790000007030071100c6c81540a81480b81c0c210034503102c0c513000c0d0462141229180212803c80c10058010b09507035019040b14407007a2318208003c1210300d042e016100840b52a441d015042c5400c14050030000d0512000300480060018608411a0001d01c02d0340d0f85080c0012025201c40159610103c04100061a107440d049112500f48000ba0300030910b00650b44621803000e90710750b28200142d00d1032048411281013a195034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 182476600 1250 182475350 182475361
    0x201030b040f02121003020105040320031603020f04140a0f02070b070f0807020109120f0302090a1806080610060302070c080715092301120908030a020c07080604050a0206030402041103 81
    0xd0700101324400001c440c40619070782d0068404841c844901000380050401c100420201300210001001038050280740701001c041840060320b0a50811055641c110030b0000800035864080720301048154203440078814860125203001e01c50f03100400060070a0355400f4840301e2a00c40b0303410b5400c10743e0b0003c8034685c1c03800d000b20040c040610316400c2200046c549800580a030744103025101c201c40e440500e03c0981034402d58150362086032804140200342c0d091100040e0b070755400c0c0b0040c0040c620748440c0d11444034002ca50b503041d01c41c1030f0401d20b02640712a0a0001080c40740c048e80341190307641e180050f260882490080d8030110aa4440056031042c00c50100b0100d080e001000c162140544400304940c4e0355030340c0040d038800e4100e04030300e0b42c1e40c60324035038081075028554a900710042124000350308a52075480351746640003038500d45501c55002c01c580140b0903040100c08083e003140c400a122034a055542c0c242c1e501c0d90f00d503000b03000e00c10100100c0e08541300d5030403002080980301121603c80c80d04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 182477850 1250 182476600 182476631
    0x1e18080616050a1b080c1608011808040902030408120f0604051003050a02011107080304080a1406040206030a02090d0b09010b04150b040302061c09050f010e16120201030b04 76
    0x6a815240300c403103101100c12070324080c038100c8a14101644404642002d00501d00c003501041d11020388042d24108880e41c0010300070f010f81074040d1010300000c201c080c00c06280e00d0841e0700b0040304041c506441c0840314081005030f01500c00300d500260015035030f903641e40390200380c43c0038041d040030341c060990080c0b0505400e01c0c01c3c0c480c4685401c6d00d040007241d6400181624442d6180300281c40d940001400c0340c05540310b20240d036030662001007102d0382103603101d07a0f42c4d1a6a00507404446140c11200d542000c1002d9981590151446c65000f0011400c0540009842d4031019010b0706045a0000300c3d018192140350711204015002110601145001c14144d4040d01d0f40c2141f0a2207286004104854203114202d11000d550300b0340341242c00c181c20b43d42071160646c404d40100c40c1c41c2c0c1070341005095001d4980200a082849039001e851100003001c0c1c2282580c80314100380c402d42c0c02500c03501c00d03296444c02c6001e040ba92001c400300d06008090005800400788be061444d0041c1c1010718900d541c290 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 182479100 1250 182477850 182477863
    0xa20070b0a052502060d0b030a05101d01020a090b1303080a09090b12060118090606030f050f0705010509100314040309081e0c060702011803030c03030506101e1808 72
    0x3641c8180701d43c10b0f046101404590310148000950010b0103210124120b6916401084101d60180464108000548505281c41c0f80e8006980c00719484d002401e2248080c01128a05401e10000941c149011458058128401c038018441c02d00c001281d040b91842c1c507a98150020f5030000a56503503008001c000400390320540c0a040150342c00d11110034214100f590303040c1c1a100c003180c081c2000340d0900c030075040940d907907504884440ba2600343c004080b4503d031050b680211b00c230340d5449046c81072900d000f5090450390302484245030007a040c20481641c200d001c607840d80a089032404010780c10180c0a81c000d03e81562101e94805105e800c100401d500301000400352a086808c0301c039a144400740d0001c40c03e81c482400b83d500c3d040b54a50034690f09144001d0b03c00144141411608400c0588002640c1c400c140d205400081100c90742d00103058043c49030700e4024400f87d80d0a401000c4403030010702888407130704005e211003c0d20071844460500c03d01144480c032907c0114541403ea951094566034136 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 182480350 1250 182479100 182479117
    0x4030807090605120c160506160314090714061c0614030d0212130b0a08160c0515040c050a080102040e010801050714070203120d05090c060a20070b0a05 67
    0x266002804142c45005109032460450030b80344d044ea0590701c40d14519525000442080780d211200d03c02c0d840040d0080c80404d105a9010b00e8801000303c0c011401816509552610305083c0514001c2c03023020300000c9070b0070065400c1010111011400400402d0307051203111081d8113050101406030b40f4a0403223030418412034502144000d114402c1100305601ca0354144d2803040580d001c0302c4c074503441d06400f00c05030500c080529040c803142a40e0704100e0b4100d40c048609240010040020020f62020500c00c1f1008a482813400200042440c5c1e1340d559078440b10760803420b0b16aa070300c00050070000c204101d1009010301070302d01e0300107540e44c0c02d0b424045c0d0428020402016032044c000b0810400510545106990640d92090000c0740784d030099403d035008600c02d076014090340600400100001d4014070741c2d4a001c51000030149086c50460707080540e40c5414038480d40c41041210380c00d980c03166241e41e00d44003101103140d10b04003001a1030315100c0b455000c80c0d00b856000c10205006070704000a00f0004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 182481600 1250 182480350 182480357
    0x90d12020708010c0f0809030403050106080a1a010f05190512030702030609010b060702190e04030c02030607020d0e01030209010314010816090e100c051606020d06120b1f0b0304030807 81
    0x6031107041d850309903204c50080c6000903154090f050071207441814a650081e81c908181c0f894591030317880d4a800d40780980c002d089242d00c11881c0508002c40d0a85038803540101118104965050001e11480303103002d485818803426808020080440500000200900b03000344a5413001460b440303126140d8002c0ea0050b84280510b00000304050010b0048072140c010040981d460803c165007000031506070f000040c1c0300e10030281c101103840c04a9022040c040c602031740350381d000c4150f01e03c105490460000c02c104215004024208042a0003010340d480d6000242009a00d6900100049000300800c502c0c0c1c0c4800b5542100000c3e03904808280007103504140701c0f03040034960302e598400d4180c031b080f21020000c41c0d2010041c00e459050310b40c0000781d26a100d1078072910f031003c1040300510f40c001d84001568015400150681c3c5401c26100e00e60050003030929003020164251941c1c5094100105810f081480342040810040031106181d40030b00f40000b519500d0f420141002003151404941d1103012 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 182482850 1250 182481600 182481613
    0x303020a083115050304230304180501090b0102030c060106081e010909050705030f030a050325090f090b061606020c06040f03090e01030f060b0301060b04080c1008190b06090d1202 79
    0x3c1d50f10540840748100d400a0b52000218244c0d516031090740500030741801c05000c10310000c40c80d0b000c3c886803059112020700c004100c950520401400b250f0b80420014195130003084440306021002c60f14904696190411035400d030307607204201c2c11185002c0598500940040004902d0000e503501c0000c00c28083c1044845980d141c85c2410391b120044052011aa4420f102c00a14203210b1002564068041885100400354114441503020032684e0a0350115290800500508001d0000345005060101d8184406540701011172100e2050703c50b1096606e002c0180ca0042c000c2c5a01180c0a0030b484008580c403e1900c5e080135260040800c1c822400549821000a20000d07900d036000d060700e80108540450080c01d40d01c0b03000400360080825003554988000084540940c0d01038002007138800050080d125003141044010450003102070248403414041c0300380c40402c90a03100541c10200c800003044000781d00000c02c03034020380c1c145581c81034001504200304a09285140302188203502260030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 182484100 1250 182482850 182482889
    0x3010c09030b010f0b031b0706051e0901050c0403020105130503121308010203061e0f060c01020a0905030607050a050a05040306111b0a050606010c0c18051f0303020a0831 75
    0x10403041c11711480204100a0000c111021510b005a0301180d02101038245095070982e42c490540e101200c100c000c2d420031619030443e01c4405140c0590005148000300181d281c11114411035010741e01029041140202e15540c1281000c0c42840143c203006044980400d200ba45903200c036403080c104502d200d803000c2c800003400c06050003624095070300204140d0641080e2281030340b1902c8400c2d400355200c2140e1040201c65140c100090031070030318140001d80d13154038840700644050b0a59000354020750081c020002226408020b4031003020440c0780466941c8584807040f030390703400350340c1002c1d04040c074000c2001008605c101c001c8c8650052202551003e8600104480e111004084007a0503034202d6400914103600c40c0c5044160180304107000d802c0306031210300110700c1e42c1c6103164605087e0fa888084c40708a90050541001d51002c101c3c0d580005402c40c3d600039142e01c0c0b1980e0091000c20042070340b10181c05240100c441030207546505503648203106484174a0180c00e03100710700d514a08032007a0007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 182485350 1250 182484100 182484119
    0x80a020a08030328020d0603050d17060907050f04150e1507260d050405030403020102160f06080a230a060504110f0901030e0f0607090504050103150b0f03010c09030b01 74
    0x748a08100540000c80d501104c0340156000703040d058100300594204104110100c4502c101800f46000c0c0000300000880d050740985080064445207120684e500304100b00c61740c60070302e150f50125003890601d446032184001541035006540010443c0325151020807145030b44952400300043c0b04071071621441c02110940a01c0d84100000980300100804106d900c850088000c04001c2a0190045103402c1e403105100b41258000d07207040b10341c0d4100007010015581c1c1040030b0620000ca002107a945a45003000c00c041e0708074103102d0b0b04140240d510004908280d107500030501600e03019412218400310a0301204581421184001101e25007003005c222801c00788105034001020840d03903842e001c020503280003642c00a01d810b40c101601ca00800904041c00e008904084d4000c00041040d03042c1103001808500e0140c002da070049180000402c040740380c00806c000383d400c0444000405400e81000704802c09005081c958040d82412150714940c5c5d071000f6410f007204d00a4100001e183d03202e80045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 182486600 1250 182485350 182485357
    0xc0b09010e0415080106091d03040608040b1003140d0909060f030206030405030d06030807060b03011e0506010207030507080d0305160807050f070506070e13060f12080c0106080a020a0803 82
    0x12030004520403031a03021402c05501010640d54000e0b29281c20558615905003910440d4000d0201c0365229004030040207904840d404071f118a440c007840c201401c10000078500e040080020b01a5954100407415080c0b86451580c003954000009900141ca081081c940d5208182009000a400c011002030304100c1c0e4071848080e101c1e814100d1004510b15000c00c58240c10282054a843c0820330031900c2c0320105209a00003540300f040c0e420b494081c1410301500725110300300d0442c066410198040e40b1000c0c00800c20f01400800000040c441e20b407500100e20307000181d00001c015200310600811983d10000d0007041d0700310175079418010760b6a1407900e41c440301a10f003901d0002c200c42c0004112075030f01035005491165603d812031400c0155039103410b4607282080da0707074101003444003c0000301402c051041044035502a6000d01c16189424102407110741d0303601c510041c04580b120741c1c00800c1419070444a100030f840000340086a00c41421a844090444003244240c884100c0060f102c0404001e8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 182487850 1250 182486600 182486617
    0x612060912070c36021303021e0306070210060807051005090112060b0a0305060108100e0a0207080d0501170f0304051003110313021201270302031b0a0c0b 68
    0x203010400c4003111280419084280304031041d0300b1410f000708850070030180d4034400e00c0d001c1c029460400c81c0a260700d03c0003004110700782e108600401c9180c0020751a210407404496055841c0c2d060310484c0ca40069000403030540d42c60307060055000b070101065002403900c4890f408220b04200c141e81e6445c2c01503883d481d0b40314854000d8445801318142c9806180070b440d122006042031503076200064000c4d41240d00b0354100445085011034004d040951600c0780a903c4038082c20880c0c0345043c081220843c4041c0351007001042101d43c0e00082c0462104e030103442060764041072094aa19069408101501c401d000340c59103a801e01c0480c4548140000d808200036060380c1c040c602e014103101c24065070b040000b6407641416218200e0fa40e68000030b5000f14800e00480c005803200c1ca61038410040344241e540c803688156810842610031440d140024801001d1440c0303440307040c81c04242390a9003140510903030807456980007031600703500680c0860a02040c521130600d98a1740b035121008560503000307201c0c6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 182489100 1250 182487850 182487853
    0x50405070516080706150602060907060504060c14010209061605060c0f0406080408070c0305030a030f02210402130612030e100e091b130302030f070b030403140d050703020306120609 80
    0x2410740100383c840c0010400f031030160f0004a6840d03030016601310900302d191f00c80801644a20104503890340140103a0018000c28a072803881e0501d0844010300e01181220701030a213100382005c022406e802541110050180601602d4072418200c08070031404407a04015203c07409010000750364003031000115484204280711300c600707003401c01e8001c841140c0c0003841200d04110410800d0045905190300748000d5200d1001941d88007900c03840102078481c40c1944400c40e030300511408d01000c4811b06402c42a002c0b800c4040a40c0c0c0d84d5000061403030690349440343c2a00d151030401704409080e18104038940e8040e855199201d80e48405000c5858840d0302c0c41400100b0282052035103241401c415600050400074107503210082e0808030005600000304a0035491400d1400c000b1428140818101d441c0c0e10001b07494140c0c942485901d103440004d2000b0b003044a202c07004505c100e01172068500d10b0712011410032091034004000340082d0320517a082441600381e04c918901c0702c827002030b00e103102c0c0c101d100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 182490350 1250 182489100 182489137
    0xe1203071a0f0c0d061d0103020f010e010f0f02031e04030308150604030210200609100905060f091504030e0909030c0706050a1b15050f0c040308070303180c0504050705 74
    0x450f40744032078119074a44150f854540d01c00185903030501c040d0701100b080840702030450754510310405c9030345207401a2990520800d01c030400c1c0c00c0e80e040301825014241c0c41c10a844c0080c810107049046116003031a00c14801c04000c10307100788402c0c8901078000d4900c41e80312200f09845040b044050f0b01602c0c640c0691002e0200000c0c0014208000040d580442c641010b2951103000d4506100d02d48801c2558a041c0d4000810042d10903000c112449103511907000030032103940241c881581300c4d0700061148030241644030101d07030480b0003082001d50451800d05119401d0400e45001019407951103034140c800c1480b06e01241d54020080121506200f00c0380081c1000c03440d209040c1d4554001400d040e003406000c107286d00100042c10013084c2031903c19076000c950421400d038184111071010b0440c02c3e100610b0b00030007566095080440301525001001c103521015145811030160200040f0101d814903d030706250100b2220b01c03024000c0e600d04a8060109075075802048419000c0d0b4020510301e829800c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 182491600 1250 182490350 182490361
    0x3010e060a0305030a0536010813030206060d08090a080c150a020a0f0615030501050603010e0705010f0e0a0902122502210409090f0501200d0203070e1203071a0f 71
    0x9200420b40c40d00e202c1607020491001c20080c103c00c2c2147c00d00d4146e56000040c4080544d0b0340032714070680c05214214032030450222030710002d5031058010622030181805003003d40c103200300d050646000740c0c3c005100c41c044d25100c0300030a071100844a003103802003c02500c00c0307030100807220a81da42c1038891350003410309a980e0b841d120200309600000361003142c1d03150303070a6014088864034400690b00420001c2124144001450700311020b0384035040c1960030140060000d60b030702820300c82c0c80808606e050070b80901c10200154001e4416800329203142d1000540c800401c112030104c2c0d101e00070482d4550f8084072408030304101c00c1c0c0070600000040e04240050004619150b8006030341c80c069645250074542c440100008070740d0005025203550407250b07513040400c0800d004803804001c40c12601c401e9515041105900341c0280d068a909064020002030f119512031408a19a00e0004203990510018083c038181c50360701a0000ba81d001c480c4a0030664000c8526804a0144942591240055596 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 182492850 1250 182491600 182491607
    0x141b1005030a0e07090e210f0304080d05010e0405150403080c0d0905030708033403020306030c150c0d0516030c0203100c0509040e1b1c0c090203010e060a0305030a 72
    0x4007007104443d62803003001c1c0341040c100141030141051071340000c0c151442c030105030318000500f2492004156925050f90380488400d041e2003050800c80041a01ca450303e1404030410700800000c0040301e4038000c00003905480140d207041c0503501403c19a1034000369800100c2c80303001c0403240540410000d078085900c6181c5c03240140f482d0740314035400040c101c40c203568071801c0d54003c40c1d007520b0741d09000c420b1024038240286500a844101501c0400c000104410404901039807812002459800300004505482c10f00800035800c074001d00e41ca149540b80e0380301c0301140d00450030b1a0080d2048140340701080c0d011f8411075014125400700710150030303a1541c0840d40051045d9040740c050194584901c003e80c0c0074026240052420380b03c0300d8449107039000340b20031034654a02c10f10b05940560b0103410140604507004084c210301340d4600c5442c15036400520500c820200d0010700c4408002000142c45c1414bd0185d07041c1e440320303018428292201c104100c9088140d000142c5240c01c02c11070090090302 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 182494100 1250 182492850 182492857
    0x30414060702091f080703140601050604121101030e01020c010c1e0207050f030111030f0103060c03091e0503041d040614040c09021c0c030c120507090306020d02090d141b1005 77
    0x10b081c6030011255849681184c06c00f5044d500031940b0341d51210f030b030810207842400314030b0241105a50180c00d051138031001c018211868a00a0a80101003103031501c9a403181d08141a40300b4980c00075541c0301411008140203051201075040000c00281a082840300e604500d058840c92950042200703500b00400c105a8400b1544503a0340741d91b0b1020014a850814030145205404c0550001015859400e05106641c0741030019010549042d1050000030720510030001e1083c0d030540458200c0300e06241145c40c51007203030402c44940603601c0e540100d00c0301004010b44103074414072040c407582d0b036081f003044c0a2204c103540040c58a069180b052005403080c9c0e0250903603201c10240b10100183c01c2480c041251002e0b9000000692183c8502034201c0d00b1064024404403443c904205524201038014801e0380d15000c000d00264000803001d04c80604c60b01901d90442c03005000501021b03d928152140141d0340303990170300b203010381e42d0b1303000184541b18040c440e40c2901030150070520134500d00031140381d803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 182495350 1250 182494100 182494141
    0xf0e07020607110a021e1f020d0507030504140312030c1b01060605040302091003060501060c0209150306010b0c210c060c1603110f0a0305030a2004050607020d1403041406070209 78
    0x102c0f200303580f601c0c0e540c1000c0080340003106240c5014102c1c951f00c000307080c009003005800603c0410080b400020303511504503011241d1105200182c4900341c80085c4c18002c00402041580310040184070b00007010200900400c120340d018100f0607151900e09900382c4a49100d220040392b418081040907040c8542e100b03511000410035000c041d03071240d44901c12200280c0080c400160302098503011800c2a520581e003001c0c011600041900034a000079603684014014081d200c0c2011510140d001010400c149450540c1440301e80740070701d029815035041d00980385d105101c2c0b040d1004184025001c8081716048407a400d2213030b01400240d10181d400030030300840d00c01244108106d84030409003c1c89240502d5211765503080c2d981c10b050f502d2205880910301c40c40760448611001058001c03080b0112800c4420503500140c8488035400041c80701c0d80c2c620070240098800b0115524109004001407041e51450800112580303001800d0013594001e100009400412910126082003802c0c2c1920b001003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 182496600 1250 182495350 182495389
    0xb04170111120c300a02120402150c0714010207240c0c051011070f060903060e010b030a0501020702090f0f19060510030e010506032b090f0e07020607110a02 69
    0x11402c203000071006050f10841c000042c0c103084c000080019103000607030082c40d224025420298225042070030035a002d003000f441180700d40503025030000c0c801c5c1a40d454543c50810344511680e140328a111030000f1209060043c022b940c0040303101e0300e508803020f8510302210703410f202840c8055400d0b0b5100243d00b0f01034440690643c40041c095480500342191940541c0d40c0300511052326020320710340b4415400030002e00c50401421b2088030352000c00030040f81c3d082807010038000e0118000c54014806200825014054148807900f809015002008541c2c404e58081441e59505601094460401e903003940f200240c0034003042c8210582c40f420940403c50301400520b40d41e07107400007441c1780c10010710340d00466203076401210f031a40300303204040d40103405402500308105001c400b440d0b014110190303000c004201088000c03c071442440944050007101908500c1d00381c4442140c198990102d881d8070046c030802c0002031071035100c0d80140c554501d8090050900882c0342d820040c0009480700c1e0b103c2039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 182497850 1250 182496600 182496607
    0x1116021804210309120302090f03010501050f0d0c09050c0705070b030c27030624030a05030a050a020705090f0f0a0903390b060a0e040507060c03020f070b04170111120c 74
    0x704a605d50720100a605030b8800580d1052401c00b44180300101e01c1c101d511030391411004105944910080340f42681c811212440403600d58030300081041290f4200f01d440030b00c1c090400000e124420000c0140ca8010703410bc0f038242e651440b40d4801e6109c1100c401d90341d00d20a20410010501c16071032404400404a030040d500c0c9061401310340341ca4012102e2080740c81c11404069542e5007103039000080c1d5002034000d406065140d072211566846194140410010002502e0101600c00d0001c0e402408006080c085a41080d1625550143c004d9440980751120240884c913030420621171900b400b503058885446645050035030302c02400c1100c10882c040c00c012003c10b201c09114600800585115840c0c410b03480c1000b106021040ca00c1e60000d156440c50042880003103031000440c501162540e21305038100300707040c0c0307022402d00d0740144107902584907211021413219a150003800550b00040d04142c1002c4824410509075040d8119000602d03078104104e801021001e02c0c0190b100a06c41c148515 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 182499100 1250 182497850 182497853
    0xc16030f241103061002011505090c0435010902030d11070905010b130510120c03060305060f010305010b0a05210717010c020105070503090c0f01031116021804210309 73
    0x60b40d181100a0070440303400000c200083c40d0400c009805008240b008010404808680c142d00b66064003909108050b00c0d4001100c4014150803200070701004440000f00445003a00701414034004034400e6030161400c111031000c1c01e0144a008075040e0010000c00820b003203184c082d6981350b01c1002c00d8400b03000e6040b01080d0980540103650080c0005800c40d90307290700003003001d01110360700d8004520840b24034502c4032129500c0302145110800d0352a0010308030903510029401050954001072850041604200d845614448281d0407130340668020322441c1c4c00b070410000710398450b0180c268450a80031940070180034138114003079540003000440e02004c0e1101c4051084a11541880515a440d05011112141d085c0a103d4102019040c0642903017000701406454100000d1114003070b150301c854a4255078425045061210403da00075a07650250782032800c00c202e80d01c48240d008094104480380303010440308155101755000400e05c81d0071490205c00041808905104008064603000c6450 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 182500350 1250 182499100 182499173
    0x5043c0c02070e01080102040b0307050c010b130b0306010b0307120e0a0f12140a0504060c0303110c01060504050f13020d0305090a060f030e01140703020d0219050c16030f 75
    0x41035186030340003800c8091405901000044050300103079107590050101f0001001490709803600803440341025a00e505104031903d0042c40e241690369485003030f029464a06004c90b5010003943e00068050700d41c04e0381c9a030603026840c0720680d5050b000480c03100300d2040e00c08180d4040708040c003262003620541e5210351036900c151181a002030720301c9103000c140e46185a0300100980e0390b180700e0481c1141032950704a80a0006e008910600082c401c46000340340030140320781d100048181d0542e802c00e8444800380002c60003401e560040354080d91500020403003402c0070700b42d0075100703003103161140c03003412010707030074001c541060680486c1031000a121101265440390005005006107030b42c0e25001c095054402000e40e849025441500d07454107400851911101c01601d520400c00c0c100542c1da02c80341e204040007842010420781140c50169242031102e54020000c1400d2031404040347c81c074a100342c006540b20308031844002c0108101c0001c020019485052800c501a0b08641e10a807010307a000740315 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 182501600 1250 182500350 182500361
    0x10e0102040306050f13020603360d14070209161403040308060f181506040f09020306040606080903070201030c0302070819020f0703031d1f020a020a05043c 69
    0x840f45a511602000328a000d40304420354402c81014500d4180022500401d98502c030150104103202c11100f6200e4040313001d1104c030a9058104829201c0590100c09010b80f90190b05c40d0032000941d0700481c020462a0080582d06955001004411161243c944440944440c1b4809400b4040b041d0005408180d00f1409903110354040d8850304000d2415a0400003018408489948140e1102c034006010400344810076600021200820b0344403062140042c00301d0180c0d5020200410b02031078040307800c440c190051805444291024003080340c440c0c078280d407600012510340c08c540c0c0c41400b00002543c440e0304200700006a5003001840c00c646500c1f14540d60b031141010303440e421066050900c80b43d07810414901c0340c3c410700c4c005e01441c1c0d00719500104008141c0b07800e2440c1c001003045030f0340f241c0d41e5461100f90018402800028903a0b21381800307034482c604603006a101d8402c002000400341003900030502d090000503c03e401103003001c0580041c3c02d40540f903102ca0b44400d0307517411440c0145071185 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 182502850 1250 182501600 182501603
    0x40c0c020a060909050a0908070327060917030f07030c0204090212010c0e060903030403240207030206071e0f03020a030e0111075001020d0e1005060f0111010e01020403 74
    0x74445880c0c10015001e040c0d41015011b407480030300d0b180300640422070725010b503121140d140c600604283d50380d508844500c1280403485500307100c64000040c035640c1280481088441441e07070034089118012070283c4900680a09001202c803c0101d403001a1141d5040c04c8424401000040d40d46555004070340050040385d403415903699550f5540d0302d1260881d00786c078402070080b41c01d01d10303088242010030384034001ca1000030040102c4075000402c210151486420302d41450310119103452072803c00075070703604069030710b04045030b02449440b00b40d001506401c000340c1e407181c42d2440241c0c2c034090210002c2d40410304500c101950b0b80301d0701c80b56034404e001d03420100f50403445040c0c440722a418620504171540140702034001d420100c0c1c2c910550989809240002c1d0b001c00e0b41a9101d070483c0e4454030260754032441005506c0041d031641c210400b03a01812003106a00100c5504070740c041c425100710344013510305030303444030550071011150761290030441c01c00c103050000460344104a40030a0b0a81e00140c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 182504100 1250 182502850 182502857
    0x160501020c0a060209011b021c03051b070302010807020303090706050313020a03060e070905040c0e04020d0b070f0e010c051c1404030602070611030f0f070302070b070e040f1505040c0c020a06 84
    0x4a02d45150f13403100702c7c0154081c200c0200d509120450b40064201504002c90040c101c0a40f0500c4007070500413016201d10300c9900c0c3c2c04075036030401540c04039228106c0340000c07030204104030b0210b0341080c0300005991044c01c0050050105508145081d100c0e0b8000401c40c080c50301040848400686030349030341d480110300c03403007010444802030740205007040700d95000396181341d14000402000c18459440001224003207080c1c84400d44460005c509000b801c800003912039540c2c0011300c0100c65000e500798140100603034a100c05400d05000446060002d548050402e0384585d110b060b9011410311030032148040381c240100390042e0488410b005401c25402680c2c2140d01207410350071b120b90b43c010341c550301030700403285490f40c58402603580c150f0700701820100c8002110b00010b0500340c000d504aa5026410464000c075070f2600600090a01c1c07002803260f8041e41c140800c064101407a401030009107010a480303d1a01d80c201010320009010705440c00c410042c9004811025840b002d641070b003d0082c564 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 182505350 1250 182504100 182504107
    0x910051321020f0102070233030906041104020901080a0b011e03020903010c0c0c1e030206070b150a05150309010603060618150f0306090501090c0b0a1101050c160501020c0a0602 78
    0x1c000c0d05014140d02040210390040003240c0c0180e640c604240d0345440b1001c98030703244201c2441f03070000d1215107040c000b00c0703403900000b405141c10000407030070b100f203204452004030404810107202c20303405900442c601082c510b6010401101441c5c0060300d01c100706251400102c1035200c0081c110808602f40c84010030340c0021200036900f000c2c06a80d5003580b190600c107220000503a260388203208141b18000d000c1080e0580c181c0b1180700301070120001d540040003162110082e082c5480f924105032100c03402007141d03600e007a480341072050b0650704940e4014010750410390b644001d11860340c00100405c8040d560b50b040400014400e115100c00350441c18281400c0c85a4220698102c0d00127031070b042401003880c10108201c000314840542a01d03440f030808600e0143c82d203411409014418002080031038185c901103801150103000d0110420540d82c0d0072200400d01a02da402c075282610464208001003158040e958107408403228103038843e8000500e0301030660310703940c2403000c0d00100b21403054000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 182506600 1250 182505350 182505413
    0x61e0c09091503020619110a110439021015080d03053112080a0b06090d06020c0a052d0d0c1203090206030103080409060e09100513 58
    0x9208480d04070080181c0982c00e5419900040c1090040c4100300e400011030040211000744540031011821085801711050580d0f540f82001021a0004000d4012450100d00010000d440c0c540707078492044141409464842c07405c1040146a090030095065200c2d2003807081107a0b002d40b0484140c60101600104000d0521340c0039410b00214500980c1054108028072213200a0340f42009601d100813002090001028201d19005a0030f000303000c0c2c410600034500e42401c9030072070b02440c400c2e020103170104070004030b80701006603d00420008981001c000b0501800050302c40e8001c2c1444160b0b03208550103104160f4510345011501d203559090f03905040040d000410101c41c0141c540c0080704040c0040342d0742d840f00248250f49141d0007800800024001e0a507490081e0301c1035204540140851b5501d60b1242841c10340740d8410f11858406900d040c0300000c8584420701224040c65001000d444448100800e20015200107002001005600023100d40083e9040407031803a43c1c0007080c881013108045 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 182507850 1250 182506600 182506619
    0xf12031305030a03050a0318050a0b060405011a030c1b06011d061c030e0103060b04120507080a050303011e0b040e0402030c01080112080d020c071206051f03061e0c09 73
    0x90707440709010f6030041082e840004d0b00802628021000e0740b800003040c50007014081022250580060034034003c0340d040c14240f2140b4001c4a210711401e03281440b842c0d989410f084c83d11140c415001034000e1b03091021a4002d20404010806030701c00c04005515a030b240a411400c001c003e0740700b40111910689080c1c1c2d16003520780356603444101110342c04504841110903400308d8411075002000c115109541d005613a020b0761101c0c000d007103201421911551106500e0340e0041c142b00d0252024411800e000800590009404801c0c950003000703541564079046286030805800303649051a21503c140100f03c0158120103840100116005460301d0b040a005040c10719000d05802170401a910300140100c8020074407081e070880c0d001c1c000c60343d603084c0c01d00110000d0150070311012060007030b501c002940c0c1d04031280030f42c0d58502510702040b50392034001e41281e800d5420a0034400603e00d481e410000b04500c2d0b4402018103208840c80340000944402800803600207042020220f03d00c20030500c1080350 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 182509100 1250 182507850 182507887
    0x15030c0f0d061104050402120f0a02070f0602030402040906020406031d0703230109020402070605060910080303130c0f1401020f070e18010902040c0503150604050f1c0519060e0105060d03030b0f1203 87
    0x702b910452405100d511120950203150170702628140d0004042021504da035404040403075040f00b41152180e0700c4410050180010a01c00301c0b0064000390034030720203400032940d182100d80c48000d00d241c0c1600045c25810b4000c030500d003d501950b0341c07180180076843e0350004000207481214000f82a1a0920400c8030300039000e0301f0b030b809001103808184208000001240d4009144054603020050189840100c03480c441d00490780c1c007407a103400020b4085006086d0885500260286c1d10314a000d1554245d998480f40306006000c04a03101080120191400c0514070b11000700c0046601c01c05900820141d60f800c0e0b02c0c2a001603800000c11082d035070015040791040f00700700c40451a0030710300720000d0070208c0d811100d10311070202031909696101000c1200303110341740d01c001500c030403031110009000c0c503548900c415105a2b00340145940324039010700c9040d00c1500d0040c06245064181d4074102d0003082417000b50768100c00200d02d18140e940c0c48809842c042450100150b0766031048080d048400007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 182510350 1250 182509100 182509111
    0x50403021c08071e090603050604180b0402030105220f2109140d0c05060306030319080702011b080a050a0209130902030c0f010801090b030a080315030c0f0d061104050402120f 77
    0x140401d5130400c09942c007021030811104a0324010680f502e4120010b070092585510203c030104d503140c40c0c0c0c41084a001f9949103e00d00031070081105503155200c00c24030225411865580003682490280040d040441c41e400d17407030256500c10340c0400800c4607003490078050b20800001c03900c40a8100280b04005441c0c3d0114a030694040252840650300c00c0d00100850250b40c0c451400400090882c1c0c8082054070400803003500c12001e041c214280142048000791000c0703006500303280004c07a8074550510b417010120910b81d102602552405030307100c01020f016224075005070702040b88050a507902009120034510342000010082ca0901c105482d11900c038024a02800c80b19001943c0b9030703008800b060440c2d44104c0042034000540740000c0c00d00c115200028003140020003448440524840341412851042d170440d98036540d0b00d13041124081d1540c0203590b1000200301d02500050440d001614114410a0041c0c1001c2d15000002c00383c0c0c010b6008030424410035030410403030031062440d85400c130 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 182511600 1250 182510350 182510387
    0x1a0106021b0d060908190801080c0907080403030f05070f120e030306010c08040803030406140906190e070f030b04230a0b060d0f061b080c07020103050403021c0807 72
    0x110544285040d80700351070780c1410711914405000c00c0501400d07810240c00c0a41c8032200c541d403802201d030030f25451400900124006220f0200200d0b180c500054460700d4450010300081c1d482d075500c3c60445408200620031801c140d00c03524001140c00d5203001e4140110300715165100070b2991128010140c900132400c00e08200d0620f4007000c00341c100031007280e401100c28070b00103c84030003070b050a52051003154020105071000101700030038002d141c0d100075001200742c1c800c0d034059122508240e0740c80506503014002281c2600080403640d41c40c0d070007026880c2261003034829403a503030340e00300301500525030041d2120b060310030400c4204810340751200350090781d984c40042403500ca40300c915910444035000078525030100740800d00d50342e03076201e05000e8a0b038842c0384061076003540e24211000d003c0941e080c0c42a40160080c0d810124080c1790324620901056080034200000f940044000d440050001d071300354001c1143d201c00c0b4000403a04180a242d480c1c07507442c028103090000410700c0000c0d0450320400c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 182512850 1250 182511600 182511613
    0x601030305091201060f0509070c050708071401030c1d0a0911030f100b030708040c0e090d08070203070206030a05040f080c0106050a15020d1d061c051003050d110102090d1a010602 79
    0x6480e16041507a05491b41a0762381c1c2c100f5981c044099981072000071020f09a40714030000060111030019200c81560141e02101000015460054099811410f80c10021902c5c059480910300d08082c100450300000800c0145401d5a41c0c84060880b14910014203600500004102400c0060545903801c880b032001c4800c1c16500d400801c4040c3c1c0409002c04041040e050080384c103206030f044000d0050030800400e54094142103a50a507510000801040031525100c0018803050020058a41d1242c01070141861555901c0401c400ac1400910442d10000c43c44c2c0074030302042c0000082d0003000c01400000820608040820070f01c0e14950788001c404802107464811516408600000390007401d082000e0300031905c01e5a07a212504011240341c0241010445000b005401442480c1c001c0d00e201c42003105850b150042a25010140400351466208182d0502c4c03d600c1403a00300e18119080f40014141220300002a900c100d203c20140d40c0741035042d4a100c2809105642c850040510340020042c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 182514100 1250 182512850 182512859
    0xb18130609020706050406050f191e0e030903010e0316111c0b0117030412020907020a05030a050d060b0c070b0703020a0c0f030b060d12110705060c011d030901020c040c03020c060103030509120106 86
    0x3040c88404032b182031110345500b07000040303001d00d5168604421103020103001c2c40310800181541d03a04900910f034407075801c2c05000f1004a2000c4111100c100d50441004c515910703030f444034410700324909903a580008070300b140500140c0485c2000c03070003144581c4180205514091448007042c5210340c4025003034004210030030003440c00c54010600d080d415528200030390344940041c1d0520191000290060200040d42881603500c80014940d905001c48104801c5031904440c040e607024040304a0082d5201403800d00c003041202018281e024824070403200f400046075a20351040082341d1000c40740c010340c007106008020a45684551200d000e8900c0401100390f0780b01d500450040340694400e000d0035014a2400c0001405a03030b010341009010715079911000071689000713194034012a10000b16101103c8078040000c4215160150160300500307100d8a03070400c100081078a1126207091641c01c0000000c240f0091003120300850083e142c00341c41d10303c0321042c080070381c0d0440081c00300e40c2d00d0581c0901 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 182515350 1250 182514100 182514121
    0x3030f02150a0b040f0e1c08040f17040f0803070b0f04230a020301050f0103020301051320060c100c0e010504051309110d06090c0b18130609020706050406050f 70
    0x242d1100b040e02000c50b41c0307140300c40850014000084125034050900800078011640014541c40720706580403405006903081c44121010f803c1a45e00070a62039103498501c000c1044101b260001000c0d1105282c40c1996400c205002001c0903070210360349802c00702c1c045040c0320240808070340c411155200913a1074a03117a075070410102941e2080d254150301140030356070050405c00500c070f074035580580200211b0420029001c0c040c003091004a20075820540060b14100c0e018102d90105a804a03206043c0320b4041401582e041c403840d40c0d150054418400d100c0d1110040140201c512401080024034094101005002c0114040303407505000c0100410400b83c1c0b1000300000004000142c0060f11070040d00d04a14040c80701f850f03041c1e101c06008070307903414000250f102c2203010f4880c9294066032941d60008071003030700640c1c183c0000301c40b1101402c4580d003400070805c0505d03175441c2e800040075901c8050b85000c03608080d2003940c2d580e5aa10800081014512a46401114500040d9a01d08d060048507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 182516600 1250 182515350 182515393
    0x60f050316110703060516091505090d080f07110a060f030510120507060f02010c091202030c27010504060b040b0a0c02090f041e02151309050c0403030f02 68
    0xa54144129680100580c4200d0440d10b4034422a800c0c1c912065490400130302419003a280c08541411000c4044501c0d40038595034000c441100b02c0c03409006141c00c0003070b03c054000f4100190060700c681c5503040080c0d41e103402041c041c03101c1040c0c0d645400c11810074003052050001c50301e001d4a131841d000c5c002141c124840b28501041e51502207440c3d0354646d09055014600d9000d00b00701c00e0ba1002c40d10030040d021a8a4040c1c500315510040702074442d05049007a40d10741d188040100b0301e090403c1c8050555410030080c114005800c648184a290010600584816408104c40103034049281c01c102c500d64502401404125004d105407030400c01140340038403413403080e810060000901100e1650255414a50550f00145240c207945084860042c0c929011142102c0002c12a09101c2030f405040c0240e40c3ea080d0060040c2d0404403d40711901016404880340300e1402c8152030300000d202d1414011188612041c101d925201c3c1d10354079010305042441c40141c010764100f002a100c0382d098070b0508 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 182517850 1250 182516600 182516611
    0x1505040203031b251802160f03020f0a08040f080f06010e1306090302010f0b061801030c1119020f010503070509040903050403060f200708030a091a090601050a060f0503 74
    0x39105058182d81806141c6035030142c0720721860500615841d83d401000c8804e030100c034101404031420580100030340003280310307003214804210a542c0852000c1070303d8004088040307201e801211200300e0354608040ca000b4103c0011254100b00107028010f203540c0030490310080c0030b407000800c3e18002f900041a15241c05000c0c0d80c0c1841e02c500001542440c0c0050f501e40540c4d00407400b041009110b05009002e0001a41d108501d5400e12517002440e05101003100c0710b00918044041e41d05817003000440c041c0a511810b5800c10640c440f102d80b04490a10806030746600841d0032078419031251040c4207450300c151100307505128081c01001080b030b8001c82212164003040f81d00103a00181880c041c0c80c3c50190b504050500303458003136001e6462020344c0c400040c0016010ba03011012011040b4108144190310f4000c0406600303002051030742c0c6042d000296582e1041c40b0380c0d801e100f1241401e00012508a80c00d9060380d001c4030041000c0c1c20702c0036104000c2d201503e0210303800c0050310006440303407002800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 182519100 1250 182517850 182517877
    0x5131d07141309172104050307140102040f090617060408030a09150f021305030d020304090504060905030703020d0e09100501080405010e100e1b01080c070503120f04150504020303 79
    0x8800b498203aa40001c1d03050754001088a1807250300c0d40365481c5500000f00006400903c02c1c00c04001a94110000f8441e81c4d201c0000c51074403904d03540d694490040019000d19948d024000445c080440e8010940034155841002501c685844620002107602c40018038690b045142400302044403041100d030700140c40000420004524030381242080d892100c4403000c9d600d00f0401034002c2030150001c02d00c04044400300c804041d140c404052711101001c1910000d607004010820448915401c00395009005040001e10125590cc07194155445110102e0040e00802c540c050081d4110426525080c002d880c2e080072890854803651100c1c84500607035040c07200c00c8001a0800509403c40f00b080c400440a0301c44104000c8400c0c030250840a400843d1401409841d41d003000d020070107841804016500c40b0700715154842284c21561000005440303d010810505584200400d0342e180160f4000204005134502400c001c2841c58240c000d07030b4025800c000134000980d40001c180d405802c204c96 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 182520350 1250 182519100 182519119
    0x3030903022715101e031d030a090618080309041802101806050c03090909070f0602031201080c090402100306171518060c07060605131d0714 62
    0x100d150000206201099028000c2d500401101405035009445824002d6844100f150811101603c01c44d4543d0358104031030341100c58003101c0f18801d422500c1c4a603c0006281d036001c048458440c00e69129541031404159007082c02c101d0303150300059003101c50b1f52042e140b0101d1400c10070b209881f4400da0403040d21803601c40070b0106840c40c000d50000c0e40154000c2100401021140020b0304498400003501ba00c80321281c030000e0b4090042040300d50482d6801c000e1840c2503080c1c81001103488020380f1400482c41454004100d0410005102d030161046800468944000c061180c0036424160402d6100d41c0100016819070380b500000d09400c240c1c110307020f511150501d0303811002000070b82e01c0319404003000104540c2c0e004001c18076803c0f00c003010aa00348507503101400d803469031070311010400042d80040d0003e0038001084002d000c000b40318400104007030b69541e00250f83c026003082c01c90034040c0e8402d44028641d41217800c5460210a200203402c40d81c0c5040140400b4030385e1101620b00441030b00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 182521600 1250 182520350 182520379
    0x30b120708063301050405090f07030c050a081b041214060a1107020f0103020903071d09030309070b03060d0606080d0207090b0d0204050606090307080d020105360709050705180603010303090302 85
    0xd100307680203064080e00c0e0350301e20300c5c0c050b6011050744025032b56800420319104400000a120704112030450302c02c0c1d2607000348d589501061620954255950001c8602c1c1480302140d6007500354600c079501405500e2111241c00004805410700002500c112506480c0020340d00c0144140010f494090703804030b680b00c20340b480c0440107070042e100f22040380742c3c54003030a000030403590801d480d400660b0030072100d0300c0e49503501c480b0314980ea44015180414258010181049051030a000540d031103000038014807032006071030740c4401c1923078401d410060b0380b03400c50300c40088400d904200c01c60007403840e004144218001100444c0300046066806070140d9126000105142c413040d003210a41c04000c1c046500c2c21750f4450f0000e840340c41011203207005500701781c00319014410704112911044100b0f80f04102c1000c0c40308110a0a59066110f0049800381081c0000c80c0c016502c81d861103004140c54250307a5803451a1913080c020b03031f01100903120340e40901c014004030707600c0040d140589a06441041d42856039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 182522850 1250 182521600 182521607
    0x5010b010f0c0b06041d0a0317150909010f020a08010602060f012304090c120c08011514010c0209090619021206040914060c1305090f0a0b01030b120708063301 70
    0x105c200086d44a25165900d541441d002551305a883d001341e0741d0300320392140f04840700c50526040d81c0c1e140c0c1452030340ba117021300c52078404506030304801d5120000621001d80807400c020790700f141c805000403940c07035401040b00b2a0140092039015900807074903c869030501d0481591604540302caa08003114100c0440116201d6500c031466280e0402420390701c8a55400800070904104c071021915028138040001d440c01c0140500c0d084111169414444a07003855550019010344100641c1080041d064001c0543c9074801094050761044010301500c0c81e064924042441d00e860004200510408c03a4011190b018248a40c000600f20750115200449040480c12202080c0d902101070043c5003d2100a00740b10740180301380e030414129850314a940b5810080342032000c66804511950410010f203440325a54461a01c0f003205040010302c40020b5404105900c4078400c1030300d50760380100e8040c8900f460421401d40e0040030b9806240d03100a00c544030311000b026074034409807000e00c0609401001e030b01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 182524100 1250 182522850 182522861
    0xe0d110f01050114030c011407030e0d060e011406010207050d02060f0c030c0a1b0302060a0c0204020f0406050310051c0b040501021605010c230f03091903080405010b010f0c0b0604 79
    0x3161000340200d584480034036200340500c0c40c3c007520a110300c4803110120f501807042c00020184030b07524075003030807825103003540d1403082c100318a0f41c824405c000410000e0040c1c81050424101716000003030161440b01025803810025000e03078190350111208000a964911400c404154156100d41d01c07034512900b102028000d182d044181400085469078007404001141c1052900919048014090310b00702c045010050b0b00001e50410030821008421a0003941c090490341d2015000628080d01d0003010718154003d50000000540c0010600541d1406018200090b0404444600c11801c602c0320f44180d0140405000340f81c220040700141c14810300398141ea203c03040034642c00c89065003614010b4001c104041c5443d02081c0e0310480c201a542000b40003100007107a0300c0c6110324256051030200704540004110384513602c1071200a45c20b070501980d000512500c01d80342d052403410180707089030950303607907040490400c21907582501d0050f81c040c5028901c1600003040720800e88a640c0444c02600 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 182525350 1250 182524100 182524123
    0x703051c05091609051b0a11070f06030b030c0307051504030b04140d0216061d0d08091c03020d0503150306010b0d150515030606040330030e0d11 64
    0x1d10349010401c003010040b80c903c602000a042050520303454007903840880d00e081d28548041019610581c5042c00c1010040402c0c40c3c035400e28840b90040050301c1842d004030350700802007a0305440c900f0886683c043c010358a00d2481240074160998a40300825601d0595105442c0304107000300c1c8007649402c0b610207c40246030001441c140e40e00d41030600369140810040c0036030701031040007059001141b0120b41007450004841120800b9841d243c01140d0245103c00d4106041100c081c080e000f603940c1070b0710750000c0e070710a200b140e440b08114003c200b41e84c189510b200307801d103950f820700f5130020f64003090300e8440010900b00240c1325120320725411000c02d04985041c0e0107102d400c00100d03007410001d000c0c0c0801c455000c4240003195003001300030282c046501ca0340c0e070840080804003070204101c101450344044007801490030140ea81e202e103500082d01814501e07415440840b104600d07900f032a070110f2107c0940c1014010a1401515a035a8102000c003210420081d013074400018a800c1c0000503011 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 182526600 1250 182525350 182525407
    0x30702010e120a050604140307031e17160f020304061202031008060403021c030c021507050c0a0c15090501050306040c0201060b1209010c0c0203060103030806013005100b070305 78
    0x2031603d450320664458058a0690b850220b00410321000e0700000304035142181e140c0d64070240380d954081c1d4000541c20b003d0100c804c0c0050101e8200c0c0001c01c0310344032031040c0c6115541032001000b1180160500c1e0f4102d008c0310031904200b000340441a0000101095120b0341c5100598039030703450407454100b1003203421146440c00b03001c091000b40b5500158405040100800440c54040b810360240d0454189113034003c00b50700000f050a034a480340380d4540780d07c01d074513061141c40c01c1b11001c16503003403030300b94041118200c5105d1010300c0038a5201a500e44c0400541c10312142942c140030000c0c00700d000003803050f481141c0f200354400c410b61003904104001c00d003001e02d80d6142d0700d2120f01c2c48600310041321a4406903182c109050300302031058a0700f241080c0c015010380180e0b4255202212104d40c0140f542c1c0c1401090782c0c911405100c0030816440b00201300944c0110000c2031624001610780103010200102e5a0725418031032400b08804541c0055071500b865561202c3c8449501d14110040d15001201c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 182527850 1250 182526600 182526613
    0x30f0a0c060f0e1e0307020d030f120204180b0a031e02130902010e090709120b040311120414190807150c03050a0f0e041e110408030702010e12 63
    0x180c2104200c05650301c075000a10041d240c4071107010480b82e0042441501c4e50100114001c4552100d062007104034640042e02d141054a40205800001c1110110002500c15481e0202c0c13642c002105050b0780070301d00d4194641460030f00b41c050002c10b90840b06445594076400f48403140c2c0c41e0106000115840310b00c40340c04039501800b42c40c0280d54002c0c180c0c041c554800300001421501d01c03a004500340d058541c0d80c110192401441000d1000600000a01081440204503d100400091340c840d02c2680300e425185000d24004182c503c48005000d00c40c0d0110b85000c0c100c0960b501600c00741e80d41e000311003140e0003200e0700088100c0d44e2140c108410040e070358404190680e012a10400355103c1c220160a04420000c0807540d6101611000d800274005000b6681158400d019000d0305224516020401404000004044800d410300510760404810003049001c1442c2c062100c00e40c00d42c0d40a142417038981103020381c4034803a052000381009000c0d444c00026565403608002c0100030b041c201c420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 182529100 1250 182527850 182527867
    0x1050d1a100503220f0507091d0c03100c021203130b06030a0c23040f05040303050105010c020604141c050109110a050d140c04091109100303050301060c05030f 70
    0x38000d0100115900032441c0310a003481c594003a5040380d004502d1125a0190103010044e40488256600da0440e4000d51805103c4d000c60400c001c4440134240d01440020400103803145111003084400d200c0071581c000d00700d21001540c000c86c0c040507640400902040c1c0e03114010b0300701e00304400900c10010a00c00032040c014032010700e026041d034941c4603882e1200141c881c44d00305503441d04c6a850023045c51070b2512080c04800c20010702a00d1001010200c0d81031b108022001070181c8002c15942030f04655681c0810081c9503060141d1401040c00f0b09124800c1c5a01d83c010a1261185008484288860240c0111551650480080904031221143e2001c4105291090180c60300c03040560705880f03041180640d91402203211000c81300005c0c000d142000c2c0f82e507541000440c4c001d09a200e20701a00c08010302945540c000c01c07041c03074440c54051041c40b84a104001030904090414600890f000e2400c2c0000303500030040381d05527421402d000300c1ca00780c1d0745041841d6204085140d1000100403a0f1800d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 182530350 1250 182529100 182529131
    0xc02071d011505040806041b090c031a01030b030312100f06180506031009090c0306060f081506210a17030a0c0e131a1203030405190203060402010e01050d 68
    0x1416140300d000c1d0180110860502140c3c00d0040d40181c1d480703034118202050010741c40b036130482d420030071140706190310790f980d41007980803101050340380808a5151490b0300e2101e0750140c0c0380301041c5002d0804011810310130004c603036207000707114503844501560700c080b410300a4161103030300040247c00d40c1001e00301d03211480142501d0700b10050b2607200c0704c01c0c6008201403400600303170392085080c034511705043c502c3c0068100160000c0340301542c1c0d1104e01075010001c034065000c0c11020300101047c82030f99500c0c1140e090700d40044034400741e4580400b02e052001650719407941c03203c881c00b20802044032510f9408610b050595241c40200b9241401c00c500071100300ca2400707507106120602d010030036401070f0402a1007e400000f40e003075000358054011903800f9926800326a00a03050440301500740b5500d0042203030000c1700101c1c640d07140d0000c8108030421804120307459001100341402e6510500c1b95000c65a41c0750060703c02418400d003032450b5205648230701c00362800b0041c0c05006024801740000c2c101c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 182531600 1250 182530350 182530409
    0x120b06030903090a080105160c0311100b120123061c0501060509070c23010609110904051803040b1b03120f0a111606020c06010605120f060609040c0207 67
    0x2180104e25109001515242c10b10426100c0c5585410200c0c1034904805c0031070704540501011418031006034030780b01d00604204060160443d811300001781c045290802c012041516036080d40da107a04040e4210240b150150070720069145070203091509403541000070b041c1c3eaa0a1210700c02d51062001100c050120540001d4101c910907100344401f81c40f0480f04407060301038604064059034496151003021503041480c2c403c40b52001000050854442c18202c00765422120101507450300810b00c4c120a19162241980040820200c418045040101961240610300c268140c1500106107a42c08440401a40c010610010256595214083c00d0805a05002d607440d070b12000080303000880328a07076807244010549071425040d0806401d150700d5a90040300da541103902c160203000e03400c0c0740002001402e020340065154a03413200400c10083c0030005005000848981c0000248969920b03040212158024203941c08200b012520400303038580032103584400039580420040c22603100084a00c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 182532850 1250 182531600 182531617
    0x20a140d0609050106090e04021002010605120304083003060a090f021914070f0c0f0e07020c0d0803040204050406090203070b040801180302070501080a1e022104050c01120b06030903 80
    0x10042640c172443c0c2110400d429018001e00b603610100130401514045180340c1e038800451001296458840020a10906041c107543c00300742d10210701440980c509108001043c8040c50787ca183c06040005210700d060a11501125015000004101c140d102e1000903006040300301400d110042d40c076401c00e0002c0d0702107005038002040882c440400035224800b898914a41100700604284003a00d489260b4000751004940800251100041001080740404005c103403e016920700c0780f801d8000607042c1000143c0c0148a241007801180c0001c695400b9642c2081c0c0558000403580c0d9035207020300040c1400b03440a503240c0300d020000200110120002c00c05c1e1a442002030014143c40d5031182484403000c1e01c0100507030400c1105020f40c0d485a17010310f500280072540421403e456404940311b21920740c03c8070083d40d0f0000703000d08598050340307001291501d01c035190305031034034080e1900c1c1c0d15541400c40700c504000c0b42c00024400c81d59140c01030780303032044000c02c5070707559041c000034075503595000450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 182534100 1250 182532850 182532869
    0x7080d050703050106051812060403020708070602030a140d1805031e0408071512050f061807020d0f090b121f03030519051b10050108030c0a06020a140d06 68
    0x781c90500c00e01a0038121001915160b040510108030240000409400e141c1c001c0e404a201c1c240314401000f18a0046000380c01503d50141800713103450400190780c00c80c90541d4000c1011031501b03980051400c0140741c100911302d03150b180c0c6c0c0240e14050500748400c4449007100d4410101801404002003040d14050902c00103402074035182d480713680c00349100d28031003a0080001001403031070109000408800300e1034100300400c0c90701d80c20b40c1210015502d806240b034800c1e00b0490305050010396004244003102d01d0046601d40260000d40e950b903110300316001c008070441e140a800c0e0182c1000340141c110a0002030319001c50040e001a041021180d200039010003c0c610380507803100620800070f40ba0195503440c900150340140426650710fa03603000080250401c402c01d00b06a00c0c0608440400c0c12401602040e03c00082d5a810707524107800a01e0340e03130400c00000107607007400034400d41c000d40e100a0250700d8216000041c0c03111800c1030361080243c00e002518200d0030607590311841c2607480c56103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 182535350 1250 182534100 182534111
    0x90e01050a0602120c03130b120f132a0e0603120406020a06020a0912031101110309070e0402040f020307050309012007021c0c150e04050708010b071707080d 69
    0x401c9454103040c40382e040942c100281030034081860800822210390441c1c04c403032900030001d00c03026041c0600c1e407140803e00307004030b900f0b400060344042c15a00000704c2d1694030400c3c107089004044903100080009c010580b01d41007000344107190307071480001044130210101c1140d80c0300440c40c0071001c100d41180c0304c0d001e003500003e0504480e00aa4080d58459802005403501c90740e210700080d48031490f1f103018003a0b6070000144500c0b0056115103030511a58441c0d0300c2c5407031000307440d080d59507850034041104014805c100d804a000211502120f02a5114884985540c00401c1c014921082d0b00e104044c000000c00c4042360f000b8009500864002c0e000b0490701400100c101c03181018802080b100d00e8003080860003600c0c0c0012403004406642c3d42804413003041d96540c4600d0102584004030b1409a0b50100c040c16401201001205000780c405020918161900800c0140c1c140030352050094003245200074081c0e8003054203c03030154801c200e0368070800c030b00700065640c0004000b45502070926 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 182536600 1250 182535350 182535359
    0x30c011409070b031602030715020d0c08060603070309020d0501150806090105100608043e0906030303012d030f06061401081611030301030609060509120d021e0307090e01 75
    0x2804800c98007604203180c00c544600381a200c5180d07085c00d04804500c410f2155001140280030600c11b8100100c100581d151815000c100a56902a10000600c008141003103240d07141e00d070889038003008c1442c0c001002105880010807006c0342c114090215843d181055a031280d107044901c1c250344065086480c99520340e1405420f0396800caa50085522284400f000110301480f10700340c00c10300ca00c110107140300540c1b003184180c0e210650001c4d80d0017400c4002149903c01c5001c0d8a543c1141501e00c110345d417030b0003804a60303244018410b0340d030109440c00000706000c01c2c2d602d40c0d00d06101c442c0c0115451554904000c0d20303001842c081941c80c0c03441d1030000154046001e540391901c19044e102c1c0007107540d0b101f0482c072240034107120030000e1045059211081c00c405000a60186200e00d500254210460401030300b1658028403402e00341e8029440380c90a40080000e4505100d2a02400b6a54042c02c40b102e0505c0f404541420b000c0341030100c28800c1c917075003000d18402503542c04801800701d83e0b600d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 182537850 1250 182536600 182536603
    0xe0f10150c0b04020a031202010515010c17030c07051c081003021f2a0507090509070b070c21020102010b0f060f03040c081204080f0303040312020901030b03030c011409 74
    0xd06000010495615841e07000616118003a40d215000805240409680f501ea07000b0342400c203406500181d545508000d41c004040f6501c20040701c0a10f41500310070ba0300c0e0349000021003820b5203441c1140001c0300164005040d241156000340c1d00000769003000280f81d950074524559008440c000c250303c180060442c4031000c003c074003103980090208010690211f1182c1c01e1040598501017081103000c0c200055589050a070410a20001c450400c50b002c1414101d00f040360315085021245e085c00c040c882805400190b080540b503407040c00c4c0340d44d004603242854145240703074010902c401c1d00b4004024103040040c20b55204c0350003a002448240c40e83d10403c40030204d030308034299000b0400d0000900c6408144081c581c001e109807a849006071712a00b4641c988581805442d9071203400085c1802038110501101c808415400000c3d408c50078259000350030f8a40720360079240040e50128010f0b07142d81c800d4100c00301c94040039042c3c0ea55000e944080f01d018103009416400181d000c4004601d11040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 182539100 1250 182537850 182537879
    0x50408010c032307172e1d0c0d09060605010e150d021b01090807050f030301060801150e10030204230303070201033306030b041a010f090e0f10 63
    0xc00c0e408100200c1c0000c207050030401000d0420403c0045410001d000760034910085c03030240794040441200840e003c4015800740f400d040c016901c610f04084100081c1e40b0103480100902e01140404015a49841840e841e60080d155651009801d00c001101405401c0c0d00a8040c0c8a0a0741c48090002200080c4400c64204102e034800740a0100072510b0503015903805494001c00c07103074410305015800c8244600b52485101c06541d0360b2000200e05d410400d0400c107120319018103034080c60841d8503064000c3e200f003805101c0e420020500c0310f00c1c60000c6114041000c0010001410070401200880c0003c0c020341140c001e0946d010b88001c07941d030500c50600300700e40190340c00070010362030041144d0046002e001508903410311842d0364a0300c01146014810284000481035000141c500e00e410b1008054800883c8081c0c082e0380307070910031910310740d07465850451814203003040380200320f00da141100c51100396803028035101594018401206120300c4014000c4003018030803204141c03035401c0c8002004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 182540350 1250 182539100 182539121
    0xa0f0c030f0503060a0504020d0c08060315150d1407140f03060a0f09050d0203121e130c0b0703050403050114010b0d05060105070b13050706080601020307030e030304030f03050408010c03 82
    0x120284040c4403510b208400550340700304081c0c0043c440351703a81c8001c13806a820005400040300e40b503088410f411030340000256407181085008010008070300c00145150500a010300094186040c02544c0342e844803c0c1241caa15840100e040302890020f088a8445540c0d024160324010340f507016203610326200821200803035009005e807001351180400c0b08010300113000222081a100c1000c240442c1c81400741d841254140e80286540d000c0301032040802c00380080c4070b2040000c00e440d029510303c5100500d154480c0c81c001c1d5003100c4408904010a034207d46900c1045030560000301c0d0800c255012001d0400c0b40e00c01c5000b8400c91140302a95050a1000d0062900039001480207000c036080c1c44d00303c640c03c443c060610514240c641e40706c1e080585012502d2a5240e44000c20100c04c008007007264030024121403816103143c1c01d04000003501d81c0300b240c4000e020071408070886106075078180704840045034032011102400b8510320300a445070704584039200483d40f030081c0310031256000e8050305c10b480 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 182541600 1250 182540350 182540357
    0x5040608070509060d0b040f0c0504050123030703201f02210423030f060f06060714102c07030f0312050103241401061b05070b0a0f0c03 60
    0xc0c0c0c100b10600450007001004158000604404c07500030540301c0e41c105029034000c00d51114994a5400c100f101c040480d0b00030340c0180e00e000010001e0024403070b0b404440c0100101c0c004228103103407001900d45040341e00003424100488a6103c2440e80403c914245980159040102c43e92424900c0c0041c81c40701e200e03070000d60051201c1c00804451405091003c034260f0940030704140d02e0344111903402220a010035013030294540b82100d246420412f96a843d90800000c0c03810303141c00104020003210180c0141d0054402084110400c60a43e05024840d00c5c45030032180c8040e0041510b6001d808007402c216070711010f100c0e030f540351076041d44020780c0400300440c000c084092865030380b003028161041040c3c0030820040a000382d64201400381c02d000314091381000c80500c107482c00e03040c600c200c00500c0d500524603214080f00c0441001001e5411105581001429804a40385d036101003092184001c0880c09140004110b400001d009884580c0c590b41d00d15640038100c2c20183c400300c401a6015020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 182542850 1250 182541600 182541613
    0x60a050a0e01020306150307050d0606080601030b040207030c2607050607111c05030403031407020f0c040c1b03020a02060714070e0c030f07050c150108060a05040c0308070f020d0b0f0105040608 85
    0x41b044940007103030070510a25106250500c443c04440071600c05800242c005030110041c0f00241da41030140c00d441d61401c440c11858941280c0c4e000d0003030f2881e510b002701008100c525400915900e1002e2086840d011031269580b5429403400340e49a0b40e00f1034070100418605101c0c20b102c0301e80001d407609103601205070800d8260034010300b81c0b456000140118101038031007480c02d4040030090016805220150000c0c428034213407102e05030402e07208020b11805039182c039120410050b031203c4207900d1101d070f442000224010300d0a04a082103014880a5041300703002428204001c0c0283c840303a440c6180d07000f078640321516045210070b2004282c0b0588400c5006201246114120007142c54100f087c5003003080c90700d40140b000c5810014a079032802c40007020304004110b080810310a0b80d51103035060008100914042d91840c18200e000d001c003400d9000302041080400c15400650704032960010060003a111840c0f4111480d1501250388100c0c410905d000000c41d03003464000d642c01d455101001d040c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 182544100 1250 182542850 182542879
    0x303010f090605150d0605040603080705070e07050924030c0418180312090b01060c0b18032506050a020405040b15090415051f1103040e13080705060a050a0e01020306 73
    0x310b03000645c00324200b075903e140009050703603540306e01c400071489070000944404c5581002d0b801d000d40e640c066541d520300170080004d4154050116468008100ea03003101014110142810000c00012441e05402c400800d10a0703001d8410083c008842440e0001c800851100e5000b4041c1c48011090711380e5002c1100070900028042e00098211018000b0700003034020003502c0d06030341c0c5002a444031000c070303130001c91682c00c0c0b001045103a68044c244519111341c56002c141c40baa40c92007501740000f4083e03400020031003a4000c1d0b01310200b00c00e422050501035400c00709010320096006101d004d101e6071070544580c4aa040c00702d140140350f6141101c2e1802c01414106110240003607484040780e881681e6000710312503030f584100c6416204032010401c600d0312507200140141100c2d024003d401c0c2e000780410032a6018800c40e50764414805001c0440c8018249060340304e40c00703070050040260040000f0000e6280841c0d008900c078411402043c03007e100354020302d174200c2c4400e13192240c0045800700403c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 182545350 1250 182544100 182544139
    0x9030604060b180a0507030e010608030307030c0504150914010c0b0406110705030c0705090106081312090909060b0102060a020705070b090102160303020a0c0605030114090a0219020303010f090605 86
    0x41d40c10b08090029035640c0100c9044400d482400ca5000003416619403e0210300e581c14031a5000d40b4090a000b00302690500c242e0710b640740401010390b801c02d5140c00031000320078844d1050710f00070a481c405042641010003c0a000b044540c0980c001c04000001000400c1d88245050780c078554025100c150a070303e8a48074030018060800014840c64800c004080c001030041000305040b445a401401c240781c141306c200002c000060b403004041000c404e061140821401c0390407a05030360b0108442400e8803805401741e4030080b1035400340c2c404a01e0120103009108041c1c0105000b803009034203540003669440b111000f00e00501d03401030310980c801c00040c403010301441c0c014042d00405004030340a804400d050003c482c144e41e041200140c110781164020090001d060380007800b16800c043c2e05641c10a81e0f081100034024010031721070b00329040400e07106841941110110020b00711850900c1801120195030f9900a115080d0103c2418030b000815510900c203a0081c1c0340d0041103105013007124036240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 182546600 1250 182545350 182545361
    0x303122703030b0111070f030c050108040302060f0604060b040b1306092d092313020d03030b15040617010902040f05131515020607030911060a02162402030903060406 73
    0x541070001181d841d1765071940c100303d420003c00c1d09982e0040142c0c15440d0940384164180c0c4510b052248a40c203200000e600450125070000c12008612619a50070317000401409160b8000c59181000113400f0035518682d500400c0c003425822503203c82c0700d85d070754000c0300c03aa0024840c4201034064441512907a000c1c003200307814102040c03900e03000865280c0e10000102c03240c0200300c1110f011038500b0200740d6610226040c2e03103c400442d640b9080100c94010400804101c68000d040513aa106080030907520418645840b00261400d240c54a03202c420103440101c82151101c0240c442100005d800c44542c02103130305807030b080458400c00600d450103110307028000300312196916031111f80708500c1c1050010141c00030105111092203440e285c150107800d00b2070107401c200825050640d110701103208a0600385904c44261003403a920482c5071801c0b0304224448411540d500c2c00c0d01d80005a03000440000c12840c01598a0f01da040c107014801641d403403003140d140380c0c2c040d008400000c0201f452503010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 182547850 1250 182546600 182546621
    0xf1e03020613150f0b10020a030e060a020319090816031a0622020304150b0d0206090105070602030906040c0f080c0d030c05010f290604050609010c020307030312270303 74
    0x74894209900c194a000da41c01134244da8071880ea00d0a240c1e1a034603010000c00514402800600960700b11610000e0416075890000b50050f0400219030840c0d91007041120380c030882d04a0088114041240010110704141c070a0f4000c51040e80156207412000100001c222980008041c08020141070510701e5140003c00059002d0210411040c2c48007004c0c1c0c01d03150b040004040140d0364503051402e5501a5103902440a031a440c122491207191a030322869804250100d403442e80301d19030100100d42d80d1142d101d00074513480c008402e01116070f10010303056000340c0c4201c00b40f050030b036211000207004807203e2084120700d9004807071000381420480e1214a10f03d002e403410440c1c62074152159406d442d01012101e0019540d906048826503841c028a0b662803440f10b4645140500e4000140311070043c0e0082c14401c2c1000141c4484e80e030300034402d220030303a5400f406036041c0982ea4100030b020074650685100a1604140b80241040c1d01e0b03a6440200c0007494001d00f0500c8500d4034120010800c0480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 182549100 1250 182547850 182547863
    0x1806150f0905010e0a0506010203070b2205010b0319080711030712080910111209040906140a151a0c070902030901021b010221090115030f1e03020613 66
    0x3003100200c81410308081d00720782101107a00e5141c012100c50303a607001441c80210358500300501c40c1580e400b00031146035a0b0040e6401e80951660b90780007442c1448000794151a0082200000804c2010f4006c01e100660403030941715850071800c2445415012450014604c600c20003462001450b118010704140340c000c2c04a80b0115202c604094500d0420102a544a8070108e42c1800a262110a01c0000d0005160a820302c1c0b20840b1225503642e0ac0c503c040f007000320042803507505611243d010001e40d0390059020300440300c2c10380703810320f0105040d120013403900d081c600c0ca00b98050302d21054000315503d41c1503840003c0100d40036041c883d0003000f0815414040c60340c0004880300540040d5000d030030301100045e81c0e0b095500036424803540c202a00c03003003a401407003810560003800015100880c00404074049039540c01001900600340880d1442c205010424040140894008140f50380d900c6028010044804005121040310354818014016844200010b107009500c0503043c4107184640c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 182550350 1250 182549100 182549141
    0x117030c0a030c060b12060c0901030b0d110109060e030a02010f2708100603080906030705040906060f03050f270f1c14030106050d090305040306090b01050901091806 73
    0x80c1d003004107020003500028501040c002c2070101d80e10130b000484408450b102901e4405100031b039280c0c01d001b17155a2400c040032980850503402a0032001c0c1e000401480122030741e680b490310800c02600c00c7e0b80c2c0c0340040c00080d0041282406140030100300c410042c000c01c0052003a5004468040e42c60307203400104250f2041101c184010008045000e8a07042408a6190704101d0210714041000d41c014903000d0030403004102003000701d001c0f0f0b40d0450341a0740c5d150340ea545040094580f440b0341d030301c43e4110501e801000600d0075484498000c001c0600da40038400c680704c81c1c288800c405010380d00a548808000002e007224044a04d440c4001b0900005951200700d0b030048503400c001101104a211030902c41c1c0902c00c059005444c4154980f0079021b06045504000000b4410300404481a180d03039603907850b450a150256040d200156880902400280f031f151402c403090080030321445015241034400450303544214000e181d00704072402c030046812a081e490340005403503ea00c03814210030040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 182551600 1250 182550350 182550367
    0x150936120703030b06070609120c020603160c020a060210151404052e090b031504030806031204121205031306020d0b0301230a0c080105010809010b10030603051212011703 75
    0x80c0050000b0034020000080c0302c2408d03007400e02030089440c1c0b560040040600034035006988040580780c00c05600003512003404418402561a002e10910103580060b003030360002451640010100342050040301e0a01546503075008281101003e4080e480c00307000c0402c1140740300c0c00e20f6800b280d0b0101616911421109140038102c1c0b0000039075180800080201c80c09001c64203540c010f0341154841540102241101109100300184014100408102c540004204140d03800c1000301d45201e2a00025a0784170b549182c20354001c4004c3c203045a0020071445101c000034051300c01e4a10881c02548880300c140804d80e80c05001f54059291007099a907600140c0c51191000d12a10314520715400300040174000e42000302c0c401c0e40c001044005080d08050f14136902c554000051811a00d081c00c040b040da480c0c402e03020303002d0920b207140e840d0080340599030b1842c01641a0031201c00c680c002d00558500308406021840188079140301003c070302c10320b03000402078080307e50045c0f00c596110201b501e0500404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 182552850 1250 182551600 182551609
    0x4050c030c28150203040306051f0e090c09011202010806100203090f190909020a080a0c060e12010c050a110c06160212010204030303060f06080402100305150936120703030b 76
    0x2400b00f12401680f02090038420003400c0c2c13040ca50820402c0914000090746040c1c15074044a840c0140d40f52540c0050110320110701c1040652810360740181aa83c81d50303101c50700102c00001101c2c050340043e400760041502410400038003403c001c03850340510310f080b001000b842407024000c040346820005010541d40c060303400a0400c3c01038001400c01044120b103500401000000c190042d0019400c81c5181e02c0008100320540002c580311420207000c205409400601c00d8600d41c21000132035402c2461240c050384c2c4c0400149040c45854441d40400341c0d100c290269508124030b030483c1c00c03076010024403c8045445941c000d450744020003040d940c0d40800442030a80c3c00ad81d004a01098465400740050002560702d1805032009290084842c9072680025541c140e07090a18414181d603000407584e4014001e006401400d0090300e0700702242410158152006c4241105600400503141900203200c8813000c840d0940e41c801e4005e000e02c0c20a812070281c036501580084060559840002e18070780c85 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 182553956 1106 182552850 182552879
    0x70c090c050f04031118090c09071b0b0a09051b0a21111306031118040201020312221401060503030406120b061b0604050c030c28 57
    0x4480b000301b03181032551912020100d104604101030000001060810b190701036544424030768a520040301c000080c1481000313400c0e1400020400708141110075034002d4602e110000310501c0f00c0d41c55900d041705030100d0705144000d0383d00304003130f51418802c010003d03c081090a20000d4a820741d81b880c0601c42c500060803118201002e041540707804400c011007580d60403082118070b07220b0604600c807035a48411944100500449001e000d807501402600490f410b030015820441c04141071000c200005020703005e10822a24200c1448a1281610b804030b40111954200762015075280c03820b464507604414044e500070170040018580c021407502000030045c0c40080c050701c11400240c7d5600c1051120558032081c10180002a4804114070740502e110740d00300c81105880805043c0c0354411034200704e520419030706801044902da40da8510900441d80e04046066440700300b01c410985 = true := by decide +kernel

theorem cover : BRFrame.Cov 182374100 182553956 := by
  have h0 := BRFrame.cov_init 182374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 182374100 ≤ n) (h2 : n < 182553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
