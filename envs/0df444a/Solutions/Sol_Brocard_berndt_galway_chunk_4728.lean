-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4728
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:32:48.394259+00:00
-- url     : https://prove2.me/submissions/6f6f00b6-a6ec-48d9-a8f4-860e1c1b0a23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 850179856 ≤ n < 850359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 850181106 1250 850179856 850179859
    0x40b06100905030604080a03110c0a020607150e010b040f0c020619060b03070509040c11062a070305120f041211070506040b07060b0418060e0f010e1014070914 70
    0x200070019603a0307010312080c0c0c41035025802c1d00b80e0750348610b5801801c49141d03e100d00e6410a044c8414458201c0c00101d92106a605484080d560400b81c144004549461418500c405082032400b18807101c06412100e600001560103200d5101917640340002d40709440c0481c0c006a00c28800241c04403403a1108810b101101200068019201c0e0981507203540b0459804000c100c001a240301542000c0c0f150030314401c020700d001c00001d500d04010640b101c4020b850303003101010030b0700f502418400d401d10500500040700da40d5503072180281f40162982d0040c0b59200c0a151240000900c0b145008102c2d51240390300451b07046c28005115001c2c0d419200d400c513440d200784503494003c282a2070b110010006070031103d21490b00c80a50f841c004051310501600d07a070255003000c0c070002c42e18402c001c00f046029404000452100c00d1402540d1801c66041501001582801c0c10500d071030f5000f2a07545c507540c10140090060300307050701800c6501030060f03581100141e1000010040e068041c000391070030303180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 850182356 1250 850181106 850181117
    0x405131109120a030e033904022106031207031407060507200d230708030c070b070e030a0308131407170a020a0e060303070c03050321040b0610 63
    0x70940003103007049040194a40341944202a10380c14103821660320303007485408900500b07100b55502c001048241ca28002d140b40400c00d130004441540001c116051140400740c42151504440a1070000d83e6401001c1d8002403070641c40400d03064140400c0e95060010020207052500c40307107a408968030f105013441200c2c881d0040c40b4a070000384140c02000e0054545580c0c6c0200804465940c403a400c0c044210300a02e0f0b0301040b00411101e4124180c5a5040b091581c2c01e02d50341d500f9803c40c02c0390f05c11101b004148020000400c0000c0500c000503100c0c50740a050500e0141e6034003481034640e003040c5141c0341c0e03040d8804d06040d40068802d0381000d600a80044001c094030034541c1c1d80c0d0b4103034040c211030001d80d60040c040034070a103440318110100424881006003003112450700442e01100e000c3c02008030100542000a4064504004071051164445c0c0f003480c00742c0c0d40341401501c0e50803003018107007a0400101102042005200703120b004507004007400744103485000400000c4110200140107109 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 850183606 1250 850182356 850182367
    0x31b08010609050414151513050901060614070b010506090a050d0f02190608010e0c120a09030806102705040218040c020303010308040312031116020405070504051311 73
    0x80a001c0d240041840b200c010031242440d1420448125100203544c04a60003420900c11120066008035041120b801030455600000e0300461184952120a4007000b82003800b0300110784030540c030070001c980483c3d64201c1d5071f6074507070070709000b0740704950b80980355507084e82c0103110500e402c0300200308245c40280f15803c115900c4004c1104c40408050540d00e0841d405840c0b000c0d400c1069203000343e4903880c0340e40e41780e0038100f40d005002400180078041484641100003070009116408481c401c0ca0031a184032401d14100e440140a81100c1e042100000c00c280042441400e0104044034034220300d8850407800c0c0c92401c41d104080d152002c904454003400e4000140715103581c401040038042d80700c2582501c0140700140002d03640500042c40442d88100010004281507030260f41c140c1e503100001d00340500308294220007a144491508400d1480000c0140c40e24520b64101641c4503c29a010b006075922080142c619014a01c58a604040320f00581c009002c0c031a802641c10701c1000e26002c1c20b10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 850184856 1250 850183606 850183619
    0xe030f0c0c0d030305100e01180203100f171b01210b13020c01062306130e0109020d140103231510031401020c0a0303090212150a060602030c07031b 65
    0x1d84038950243c010a030380f54140a04200c2500a00e4040c0c400c074031100b0703207a514101660035030301300c0210b50210007175022000c100b101e645002844000e04d544002040c0c5152030310254031107100c0c0d24607100001c1c41026515284024030800700414028140c40f41100d08214844051044d0200000900742660305d4071041040d03919a401c16801000c00d00b00180c90f542d20704043e40c212100b80d0480441040b40150460480300650401c00110500341c0b2002e4a6606101c2507000303c240c0d503006406c420300882c4c000300308180f8a501401c0d0302d80c0c001405001c104206400e110a4a070700380030150102181d10f40c0d0140881b490380d5140700f5030b40b00c079046a13a0304a4800b0003600588042c2e41007030310301400f060104188481340416001d0b03403203814000c52400300c046d841c0c1e0b07503500b2556400805142e20307500c0e8101507549840e2425444510101039444030140c0c07031411101c0550440740c00440b24070f40040030a03038030320010640301e1074000b400050100509544403d402000400603c0b484400e5074400420b44 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 850186106 1250 850184856 850184869
    0x2d0c17191113021b100b0f13021e03010b030f060d1109090c040e07080105060910150e0907031b0c080301030602031b040807030b070c0803190e0a23010e030f0c0c 71
    0x5211084c400b40c04000d00c1e5001130425240c121a4080c4115100e050303080f0a6698a10315011804005070300580c2c1c4d121081d8181020500c0354641c80141e540070000048109074400214410380c125540016259504820011020070800707028100b040a04010030a509004100c260400e000780308480503001c074000000c05440b0f03c041648080e0308513540401603902c09000e4103402104c1242d140d002407400f09061068255981f0514010801000c030059896001e501210420f10300504100100e10b84684090060070140304026100f02c00c0480d201c20891051021840131a80450a40c0c5035900e1511550040e4002821401218503130341103160003500b88400900051011901030180ca0b0320354213040c49000c500901c090180541032012500051100088990000c510260504030b40c811380c214100910011250204500c5401c8446040c0038400750000d504622640c45016238880909038035099520b0b2510b503003032507482889054130b03028140b006001f01c2c4013040100d84041b02582c001409 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 850187356 1250 850186106 850186147
    0x91905040e0307020901060207080d0f031e14090106060c1b080d0807090506040302220603060204080f060c090d14030702091018092d0c1719111302 65
    0x4154400030f490001c5080c8825440d0041c14980068500180b8003454280c40b040c404207814108540760700313135068081c0a9031006c141d541d0350074298450481d00c1c01d00c1100600c0351140490783c0070090030000d0405101405003d00380d440c0d47d40d440108415560300c1e00780900d05a08210380700e040080001c90b14035020024914a41440c0c3c0e2869618184650064100d503100d4028500440b420082440542c80b412446030700340301080003203040c214400c012400108041d410090800d800002c00040e0350380300140c00080c40d051b4000396400b40d268803000307034110310846502a0700080e5440c841e501081d10310141510540d03400c03013640c0c42c155035980042c3e4040c404940700e00051041e680305110b01014013010700c0c58100240b03020000e032007482d156001403000000c1c00c51509070b00603007500c44c018150350003880300c1940803c074900d1907a201c80a07c41000c003d0b0b152070450b8490100c2c81ca003c0d2401c23010344044240c0065401403111141424480514104200030f503a158003040054007000d0050307034804 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 850188606 1250 850187356 850187381
    0x3170f07062a170415020c0f031306090513051003050a030519170115020a020414040b1311040b060f0304030305011712040e040c0f030b06210309190504 67
    0x71441d00803420320946480d2040d11901c03c12094818103010003802410300358004e80c10000c490240d034400201513029100d00d550610f05030085420b00d02c03000d4000800350280c001d20b06205040136488040468003982039100721680042d00b207004000f4000158409500640355040c02d2120031745980391030380340081682049002a000240c1581d441c0b081c3c820b1001c000d00c5070f140400c010364150001900d455818011000328500107009540c0c41802001440324070703a4064800c1c4000c4a0320031002007040d800315001d440c40e40c1d907c4001508200020360403901d075603000e150248215001c205210041a400e040d0f04e420600811045c00c000580d50040e51080344a6680456990b04100500c9001d2841d01c004100a40c01240045540d000d4541600c095404500c070f40c181680c1e80c2d081104161103558002020003510150100900ca40740400c144201c0050b5801480e4840300082000d040c3c200404100c81504203014461081c5841101a00340d02115480e00d1000d81d00d850020302100c220302100e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 850189856 1250 850188606 850188641
    0x110309062104030c170f0909070e180108060f040507031e0b2703090604060e0a03020607140d02160b03041b08010b040b0303090102190624050f0a03170f0706 69
    0x860800c00b144000c1158602d1440c19181406d101404103503044c003840304001c0c03003401d0120000300d215204000090f5a150000c103c411050100c40480c11000b03428001d0101c03900504002032107000d182c02149000d141d100c00140540741c6127850300b01503104001c1d1641001f030303080c9110801103890707001c029004000d40445280c40070420000342d103180303440340d1224032260024050300c0c005039165425102113480500b1309101b0b80c018440014001c55440d08000c0d44007501040302d0040c0f044200400b180c3c407083c1d0084642c43e842c40c10b420380c2e41e0b5100b01150501881003080a00c030a804002c06140c11901ca0154081081800e15075003081031000d41041c241c0342e541c2c5d0840703035a618050140303104c06d83c0168095072034a54802d0000351a41d2001c10001191040030314110204901d07070f809080c2403103100c042006e48854103074022007140384070310505204141003c000d0704117151a14100040781da114240c039198601910200446070002240103101010500c10f00c00440d2b0781e80070300300c062000c04521 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 850191106 1250 850189856 850189877
    0x13030201320609011404090215071109010b090a181d1c0c080403030e03030c0609010b0f0102012a030207050303090706031512060b040e0f0f060711030906210403 71
    0x40070708031002401644100540801000312003030240c60158a8a415240031035160001e00100700030b440100c4070304100040000c0d070030041c00240380c0b130501080e008440404280c2d980d01c0810529000e0341401641c4610b441400b007051351410750340d01854181c1c20501144042010380e83c0c01e4a001022803c010760340044418030f02c48800da00c81ca603103420940c10304200501c5182c8822050303010f10700004080c4016a00c8003c80c0e650704005445556041c2c1d4201e441c10700e41744100a029250b43c901a90145032894030600351580180903c00c5406982c0410001620502c2003407041030819050200915908202c5480420801e10065114162210040c0001c500c1d000c00202207504200400511200d001018401805452048a001c81d080400403410f800048001001000c01800488c2c041c841d58004450305280452140038100403001591159a00c10005442400074048084003a0b00308000710b100030f180100141859082c001d040c2c60421507a540c030b032040120151400d40204001092 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 850192356 1250 850191106 850191191
    0x61e090f1209150a0216060c0f12020a0c090e0601170a030806121608060105040204060807030f021b06060301110306010215041b06021f020702150904151806080705030613030201 78
    0x20010310b01460640ca40209a4031100710984004030001c05007502c0098014a07140b00b04004cd90031900040c1c002a034681d124040c00041c110031300c0b00f40c0c5c00d000d01400044c400521004001c0c80703d01e5032001e0701404400b80d408651903140200b0290384034400241400b4203030810010700703001c415540120300c5600c6c1060310340e40c5000c00590149101c1e41c0100014052581d000c0d05036034100c0954200803906083c0b110210010340a10341448100040c510004030051000140d0b1a004010540c000c2110410700b190f110520301c01200c2c014056271080b524241861803801d03100ea80980a06880f05420701c051010000d007140759440480180d00c04104180c00010850a0342034002c1e8480c802c610380900d0f640801c0d0f03094503c0008540079003010415020b9a01c1c0c5d03410040da00a081605449000d89a103000740014040d03040300240c1900d811008039010000046042c29680000c006125640c0c45920071000c4205a050440455407100b035080c01880c150000c0c1c014042c0d0388100b038244882c0d19003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 850193606 1250 850192356 850192393
    0x301050c1804060b181f0c080d06180b19051507030512010806160819050c1201150e0405060f0d02120d020a2a1412061e090f1209150a02 60
    0x1e0501b0243c01c5100410710703490f0f0b0000c2141803d1544510240d40b50109000003400500540d8402d1000c8602d9101c05a580c00440c2d0040d003034420119a40010151011083c1e4480c960300d02070150001d00c802c02c0402c5c01d080d005e0207000f60901ca46040c62808500702450f00c0591020313846902594468414416180060000042c2500103454040752501e0b002c0d504110341024400d00d08200d40c1d036070f400304111481003411034000c200c020440018a50355880120a0190040c1e810340008101c2c1010121031f103440e0080e140a10f1004000f45040e000b60820002d0083d003c101c100c1e840b1804015140c10140203000c0f600304d114841e0098a42c090701810f041d00c00e081d0401102002820b0b40d610780d40e154031278121500903030b694507003041d2000e81ca110102d121507800d450000d0162003078604026810008590b8090042c840c20304030802501c0d9008526550350000c0007090b4160442000203902080c80809880c0d4080e0003044011903240c4081c0010340e80d8881c102d4940140c0006020f400c3ea141400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 850194856 1250 850193606 850193629
    0x7080a1b0c151d300904050c0705030703210606020a020f120604050c090a06120312060f08030414010306050607031803020603070507020906010206131b240206060301050c1804060b18 80
    0x302c10318500042094416864403d4a29172440389950340080780c41c02d0700310320544d40c809a0000880b1758904007414083c0110014500f03c130707220680106942850801c40c06034104903500340e001002d0340e20710340d820040c0c00042090402d8102e0f428007150111400700300700300c6010760f0094000c1c018064070340c820311440c0e250007080010205e0510104000500e407884603042d8243c1c240c5069072103c40c080b94968003410950b4081202c0c103031001d034082419a4040010002c03540591a0f200000707210400540c1030303485178400c017070f40700000380820130109004800d0604d80c1c000700302c20002e8680d145d500140894000341c1c1c1c0e15002490100d03000003141010030526420a009000400c00d5140085406807406106034004101c080d60440c5c1e04a42e45540405d00042c100070702c1c40c0e6200c081500403240310041482d101d40c1c01481042c0c046680381c14188580c900420324485854904100d400100c1207449200e50300079080742d9541300010b26045610301034a41c101c6507004514254940504000c0c080c040d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 850196106 1250 850194856 850194913
    0x61905041509180b0d06051e0a090302060601050f0f0301060c031101090b0106050904020910020c03070e0c0406030b2d0a0f0b030708060a080607080a1b0c151d 70
    0xb80041c000c101d034400a20a001200300030100f1007140f0000030901905004000416940c100700c20f010550b8880701c0001d003c40540081210345648a100342001d0701c0c034501001d40560000c2c800b00e481c5510404c014401140707207858403458441c080c2c080521650090340f0500005601054034020107034060919040d840d0a039009002030310303440e141c8010a1030180f069405100c000640b007595038490350140d50085500904072143e003041d40314041c0d255211074641a129000300303070010403146640542c2c0c034010b0206400130341c10301d42442d20580c01440c100c0e56159201d0440203140c00741666400200140e44d854900e8807244246210910009500780e0f046000d000e50a40000e00003200c0c030742e00ba203074020344034601251141c44030030201d046803d02c0e8002d5230203030103100100100940c0104415001d1002c8035020400c144107200c000000001c200d8100d00043e8541c1c1d1039202060340c45c20a5485103070345040002c1d048507811200c0c00098103100c41d0306c0454101e003100d10301d400303c01c14801166028 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 850197356 1250 850196106 850196117
    0x715080c09150310260c030609060415020c0d03060303030e0f15100e130201080105100f0c061506020a15050705031303090b4003060b0619050415 64
    0x401400034074500041002c1c4801e4041c003000259520030f404501038001c3c0810200d40840d0103421070300d06100e03a00b858030b124a502c50120542458140060700d2403194405801421480d162561062104803001c0c080c204426001d10418030103000c00e001e44142e03641583c500007a034514501d03000e41560012200c082c0f007070304620090b10030400089a165012441e01c40c550455035940001d015a01c0510b800c0b4501c41e541d1001000000b10000f070b00e6071403d030b000741c0304c011950b030b80d4401b0440004504807a210024822400340701c41e1034014460482a180300d40d50100305000d4003810360000044990182c0d0069202000403420b01400489130f074040380500e9414840340c60607210140c20717440090903281c0d0301090280c0207018984642c894801074104000c01a68a4024505d04404c0e01003550b4032452020010f482d042c1022a00c88010840e04a414100e1003050f295449090007403507c2c08110f80c00040800002216105030349204070600c5440d154503440341e0a10038080b00800d03402d0581400d001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 850198606 1250 850197356 850197367
    0x81911060907090b120706020303190c0f031d0d050d05091506151c050a0b040903080c0a020a020a0e0103050f0111070b150d050309030f031602040b120715080c 70
    0x102099200644415103800b0a400300b01300d000c1600b02242c501004d25502900c04042042e941c040001c50041c0311000348465020314009011045880355419600420741003414014a01d005c2c1c1c2084100c21181107051100159100001d824000446080c10004e4800904920070001e14424139400113010030042140c0701d45010400140140508407620441220201003070303022904084580a0740542c0941100c81c1c1c024144e000600750641d0b5010b0002d0500329419890f00701803141e68101501691005119102c011445106034400c9010b0400c5014407410308000d61504040e240c003e07c40f607581050250301d542000c40c00d1101404540c40742d641811042810940f80e0700544100301c1d0402ea0304100c648a0080d50a5010004044250000c01c981001002d119020019200d04103050341921036907520005c42944900c1540c0103d921342502140c108051708155028500c00c4030050b001c003048846140c00c4a18002c070a41c885000910181c00841207294884c1c1d000da04042c207071a030039003082d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 850199856 1250 850198606 850198621
    0x501060215091b12070608150d0f020f06070b01030503090102061305030a0f200a020a0617010e060604031709040612080d2f031e04051e0a08191106 65
    0x5400c400c0d009062a26080120040f40d80c03401e10b416213212815044410841d604d08002c0c0c054601202c46040c0c0400441340c01d0400e0402506140c900c0781e010412070200305032682041044600035100d190006818806a00010104407800340658040c1004545a80e03009000919080b001048201c103111401000c9001a10010586003990a141412029550085011276150506040d01601c0c2c841146072704d1040e91022800290340d41c02540e480148548565041d901c1c80d03594000c4c445c00020305401005400014074159810a200403c0c01c1e160a541c0d49603070740d805c03402e8010040001b01c0000d448004e4079192064000501c0b200e801465015115110020640103103c140a81aa201e01c602501a000304807280f0801c02c402a0b19260083d18100e8002160002c0f95954254400d145c7d680c9061240e41d818107100b658000010030640507503155401d00300140c64040760700c038400c0f000404001103001e409000000c404421400540522220091426802c40d946c1102c1d074001c3c0e004d00010713 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 850201106 1250 850199856 850199863
    0xc1506060415050c2e060b040807031b0b12241005030405071a07060b040b060403021318080a080708100909020f1f120c3006030303050106021509 64
    0x8100e0b05091941d01e481400d040d0609001121003c0d28000a60074614000440302d03041e1400310b00000301c400c0042d95141c0c5542e180505c640d01a00c00300c2e07840340e0300801c00542d06400750310314001446450560f06a40e034009401c0e030b800244441d000702400304100685180045090b145410072018049000406240888d51100a120a0a04002e000000101449010020300004180300e90880d0301c02c9148009401994010303a9088410a0074115401d074185050b025010034518010701c00303403507d07265508101c02d00005034005101d1503110104101500290b981b0080a24000c2611580e00d1021100c010300c0c2c5000101040f00f4803500005006030b001e280d042d90301c155044074500041d03030310722070000464807005024126403000c0d403441700611102c0c1c01c5030001d0300d02c040e0f03450382c007007180c0d0105a0a0595642848840011f080c9005410310208020808000302c5200040c44040c140540210026140c0ba60415000b00752900d004100c6075504000070203a1903040b6841da0303020300708541d13a40e45 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 850202356 1250 850201106 850201139
    0x6010503040f020307060e030714180421030207120804032703080f0c010510030305120711011419181401110d06080c090903190210020c15060604 64
    0x1001404000142000140e1203a1a05240c00404584803035551b60703070007400c9611080c042d81c003074003482d07400240782c5000701d50700050080001d12210304031b14004014900154010f2095805511844200d0040d91045190300040d02c9996009030392060030381000055080d8031b03081e210400401004001c0407a80c00b85006c001c00400c1440c441c640300000c0340f150152541500080c00c200302c005540f207034164500008083d0812210004e00c2203944040181409409511025002c103904201ca848403480d6052000c1c0c0c040401d0411300b48950320300f03075000c0c03c445841c800c02c81011036078400d01240440c0b08500040308403941e0790a1142c9084030451280301400940020300c0f10007030f0302c030804d0200000e405c41d034081d40c410901c2c4c980356024a201d0f5400b03060346d4030034218036000d140701214483c207080305c0043c4035840c1c4800440c0350070600034980046001100740a0118018078030803500380000b9000410142c03c1d04001010301c1c0b64003202ca10585000904143e1049031300f008104140c0150448665 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 850203606 1250 850202356 850202359
    0xa1d04030e010e030321070207030f0b07021501030602030f0a0606090603090f14160510080711120316020609160519030203010f060e06091513140f07110d050306 71
    0x1851051407100507210011a00e400d96494000441c958400303a5001c0103003c43c0042e421164022620b511900341d031550194000171341980e0f08c094459010030014440c06070800540d02c1100e446040d03034080e000511000b0f03007003262903940010074814101d414070342198000020b804100b10b02481d000000e032805100b8420082850740b0303400d10324148020240e00403070081e00081011440742e04400c82039240d0f42004219042c4d02c01620011902e814418560480c41d01c964640c102d5546410000356694500030702581458840d00d4598502c2e2100c10300558061114480282c0110849841c0641020802004100654062080805020044004442210810f440e034503d01370b014a0744a107440380c4d540001c2d415608040e481c81a0740f11039407020040718030b400d40e0380081c0d0300c0e250100465034400b620049420030000f02c0d200c070740c0d1034035800181c20400d6200300021032045010302510115402c4845d03003c000407002c10404440c1e00035080c01e5145201c035004c2c1026800301c05d00a01180400f52645 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 850204856 1250 850203606 850203617
    0xa3207050f03031303120b0a260d0201151d0103020609030102070f1110050903120c0304080a0302063408130203070906080d0503070f0c031b0c050f030309030604200d0f020a1d0403 79
    0x14010400c41c0308a105902800900703640c1d00b105100b03006400703037000c4690708661102144000490301e1840c102d03854014155a030b5480765910315002c00c01d00e50030445030554195400c00144002400c031651034490035102e14880186213003a4001c01008881070790942e02030103010420341907940e42c042145080702d001500c4458462a031000618034600854000c550709106001048003450740000b0500d10075400000c0321400900c0081da090130502c0d04141c00c2c42c240858004103030859009800640c3e001c0c1c4007500c8a1188007107500040c3c90000180d003c03240c1c99988807424007000300b00380490902c04405050081c0356090880004041c2000d04003480104000600c0f0901011300c41c65005002c00700107000c1c030a40c40d01038185000e000b2101c0c40b602c2e2056a09000746075080c10b02005aa94050004000e02003d56660b20341180c2036072030720301c10841100340058100b0b4940d00e0f9202c550025005143c07584040078288140078060f0f00783d8010352003446c1c800303100021320f1405038080e640c840e40c1403034171 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 850206106 1250 850204856 850204889
    0x303030619081204080d0e011b0203120417011d031603051207030f1a0303090103050c070b1306050603072d0b030c0a3207050f03031303120b0a 63
    0x2520000d007403581000e9068055819441c0408501c07a0150003501e4280e0300359801d003240e40006486581449240300d0201d040b524004ca2072040d00324440742c80750300140a0b59400031450b14000f81a60164014403010940900c034422510002d00c16584d000324400340070703402c22002456055403030181c04031004100119040d09020103104000751182c044c0d0f044528105c0741800d160107409000750800000106241c03041c00040d01000c4d1070300644030200a80518a400c1c003110044000c3c0c00e0040108614080800140c0005003800103070912440c126542401649558501001640e0b005030055120f607100c4130047c0818865151041100d440900342200c1e800c0700c011046150211a50102e60104008000c005180300d1000050690100907540d0f4008112010102e0b4034410b020a550a03007601603c036207090540c0490002d0076514003c0c0120380f009c142d00c4d4600e91550f0700c01c1319600103c4859000e07850805401101102960303e46880038044040050045481c2002c1c07480390080e0f00709112803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 850207356 1250 850206106 850206139
    0x1614060f0f130204092a0f0b0904180f02130207120c030e0415150305010e01060c0c1503020a08061206040b06040f06030803100e0106020d0f110d08040b011403030306 73
    0x240c000c0c4440d40600244140540ea06044851742128a00440c2c60f52000c6c0400340c815100e00c5940e0150341c894011400754038100800c101954200d1a00303240c000d80e55813500c128501ca11485400340910030102107c4080e501c1c41407244074450400040b19503801489042d00007030510030030f805074813400e107030a0301c210b003060504561208050101c650400d2400d00c0c0d0000c000a49000c0d8030688035034202c2e0310181003584204600b214024421704000c6026600140409449042c012003041c0c0584898460f9030340302c4141066098811400a01090b4002021240e0b5a0480003007076100d03404641072078024401100e0300d0b4030380400070300040c0162102c4000032140d40d11070307210380041c82c03070300208200058591620b04c1c41035009031507542e550700e50140000740d20014014911306844041c0c3c050403500c5c4280d0340980d00088020112000e0140e050846003613031501b004001d02c100755503519400142031a0038004540b030300c1a0002c0c031840121228194480d1000030850340c0003c82540e80d460802c03040704 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 850208606 1250 850207356 850207381
    0x51f0507020a031e060b030d0816051b07050a050406030b0f0727090f0e1207080403140615032d0102120f0f07020d0f031d01021614060f0f 61
    0x10001801414020811301c00030001c600c1c2454043d114a20801602e100a400c044d80d400300c0c1c400003000155060002904540000f6420000742004d040c80b9007011540c09000c4034403401518424115400018100114a0403000101c024841170b40d0821441c1c4c215103c0340c0c42d855004141c0980c0009280201710294851388070f076040707000c03800662042038001c00004801d8100d0381c42a010341c0c0d030903c2100050100b0601c00c02d1042c10170100203060011850840e29410780040c034080d18036010a0200101295500112000c0056034201801603850010391440480c003540c00d4450180e442400340f8000031004d00c10827044208212000c010107455103079468064030a080b07109400d40c000c40140880c50030101e07901c0f070088200804000c107030b0352504402c0742d45900c020040000202c005000320307441802940b1030500021307080c0e071043c402d59001004600f6030b0300040c00c6902064688107988107010740e465400704d1915800c0041e20030350171706561112100401070241001400c0c4036021442c0980741d03d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 850209856 1250 850208606 850208609
    0x111b100315090204080102091314060d080d1406090a0e12091203040303200a08030109051305011e110306030d110a0c0e01032d120c140313051f0507020a 67
    0x2c4000d556841d110404603020b500010740481c000d505071001d03011032540300c1c014010199a840310740111642c0d020100300c2846800603058601c41301c1004040007040300b0713000c4d00c200d030a8500418420790906106000300c91000a240d1480a407520318030761420303440850340e45240b00c1c0480ca83c17502c0b1f4802d41c0c0011803e040c0d061040c00c861000107000010150803040070841844004846200c1020104c0c5481e11103080075070060150340204014050540a5800580c214501d00c003c1d2000070181d50b1168211680495030800c603a00100241d650f5070703018099140395002c142902030440c00d000300401da0f1041c52180020901c0103080901e0f007120010000350303210b6608444601c420325503a5540b8100f401c0b00303000a5500302d0640c0000041d0a643d000140c20b072406059130f00002a5031a21064404c1e006080250108958050301e500464514043e408489a030000510798803110364540d05c12001c0540d00c01c9000b41c039414503c51401c501d004509007459094104642d4402e264230008000a025 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 850211106 1250 850209856 850209869
    0x601020f0708100509030711011d120a050609010c14070602071709040b01210b06090d08120f01060903060f0b0618010305061c060b1f111b100315 64
    0x1003010000710b2460003d8096040c00601104100c9a10f035500d00c9070302ca200e00e81005d040e1200142030114154420059a03628401205004030481c5550000540c5040055003903425503215107110001e000e0207000d0560042c51100c000c000340c18001c0d03000380800018808407501c02750302189801c14800990102e51280d41c0c080ba18000441d182c070004460f41c1c11001089000c1c41c50a80010201c0d402042c03141c444121501c83c4144011741c0d41c15850181420101454000b02c040c0050006622000c441603c80e602c01c1d0882d0341c542d5402c0980d803001c0e120080c00441d09000d5200104143c90b000341100090b03a0b001140410310322050b40b803a0000d00607130003040b50403500010b51500b40910002258030038102c00d80c0d0600854130303040c00300800d94410600f42e44554100e09002c03000074030607900070382c0328107000342c242001d4004103603042d07803290045c0000d079003c5801c0d11003c0f141d13094144486407481036000781c0004030b02100e4020030f032240303221600001810b5407400b91760041c84602c1130b14002001c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 850212356 1250 850211106 850211113
    0xe0105251401140f0606120a18080307031d01060605030403180e040821090304150909020414240a050711100f093c090203010b132c0601020f 62
    0x8001c00f14502e981c003c45007007076101c03000004159079103801b078102c500880b114088401d0f207840354480c034001401180d0340c0c0e654261a640d03510002591550180d841421a520005032080040000614140480500c85103591401e0401d001541e00501070300e4005030180307408200450030030003000300400780340c015607406003c4c0800c010801a440b401000102031210701a45141894620032a00d50303c152000402d64109000c144004035100c0d0345a0810800ea140440a29954000490499006411146544a40100000c41801c1a01e6544000c1c018003001c54000000c90880c51003d000310704d00740c4208480040d9480512a0701038a2242e90903006103a014004110b10018100c811949044000b06a00850014042e50720a10902e01c40c00ea00e12491104201004c041410b45001d604002001c640900041100a614801f45020303005000006940f0100c08a40c60148441a40040e103600154803240554020111200100c650001d11007400c0d500c404006038204200004200114030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 850213606 1250 850212356 850212371
    0x10090504110f09040f0201050903100e010e010b100e01050f0d021b01061d011e0e040f05211206150a1d01090305070b0d1104060f0e0105251401 63
    0x24014081016040c011034290910b00b6007503080c800c10f00390458018081030a41c94000c000f650017480140780c441001026618230b03102c0d20040c4001c1701c000c0c04c44880070740c0d9070755000d81400703c09220f00f90b0b511008a41c100070354110800000e00240b840c51096040000210700d01d5401e000c1d01095602406460006540741c0322003140c8101822a90036145207990300381407000074583d03003d41080c00b840750729917020007007603084c03d8076070075280850700d058840310440010010f1020045260280600c4c42111b840a2644550070802e14109001200303155801c100e10845119521a00465084035001c0c1303010801950703004005401e2401a41400d0551480050840c0070650304c02c408040c0d070030402d880241c02e400c00c1c0d0b00454595a05000c01031907980140b109000480b0000c0c090b041e03141f40980302042e0801c00d0920036600e504594054000700342080c2e001140c00e500f080514130010802c0c41c101c4c0c103041101202c8480400d002091004007818940b480701449aa540075000c03200682c0002d10044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 850214856 1250 850213606 850213613
    0x7060203040b22060504020303040e1603060807050a030f02010e030304090f0e010504020904020904050109171b2803050d1802010206090604151a0909060910020c03040e10090504 78
    0x250320880701111800e560a0004550254014100d0402c2440d0000c100841c0c10f256070fa00024000078205992621091000048603c00c15003441c0c440c2c4002d2003103a99441c01d001c2c016040c0c400d50f400000e0150400c290512482c2c42d400c0301c10040700c2d002044045241200d00040e1000000c084603d0b800d030100103008200200030b90026803018100207020040820301203005800c84100b0b680096001e910000400d01510301a00b0305900203005a00000e401074241c2c0d54883e00003100c5603186039103000410303201c42c00001c1140d440c03402e90300324001c2c0c007480502c07458110803280109280c86105184074801c1c4107242c4039000343d071602c501d103990401c05151031154001401070240d40480c010301c075940c001002d4400114490303010319804440100800e624084c20300241540c24001c0c044042c0361840740c42140d848400340790150300700201401113401c201020904010801c049504601e00402c02d4128060000007101c0827100803045042c8075440f8441544002091a405420400d05042c188003d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 850216106 1250 850214856 850214861
    0x5011103070207060c021e060c0304032d020d03030e0304080105010909050106120c180f0c030506010906020705030601091104082b0e062a1e060714040b0d110706 71
    0x4450300e400721030350f03255076410441d000e059017940290003218010014100241e40e01400e6807501e00103044c20b0a1020220685240d80c1041d0720942d00314042c0b810fa0b1458034100c901e01610038051200381c241a00e455000700e04918003a81c0000c04042d81c6101c01c4e00958418410381c3c1c05801c0c01c80003403000b07503944c0800102401c9040c005032002c2d480d010001411050356030308617681940c4002c040090743d14000d28900e281002c0c0400d084c180d07840703e59200c100d1645104042c03142c1d01c00e0300d00040b1400c0031000140700300700c00c1c1c000c0007d40d03014160520555400203900c604441000300302041c080e5071000b000c1014041e60b4000066445040d41c01c4110208500c0545035030740c600c0518100c00800744104440d0b1441480185030400d0b01004421492150300c40034a292485d044000c03c0c0012003515138502c0c019a80000410440b03500c203c0d151a00c00a02903560401c2030341c03508032542941e418485105201e40d1040110038000051091080e0140b600003100a900b05501c55899090340c0c10141c02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 850217356 1250 850216106 850216111
    0xa0203060709050a1e0906090923030906070203010902031501080d051912060b0310050a09050f010611150430121a0303131e06020c06070f05011103 65
    0x82409090005141e95201c0c00c04041125401080749000600e001e0b003400408090134907180c2c2e0728560346808038400107070380661001004040300004120301242040d184c9600021000704c900245102c14802d4000004180c4542c1d140850f603003aa2a021840080d0052400240081d0940988800b55a1180c80c2c40c00c40c41c101e0340700005540c0403400c0c1c541e0494452007601d86510391503400fa12134081191068444070090f413a988400210580c46040100e6a0b070411600080054030b40c1e0b105114a08004500000800c2c2c021000d01ca01d08140202ca40103000501816082055424500f40154420490701041346a80c00306034001d0706040c20185064003c940c00941da80c4024004102d240c0c0c6c6001c90054080740f10742d0ba021800030400c002002420078020014240c4128902c8030301c540d50140010880841003039110420103241203464030703d11644000f401880f0100404c10800c482c0c000c90002d20104040361000e03550300c0036180c6604c2c19812000b01030200d44c6030031003403980200e01400960 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 850218606 1250 850217356 850217359
    0x102160303140901050f04172b0606020c0f151204060b01030506030f070b03070302090a0f031a0c190c12080f010f06140c0a1703060906040501080318040b040e0a02 72
    0x4240e036583c1041c250a036001954000040200c050000b00071400c010382c00102c800304883c01e54a04042c1180d00343c0101e80241c40c00340700c4104119040c9001d8413601c0f4030320040505001601051084600289420038820342e914010403850902400b4280c415080f2120001c3c416083c4910741040d0030290000c0c00b80d0b448003400b0034a4040841c47c0f500d00011055841c116901c010884642488220444c1c0e41000d800c402c1410f400f40720b050440e503608c0d0300f00005030032001f40d940e00c030514506040161a40d046a9824411125400d2011080d0500b0031500c0815400e4080e2040001c4c000c001c6440c507612800140c0b07400c403640b11b08100d0aa010003030324050314980c104840566211100c1c52040a010310590020031300e00480c400d600018107010b04910220502075504840f000d80b07414012951a0304940d044080c00801c12119180046513290400c3c030a490401203136042c0000541e81e445007801840780c403c0501040c099690391600481d40586002d4010b0003000c0364045004ea0304d50590000301d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 850219856 1250 850218606 850218641
    0xa15090b0a030203030a030213240f1b0803040510050c160206071a04060c031802010e060d0608030c070605130603050a0b22050c0702090601110139030b060301170102160303 76
    0xb03140d6980724ac0d04076038440d44c011f92042d00482d1080c10740d08a0126030240b014000501c1e4201c40724055000400801802121060341e0ba00c0d040c078001d4180507031840d400c085a85070400340000c5515040c15035801e44181c681c841200742e01400000c1c0140a181c80080c90708080214112415485500346070144d84558820311400032030f04010b0341515001c40401c2c0e44035261072003201c055071045a1031008000080c242e107103481610403501b0250f4045811142103a07100091f06c40c8034040070400140100b13141e20b042802c01401c0903609503a4003841c82079004160701e5030301203203d47c500c81d407040120301c50050819141721410840003c10b81e00000c0c200310546e14101c00904541c440304100c88280f5801403408e6072558860700150b80801d070040740042e10f5036075040700150492820400b007a5042841a0b442c0885c0014044160183c00582e608010103050608203140d64031544240e9040d11500800441054000c040150083c0510200619403418446214040c1500351384001914a03021460b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 850221106 1250 850219856 850219859
    0xf060f020a020108280f0e070f0806070e0102012405011d030a020d0302120412020f0d0b01090b010c021504170f06070804020a0320090a15090b0a030203030a030213 72
    0x2607071a0200d21102902244410340060040c19825454102d41c40f0410800703504502001c1d0581c04650144914180f2684c0d07038410507102c080c00b0401000200810391a07614541d00f881340300e5440721405800001070001c00070790060268001c0d00004454080d040e003809452142c0000d00f003a0543c03500c00c80d03012907540082030a01d20305500c915070300b401000e0000c08106040d80c1c24441885401441541180140d0a2101c00540d950f40200001c016002e021041a9030034010028035502d02d204561041003e000c060340050f04407105d07641102d104403000201c0d0709801c40182c601d203030115402540070041030031101000e40400051700541d905480c00749002e400c5082c4030b41c0d84004202900280b5400080001d5200d4412521103510601c081c10040703000d40c3daa41c5080e0103088800e0190841400c902c58008581420a4a42d51040c42090148010352406030700300c4001c0340c18000e40813103e4880e000d0340080c0e00d40346d8006004690250032039503034201c541401402900219502d041c00e441d103000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 850222356 1250 850221106 850221137
    0xa090b10082104051309111e010305061315080f01110d020a03110d02120903042106111303050f0604080a2d0e01020c03010c0503060121060f06 63
    0x2440016992080014010141ea0544042c0d0303040a0707030625540800c00300b02c04501ca40341c0c4107020303102ca192014081956903882c40c0400000150a98840c040c100346607091080040707080d4410009402800c0004150f129903010a01000c6030502000d01d0a04240620b51a510009003040413503610718280c0d07100c0000b048429007610794000200c4041d1005100c10340582100d40d00402c80e204042c00e000030518403941c60001160086130705002c001e54007052584168403083d4417030ba1b01c9241e580c0035502d081d040003540c0c1c4c55400c400000c500f000780c0811013501000044e5100c1c84900240c00c184646480d82442180e80c1c002150004a5080c040e0780b00c0311700724140000d4981d004583c003c0c2190f0a00c1c0c8800303c11034000010980c08827042c0182003091303300b030700208180d11403403403142d03500001d10150100180c83e011070059024000da00d04040d850701e050348442a241c21032803d2030009106503c0e4076007401e8003013044100d241040e28203000001d207900038554070411030300146c8418024062002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 850223606 1250 850222356 850222381
    0x60e120a081f0308160c0312030f060503030301090c02032503110a0b06010e0f09091006120b071b1707030f05090d060f02070f060e07050916081e0a090b 67
    0xa07440c41034900782c074070a100040340e58018003010f01c000303514410220955114000030413a5640240c07816211000d440103070680c54061030704642e402410510101d403410000c607980b480148619401603a6030860030715620702c00c2c021214107440c0034015601c446401031181541c2c0041d410210085442c10501c000e2584000c01d9024000e5048650440c0c40d41d04d02005442c8031400601c5140c4c0040c40c103510000c01d40e14180c0c01c601503030048004068102100030090125a11500070020380c00c0c15254510000d56000e2078594010f266182c100801903000c0050207242d41c08110042c104000310154902c2445c48030040d03c555401780d42c1c0d956483c030034048241c0b464421000f01c1a0084042a014000f082d5a0307000001c08070340400d001071800074680c8031100c80241d8800b04032811611000740c440c82c924100b0031180507007002c65004400307040c04001c0080c44440118490103100700c00c0001180310b03800c0c800031440174035104580c511610f40b501018004010300789044903003c403114040f900c0c964846 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 850224856 1250 850223606 850223641
    0x50606010908190303052805060f0406030c0909080708180405060a060e0f22150e1e0603030d020301120b070e030d05070c090e3304020607060e120a08 66
    0x101c00f0682040700a840c02c9003d008020044080703000c5030002d480f1280414008080da1801d0b04200250394248042008145240c542c0c3c4944100d040200510110321601d103404104c58540d000010542c06914202295018107000580a07002c08510450001011003990500d800100e60800880da2076a0420400c0c2d401c40c0140e9002412048000c0018202040d51240d00c0070010f0483c41d8501c40c404076540c1c0303442d000b0340700900f09440d8003d91203040d4891503d40b003e80918054011a45484c1c82c60760b1311100c02004403d468008240454460b403018030071151004100d1100795503070341e1100d250b501a0300d500d04045031140216070000d81030a01c20090801c0b0b558008014160400c0800300442c0e590700030030002d44500046800c005844403440c03003a080d60505400190140038100e2000d411072400f640660b0b0141c18402e807a14920081c1208103d911a0341103440d281c641900c0d0800c480180320900c04400a441003215071068440035a015003500502940c610300c41d6954940741200e1507041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 850226106 1250 850224856 850224883
    0x807030e042007020d0203250510021908162907020304050105070c09060f0807350c0414061203281430040309050402030705070c03050606010908 64
    0x15610b007001d818400800800c1118001050711170101c10f80d8001a082101c0d40742c40208810302c003000b280a1000407070b20322000b07040071506000200280d1102a440f20141d440e0340a000704030940c5141001003075002d8501520050183e84845c00b0503141007024400e030151f40078200040300000c2d810b4005800c51592055210f940a50704107440c21006403601c1d00140c170101d5810f017030000081080c103140e1141c000140400192240741c40d2070002e03c2d9040104a8201200440d10143d0103d96040b503a403026005104120369800d00c0d100f00040301d400e111030741d1030170b66200307082c800e4a4400c40d442d541e80c07501410080b03a00c015540606a5041d81e07a02c6400c05d9040b00600c06102c4102c241516107001d55801540c0c24000e40c0c0801890341030040f50b1020342d2200d4482844508400e0b82c4100303080d282001501c80e5001001418103450142c2100540d10916201d07031340000001c0c403044d12400076604010340c80f20303a0a26284c3c50b403400d944c94501c00c450f014001402e0344000182c0100000344038001c40e01c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 850227356 1250 850226106 850226141
    0x60709141503070309150207060c020d090e0a02070b0a0e120406080109180210020d09170c041d1902040e010b01050d0905031209031e04050105040603050a180807030e04 74
    0x1c8884001c0342070340000b003601007455900c1c0816008a880c0ca040c0762001d02d0465001070f968440c03843d041049074407014070302c1d08562050100c0c19030070350408698015942d080c481003100d50741d00115007020344143c5800a00014088042c8140414590002c2951034001c0050711813288a8012221403401944541000911143e00400c4030b141507038072100b0074800319456100f50141c145c01060940a510038958010703440502c501e448035074000403c2028020580881140e2a45482c000e951a010205511700c541d5072801c480252030459220b060050500400b5180c0041d00ba1032002c990700001141640982d00b440030100ba00b4ac1d042c0f00e42600c901c8161500c1e03080901001c2844018111840200c40302d11013080841803c003402c41c07000c0d100e103844500550342c0c0d03c1d4a084819000b14410000105180103000038004c40c0e030010240c4041d40c820f86000141661069001006044542d01c503124080000480344144288000188401c0c1e00984a050f550902441484115900302910014008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 850228606 1250 850227356 850227379
    0x12030c0919150503010611061905091c120e161802090a0906080f070513150b03010305010e15041203090503090a141c02091b0f04030506070914 63
    0x689844081103005840c82032030012902c03242101c0903151102c07000d501040012004000f202d074044200305402c0321100c041c00340c5040c003184074403681d5000100b0908490b01d81340050302101c1c1c1007180340610b601c018403456034207140e040060100030201e881c5c861f00b80d050900200340c502c800100040c01180704045111032034030b042c070282c070380c0e03071405213104c6216408200303500346076803000780c0300c00540411040029642d00d445082460070500814640094201c90820003076590303000b8602c4480c5081e13aa010a81e01d07a507901030210010950070800c00214080004020f01c04150302c2150022118412a016240108403880344480b0445004080700050046082c40740d2080d04482e0926228108880c104101000020b240401c03a40000060365849000105246070134040103885100c640c44c09841c2c0328041e0081542600004c00583c0840c400d05e407060900c09211041b51480c020020020340c5440d2a4981161200c100752209000290100400f1502c50b0310181041e41c0c1d000d000385801c0010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 850229856 1250 850228606 850228609
    0x5060403080c0708030c0901090e091506040b030a0503130e010f060f090b0a0309051908041a0c1e070b36030a03020303040615120308040203010b0d0b070212030c09 72
    0x7000100411401d82040c4001d00004442002440c05903114a210075102d580150006007100184d48c4030b44416200413007031008162010801d180302c0315040d96a00700c1595070501143c0540101460705400d4494807072580d040c404040042d04d6580341400081c8034190b43c400c4028a9110207006040c0c0348070701e00d9001c012941c00343c505134040c9403540c109103401e2030740d490f1242c05c10303001222184080b0340c0781c0b5040b004106050203820006c054a080341c0386001c1c0e16451712021401580511100803d140e140c84950080d140180d5180421078411101c2d090f09444030020b040c6651030b81c071650342c4900d49001c5541c600410980c0c2c0e400310b91a00441c54421499100c00c020002c281820780c1c1e03801c1101c0d46a4058405101c030442c121300075001140d503802c003031500104440320384003080351001c03001100303106c1c0329000240000c0130f035018a0b01e00103d4403607000181c01071943c1c8007881c0d03115082d203c20200700905a01c00c0d6110700400d80907503d40c15242e841e0282c0510084a580000540401084226 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 850231106 1250 850229856 850229867
    0x102030a030b0f0405010303020303070f05161b360908090f0f150403030e03010e0c09041a040b01090506041b0c030203130e0f0c0405060a032d0618050405060403 71
    0x4642c024001d0000d1484000481c003210802c0e0015001a00b002040203a240e0308610400c94810f114904a4944018005202143c01c82828000c2c0025501000c89028a8440da90311002d49200c04585115810501164403801c485a035030301d07002140b039180390480c954188280c030321594000034544d141120040400680c1e40e10b003082954401d5032402c1008998884812908d800d0440c010181c4d0307103900790308026118829a00c0e9040c800e80c18280107090314400450403021003c8103544804d155155031401c016041180001011005e01100400007480301181100e81240c80b04030040001d5101c100074003060707840031a8a290074855903808100d00910446540c102d00b40a032048c0e034100f0495101010500c030155102a0403034001c0001c3c01070f56440d0088198000c09540026442c2526000c00b007203031801146448810b059407903090707031660704071520030202a81d908401104000d0026040340e000b000140119081003403000f8009954200034820749010b0380c0c201c0000d041561702c641d01141d8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 850232356 1250 850231106 850231121
    0xc02090a020d06090c0225060507140115060f050310140a05040e01050a15030308040303020f0d09060603050106050103020c070b0a170f1e0115030c051605150a0b0102030a03 76
    0x90241c0e0801840d21040200d21425000e090103120100b80e259141c3c0c0004d2030404c030302c0d0712621082551640c04038139803004201c8008640c0c19050064882c09035003040103c00b080e5841a000c2c1c1e50a241000d02004044140c000503135540d52100c0f1200b444130201140c060000f25a02c005119048200380300b081e2110100d564040d070010100740100e80c4500114043d919180d003400f00c9a91500c051158103082801500c1c0320741400e00c02550483c0c0ba60314000c12101014002805055002417114180c1407280c003280c4000d150510300707104a8403203140580040c003003480700780d41c5546440e0002c555980709000b04d54261301090010113145040c8107120940e54408681072051000e0340000c40c4100850400c0c603481010000080c441d1031604241d00060107900f1b00701d4002035424030380144481b041840402c0c154254078680040c2048020006840e80c2c0f00d804214404240405840710400c41d0008010700550000201e4003590b4a48039204800d07034507403148031800740c1c1060018a6100f446580441c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 850233606 1250 850232356 850232371
    0xa020111010209040c0507060b030606010f1101091a070806310b041104080c10050a2318150c120703140a030209011704170705010212090a051203070c0209 68
    0x5143c458440c000800303d0305c1d011054000b203503000c02c01c00c06124040c4556040020141c028080714503104000a0410786440e00c01d00c1032003101040710742e0b0018254804010035510000c1c0340d00d4281680d8240c10060b13405c48a000005c0c100b400040d4003800c0042d0311080702d540d800b1544c210040c802494060b04080c0407150a080c2da03841825041036516405004c0e54801d0182e0f106030f4942c10640721038180300318041d9541c01040c5405e103008525500c0421a00c0d0301d6410301c0c004941003c0c2e814103d4104030001e0310840070043c00300d0150355140d031170a54403421480480780304c079826808840c4440140614a0a00040c0d00402140400342d1032800090240a2007480e00f40c0743c0300e222005251250708000c402d0710009a01165054465030003151902071300426107001c0503240383c69035559169408541c030b0840040b8010803841c1c04c10209405542c504100700c0d98a000501d048071065640303564000c3c0540f501d1140000c0c6045021703200003103030301628141d40d440c8080d050903020702000390360240250 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 850234856 1250 850233606 850233611
    0xf08190b03060403050715110d050612010c110d02191410110a030c03140115050705100507020c01081b0313060e060106030608010c1b0320030301150503090a02011101 73
    0x31065034103109071071055200380c4640b034441d00142008455a02c1030301c425405e43e450706001180c80140c0d541580c030307a607031010030201e01c503a202c60209004400072102c5080301d40c240010440300c0c6030010713022141980382c00203c1d04070b50003529049a81e0b420380a810204042121115808940744044d048144081081100c5082807240b120310120740510000380f41c00e0744040341c080c82480d414080c9030b44a40b10361809000c09030500c0030400c4405018031405606030b031840d5003105414040c40a850071a900b15050350384821003242d02c0000352804a0b401d60050085943c41c483c2076025441c8140103103440e000c04142c00d02d03d484000c01c1c0b41d00140441a8030896140c8203400030f1040c0c02a008010030b48005403989500d0316030050240c852a4005080d01d90520034001c00282c4d00902240081000c4112030060002034101a10f4403a4030700e03040c00c55454004030820fa0030384000015812202001405c01441084880881d039900050700c6009064229500d61000343d032041d0503040c40b998090000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 850236106 1250 850234856 850234871
    0x2606030d02240612060106030213050d021c02030c0a0b1206060703050304260d150b21041127090307021c02300c0f090705030c0c060112120f0819 64
    0x405d14140c005d81c0801c001a400181c140003900380c0504850092605079a002080038017940050070950040500001c017030741c0041e0810665500b08100000540080e249940c0e1540f502461081603000000703401031501c4e003902044684c00e0240803a02d0341c2c3d0b01036480f0385c00c503210350782c1e0f0040301740410004080e01c0c907140000440d0141190024554141c00703640020300b80000181080680b101070340036210012040c0b000907411258400401c0a6103001106001e459403189070100343d0501c03900000350041003800084400c1e10f8078103c00361149042045000b5155180741c00250741e8496034500075045403088641c0c0d03481000c0800750811035407000701421600040c071100000603803074405100103a0801d000b03081c55200000d2001c442015010342d400b00c40e800c2d038000414a202c00140600e4100980080002c401d0200f01040e04c9959075000203941480d40d480240c050011241401920f91185403404016a035018004404a400c41c40d109d494143c2e071203030404c0b0501d560070101c50240980343c025 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 850237356 1250 850236106 850236139
    0x303251416030f020a0203062707080102070c120206091c0f030e0a0e010803040e131205040306051e0c03090727140c09040c2606030d022406 62
    0x2809a4007003994525440075420308008080005006a1105540100d0f8420f005a240416030b1070744140d20000301486403d10061254401c00c1450b41203e0703500442202083c5080c040d00148082d90040308200300450300c0b51040241c02e4400e1200a5000c04200850505030505200c40364928040d460366010030381d880d440b2081a07005c461400ca0000340c480c58000428030b0080c1c00351001d44582d0052220a41c180010207640703201d180204e0000c844400005036101da8803625610304541d00c450888203000c4c90940140468209000859103d400e04000845956400c1100c0c0c40d0603901203240030582e11107211403070855101819091a80c0514580440c6030000214006076501d2480010031000600c40b100300300b01c4280c98101010801820305100c240080d840a8480300102110001041c0340b40040035128507203c00c0642451150300551040c041c1603414000b0b00c40e41094094a510146000d42262074103e40c400000445000c004008481062010b28950104024000c400c41c2c401821 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 850238606 1250 850237356 850237397
    0x3080c040905180d0c0c030209041e0305090916020339030903010f050609070f030f0509100b03070506070b10090203010e0a0c0201060317030a1b02100e030325 70
    0x4600510343e5104803810000f501d810011409001d2152070540c90b22812540c0300c08400d0b11754800a4401c0c11518082014456a0b6001c141809000c2107640b0501d5000d1030080c1c4070ba00522006441a01082d0000728002030001180a210140fa4082e40c501803007001040751404409940440c05543d0503002100254040b40702590340310303250021519481743e001054251152500468825400e203014006a519002c003440d800c4052800d14030300b50440c2c0d4401702c005240716503080756640d003030405000c400d10011a5041000c841c200041c40031900100c10315940301694485c16400c140d040101001150b1490103254215031500c1c840440c03142d84030b00d00e0050780c00a0300310051410031b81c0305000d9440c0c524030a000861109000902a480c03075900d541c51050201c02d5050034a500000020b81c0260140e4025550aa0411001e807030b1008103082c000c0d6901941030950001c20306d42941c45d940c240340001940d2040084030b039881d408800754403c0300044209442c00d007042c000182001c4400c0b400c136a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 850239856 1250 850238606 850238611
    0xb12040b091c031410050319051009030807110d1b03030b10020d11061308220b04090e0715030b03030d1e0506040b1509180408190207060c03080c040905 67
    0x96901003400030b138039004614414409446071001041000041060b03803000700300095400fa04552000c902e034181d0030841c0c02d20008140003c00203180c405184d080642202000d4000c0400d030b0780b060103030311040c002c450b901c11140b820000450145151100c1c0ca1030048105003800c0d200c0e2802140000d41781000c100e60884001e00500560003440c030700c0001c580d000f540c803c0540a003000a0945080803401101040807005019104100c0003c480301307611a0b2444520045000b5280ca40c16240d480038400030030b80050054800e541d003000035840400c3c030000b40c40c80c1524071211b04c280b412181c218003503000b442c1040751190140000d0004880040303c92040c8100504942070b58400c03503d03078010b03403002c5407002001d1a216600e00103580e011503d0b13005207240c066200040e00b07a502c1d01c041c400540c00907010310041224800a004000c10072450790701610071801c0001e03800c80002d454034030a0741c5a4085016400004480700c1d041e90101c3d218a82030b03030300007580140d150b03d4117484002d00ca040d0b6404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 850241106 1250 850239856 850239913
    0x905120f0f0f16030f060902220501030314091e01170c0d0b0d11090c2a100612060c031805030909090c15030a0e03070f0c0b12040b09 59
    0x160b00d8460404818010b1140586580ea1041146411544c400d8070300c01c000e401c05003030f00e5560f103c00d0045444e0281560407104528560808070f1a401c5040c2002c0c20007400100d00140391498844500e40f040c0301a82d00801c0020034032005000194800e101803516000c07440e040019180e500b0805101c0c07021603e00a20f01a00c010359100503240f041c2080c2c40340c0420490140ca260900e0750041102071003c2014441c08550462081c1c4508071a40814000c08021840000c4802d01840c4400c0802c1040300c100284282521010400b54138004200c603010702c41d5280301c5a640086000248003a4043c181c9441d090800103540f051107000c1e005040f484203000c858507400002c90b09124070700b40750866071180054005116210051000ca0845480e00c1a004003081001c0007082e040a4541c2005502c025100308a90316400e081c02e140080801250080c0c40c0701d240b0080215882900c80211461055910f0742c80600d502c443e540c05010b130748014814030880c004c80403860491042c0c510f000d41c18115 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 850242356 1250 850241106 850241113
    0x712092601021b0a0b1317030703060e01080a031101060305060720060c030103062a0e0a091112010803042103020f250503012a0504090513061b0905120f0f 68
    0x311441e00b0b615101c07015102d08200c1c9001070040001401c4500207c4020b01c401c1100d50300c0307868642c2c0641c0078102c01d070415268031180c0c6001181c0034000240805109001390b0704c030080340c0280f9801c10300300d40c81c1d800081e141c2c1e0840b400007504035009200d40204158007a518402051040d4042c1d410720700706031424140108008010420300c0400d0003401c61003100c4014180c009480ca130400003204241890900901400018a40c1155151820100107041d00c0c80f0912803000c3c5101100115407000b030046e008801c20600105040500009803802d4400c00b0410b040c003825072156205460039440307404c8007144202c1180b915144018400c411404000c0c10003102000d140d0701e00342801d6101900028000da240800501078562015111030110441002a040b0802556811902441550041d200103803c06042c0990109030610040ca034900682d007c01080321000365039042c52000c003102000007500c50f0401e1065181080548408081100850340c7c5502c408103e1402c0158106e01042c1540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 850243606 1250 850242356 850242373
    0x62d071a07020c180a0908030f0402010f1e051b0102190f020a0201080c03090c030f0c03070b0a0c140304051e1c05070b0f041a0712092601021b 63
    0xc4403818460308045140050803e01c514078010a000060344241c5500300e029840c0031554610b0310303500400200d50080c54181d46e03880c144d4403480140e40d040d10124001a11612002d54903486031018000000c0c004240b000e44c01c02d5840200d03110742020400200a04000036249210842403009006440340c00440c2c0701b401c1e0710380c00007510323400110340c0490a40d0080c660005c0140e0380010b1150f407007004110341b1500c0e51500741215181880c0142c4468040c4504038a1102c40c0d080042c0e6488920011401c5a00f500c2d1124405100d1b4058034510744003060340c4900c04000034681c03961500b00008007004a1741415528130005618542c1140d0a18800310310040480844c05e140c00c0c4030340155440b5002180800c2c00e0754860360b44070803a11400c4a0b400340850701c0c02c00c2c40d88040890f0001c0a80c61440b8040380100041c1c21a2540001e504903507214584070035202c0540654501e800311441c5100d401c17108150303104202d84400214124040c0c5560030440c801900364000c4e907001c00714044030300820900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 850244856 1250 850243606 850243643
    0x1e1e0e041e0f0c08010516030e011d0304030b0a0b06301311040204030803160306030503040605030114012f0c060310030309090209030a060c120c020d020106090b062d07 74
    0x8543d9130858645a41081c040141100f0340b401f0b003039034488581c40d00007040320444c078900c2c0c01001b603000415542e07021404505409000040a8000d83c1c2c00b4200d00d00d0b0b541c071aa0341c2e823000c5442030200f452b00803400780710007100f04e00444403c820415550a4440034140c5003004811103034002c41e00000419841030b00c010030b000480c0d0b10400c0c404801d580440c41c00d411074450300d102d0b00000303101c40c3c19024503140c150310700d51198009400546d849402c59848036107400000d04035400c24000c071032146030b010305000300c658441c102c07031380d0708000189800c2070201245004030319400303483d03030800168811051070090070b4031940b0055201d03003000040c0c0c44169055290007450248150301c40c8840a0040c000d8000030303603010906100d110750118000641800d144030580700c0076a04a81d03418450300e81f8000300b68468010440704004201e80c0e008004140d00c5840030300c00c90b82d4410259400500a10140704512088001009050103e02c60020a864288201e45890380042d07400c40c0e80554002c0601000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 850246106 1250 850244856 850244873
    0x50a1b23061e01030f14030f0316030f09030807030f0617010614011701120609051009060c1830111c052a0a1e1e0e041e0f 54
    0x811268080d00c074603d5256454101d490b0100440c06007091829455003204100100100c2d503040c500d40c40603e440307250690001c1130100d017000d2002d000ca41000d00780040c1c0242841403c200541c15183c940b41500c0e000c108400900e842c029000c034180d500c240102d510407004010003514031000001160302e40c2032444899031982240d003880d041c40b01c120f19910b0b500000a00d058152142000218280511820140090f0aa000340a001401521135051142c0c00c250000001035004c1c1c40c0c01d00c400f011202d41126034003c46200031100191402c004d1000480183e22410540f024051003a1030b544070064072001052100b800310303041c1c8030741c0046d1100c03401c040c4000b165030424020003040711003032034840303685620b0605030b503060300b14060f1009540500901512150368401800000b00c40c0d894040c468520105807540c2d27001d0f5000031000207200d038202052110f500616404c244181e52400c0c030605035007980900308032078031105000c0c180480c01c0070000b218091800390176504000221820316456 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 850247356 1250 850246106 850246141
    0x1050c0109050a1506120305160206120402030c1203090d0606050307060c1703010b090103020a121109092203110319050a18050a1a0d06060c02010f050a1b2306 70
    0xc050800350200100c05c1c6c4404c0d0044202e0309400d015a0300c161441400c20620802c8a000f5800100890000e0310109140c000381c1c49a8826000c0380c4030341c240c0c1001c00242e03040c42120301038298420400e00d070040c20a003c080c581180301d0344000c1000e0340c48400280c100090340e0481c00000395000c3d0064103122000b5400140c000c0b140942c546154149110306d0390610410b01120306041d00002c003910b4440c8a070782911130030b8201c241c0400c4044d02254262403c1e074000d84d4080e1080c808503000c41c003100e000310841440c042440d2040034040007541d400743c07109217007494200040e000512141010408100251805404641c1c07465916880c6080142000d00e10461b034020290301d1030300910051701c400a454080d40c2c00e8444d0151001a10401c1d804148580300410340365500b42507001541c90707040084004180d101b6240c0380c0c8201c103003490440b03160091900940024900c0b0819240b452040c074052490940240803407511114014265034040c403080c1da03403242031ba110004118400405514042 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 850248606 1250 850247356 850247393
    0x9060e01230108210d0c09060e09191107063803101503020a030606050418050303070c080904020a1d220e0c120a110409021e01050c0109050a 62
    0x1445504003804190350b01524007210100404615002504145044c1510400a8107403410f0201118120006101078018880c150205041e2484010140341000c0050f12451000c030170303084000400b00b08240580310002031040d5811082020070046501c034066144226604d503d910000304865032070843c00e85000e00003c0800741d6030564502d075640c022640e0103117007001100c042111541010f0904440d001503100951107c1c440d1800010410142c02c01c200f00d60003206c2c02c1013480f000300141c4000740d14841004146410401c0042d0300b650040d800c032240306004403840d13824041c926000c14204e034418042d49002c81d216a0382c0662100081c00380409030081500d030000d218a003410b00c3e400214510341b90b03803034241d06c4031480034102c1c00030050f0b0242190b00901a1921200605d40d042e100c4d0280b00301a606806014103001c55414207004480e4001d034084c1261410481c0048045492200b81549a040110400c06000c03111401d0085c0240c1c2ca0142c0c0c00b425100301a13103031200b8002101c24814 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 850249856 1250 850248606 850248671
    0xb0a18090c0e1e10120501050417071a040c03150f05090f032a01022a0c010801050418050609070801051503060403050a020a06050a020c010f11090d050109060e01 71
    0x403030f80b2501030054500c01d000d6110b201c00305840f00f480107043c00c50707070742c225100b00141588140203100054110394040c0c0d01410301941000c4503a0007001c400d1084074030181c5084450100c0111120500009640c001e015600c0d121032941c80eaa03408400c0d01c8039040d480d954603120314046903400518403c003904010420010000109040c815907103e005103000801902c00e000f83c1d840300d00e52851b80e403a043d00d040800031559900b0320400644018400b01c0d900b4849003188100c200100f50025004090900584500c2d48903887c0100b00406402c5800b09058070b158080421070000d042000103502480c680f1014207803013401c041a00342102c200800c0090782c1c940c0701c4411182c039140480d005420074bc1502d040da03502c03a2518400e034907000d0310101c0180fa5620349400c103d01150141e01601c220310580c4002c0c007080c40c1e040015015204030054690980e0380400c0480300300d01d0500002c900d030600c594008560003805840b200c0031100c0d00a030303102059440d446e600850740c03035020070203800790f8444050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 850251106 1250 850249856 850249861
    0x12320606041514010e040c020d11030a0507110409020307062303150105030c070b0a06210c0e060f03012c060118090f0b150406270b0a18090c0e 63
    0x3042c18089061203070580500026296224070f91280c0c88003d0501000b0b80300340961503480310001c0d6280c0b100b191060024034a80035103400b510000c0200c2b400300103690b0320503080840700e13143d240c036481410000c641e21541c2c4140c42030068400f4003401000302020707200c0d14a03054254140142c0000440c0413420780840c01c000b00900010040088165030900f8030b000c0b0340b269102043c481e1180704d080d601900480502d0208a49080c46400507801d8810a4103d02040001800101b05254417007100400f031105081003804403a00f80034110b540480014140c0304181c2c0c5101c0424216202c2e411418603400700c400158401b41caa002540d50340d0350280c001400c85615086098401d80005980d0b1907010f0f0303d41e11000d0620059052120110f07402219240880c20104504107003070800080550207036007080d000094604400e14665441e0060002065003d0303045541c00005040614210303501401d0680701041e141c221441054141d40040c06c00a1074403800c3c2000b10040802e0f41c012520348400c0400c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 850252356 1250 850251106 850251131
    0xc07031d120a05070f0f1d04020109051f020d030e0a0b15060d020d060f0b16031e050d0506030c1e0316080307031704080405010315080607020102311232060604 70
    0x5c02d105040d01d0b1f50381504050316584012500c8210940c4100d130700c2000b4100800398600130342002c00445905030210354450700160800d5041e0f4464540102068100070b43c5200070400c40180702d0307840001030703039411121980b600000340950040d00c0d00c0100380d5030214101c0b0401c200c511030766001d49542070f02d5201c10707460641c0140e92031280408503003401100303000d031070300701401417621031030500380303a040d0f000e015840c0b160040403904403600d1040d00c1400c090110745142000700f1240e0700c0f1000980003c138070000041c80c101c011a42e06401941600c0784080b0440e9103100f2401a6010b4285240a144cbc0c030700c21401c000b8001c0c0350100108114009280500c0001220070301201d00700ea500382030120744039000c02d040c000c244a01c0e81c85080300d4000c4d101040546941035004140c0c1245c8942420b0080b50000454854092103449118070450044401d000c14004048000501031080030000d50070f03a4000e40c19079a00045440410591101d9a602d4680d80390501696501440544041120f84401032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 850253606 1250 850252356 850252379
    0x40806060d08071b1208091c110114070605150102060a0c0806090901181214040506090108250224071d01111506090c07031d120a05070f0f 61
    0x21402040000050703521010f5041d981c000030020a102a03415020014600f01b03104540c0c8140d001c07520650034400d03030f6512407400c0d0f564144040e40107510001c8410354000151840c2e030504505001a410034000180051058081c492060040b5400401d400809800192809401030400d481c010304101842c0d104a5001401603441303481225003180b940c4500300c003a401060103250801000700500600e0081c0000042071806c0b11102e82d0300c851100704040544a1940607a00032168806010809108550311910555400c042003004290211072615000400211031640d2103016801c09006a180000030004c8400c070114a1101e5403c68030f80b0580052000e003200d1544022504841c0b40305d841e90b44140803084070f90462808460020507183c940b0815402c04035003482c420b140780c1c0e0016002d0500c40058842282c0c2c191189466400c000c00310807080341c3c803990115001020000c0003401a078040040004031070142002d014401d0400c80400040c0b0001d41200200404041c42000f200001c5d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 850254856 1250 850253606 850253617
    0x25180c110a11190801140906091603080d060e0403030b01120c21021902010f0e0d0203162108070305010608060a0e0c0903071e05010806011209150c0302040806060d08 73
    0x11522198108228460389810f5002074201584541c42c01c1d200403072644001e098a40500d0410b001c582e842e40e1042c69580e42c6290b0803050540b44400701c1c8007000011004009011464502c0740040340303481d246e030300c01e00003000c1c110b6050f000640c8440340110325507004540303c9080c1050300014403032405400c03400752960300d94101c0c000300d2890b54910b92030341e10040e80c181d441242d0080081c1c9166811207a000340a080c2ca190b12500e128940702c008101408001642c01210a4603000f850a00d1000081c500405600c0c00d07091711100302c480114104614480480c40b1099116103a080b41401c00030801012a641600910180103070482030106a9032070300d11b1030007120005900d000c440e5403074011144941c05000341e00e0350988900c40d0041100c110050030380d0712005010040000c210707640c40044403a10020385415012a4000318040e10342100e0750450340700c6a010709086801c10801c00b100310112215558480d0001c3d5002c5030034001c2c17440030b000c041d820400445805c4442d03c140e4482c0c420034400d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 850256106 1250 850254856 850254859
    0xc0302130b030402040b03031b061303021c02070f030f060f05010b1e13030c0501020f1b060a031b110d050408150618010312030b010201090525180c110a11 68
    0x2c0300003011550389400440101c500502540e4480c11046407240c0b003961a0241400c184c09408006004202001d00d41c44240c1d4240c0d004200b140d03a0044903111203100c000c040720850141401c0418100d000b0700e559001540314050240740748586040100407034160f50854010142000e004100c007645480661f001e10247d901800307100e11100801d041c1c0e82c81100348000038050b542d07a000003070000383c1c00d420007110001e80a4907000b4034281841c41c0c8500e0680740d8070308410380d440d003080c6950070400c01610420f561418000b41058841980340081200d600350200051a11650b541d1400380500881031a85c049051a504250900d4071b4141c54204085018015000900000e0910b030360f541300c440084803006a07000c0e01540c4904064004415103d070702000300c0c1c10017181444c1ea520510440900d5900200a8070020030150451042c4442091007250b8043c9191030120f04912440341c0309141415038080024500d044010250115019001c01c24940d00042c5800c40415010403020310640e90 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 850257356 1250 850256106 850256129
    0x1051e01030b041e0b091f0605070303022802010b100801030204020c07030f0b06040c0806010206280e01060906140603010b03090304090c0e030f06060d1401021e0d0c030213 76
    0xc800800c0050a035405211403096841044440f041110382c031011780418192810401580c1c0c140d044003d5024000000f542101c0142c2d04200c0c03648a503018100103480303851302604d0400c00300104003101c000c0544070288088940c0d0311034a0540c091040010107202503500031135450a858000d0407240701481b01078003d6800050a0104640c00d00440c0042c2d40d101c00c00e29804a003034101002e10074011203245003c1c030f103890300d404904c40c0134402131481024141d004040550341c916401041002c0b04092a0700450598108060500d03a0b0040c800c0c103520300400028100d00d81944c07402076424651103170401202d18059681143c603040d085a0540744c070703480900e54980b90401498554461a80b047c820549002c0c0e0b4891010351110600806500031012101d4114060b4842901c50344243c5509600c40040d04040000480e86140c0081c140d60042c0010b003002d20207201442401403400c14003005c00000990820001da031803081030001c0400d032038210b0500c095a648405034174074a01580c100c070413 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 850258606 1250 850257356 850257371
    0x1080105091512010f06062106050d030c030c061802090a0b030613050312040303020706050603010e060703090203011d06010807141c0203250f05010513030b330901051e0103 76
    0x9025045000da103506281704204c0d9569030b041c0144a10348080c8a041003041c10b40141d0303000103e0380241c00035144001c0c4803a030700011556040e00c481450010880034008c03c0541236010860500c200005151a0501d0300e100000a104024041328000c1c40c401c1d8040c0307040e250b0000d9840005003035600c00d10240a50300c842300c0c54244a803450040441035001d070089481040304140e85600945680c511914003480f203516044105402d80b840070006e1000c940c4180300148015101c0d80016860a0006e8000592020191071007100c0c22a107042501c990b5000400401481e401000b244005154200040109600c83c100180440314260103038039a058050030548155a0700b4098450700d000c42d84070159203d00010703a82c4d0080303a0144120b04c451a14420005410b5008104440300702c070341c100340001c8081c1190b4071040da403103014250301c9080301d8180450f0b0300403299010300007184400d00a14041ca1802030304018a5410503000136028401e043c00510344440d03020311008071a00b00342008241c81 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 850259856 1250 850258606 850258639
    0x14070c02030a050105070c1109070c0312180b06010813030804030f092102011202071106160206070c03050c10120c050c0a030e0306070507150b010e040614010801050915 74
    0x300c40600083c01c194680001d005030241c00c070030103400451141a44072040c0c0141700030406a044100c8040d0041040701d855070000074402c51564a849071030000015010016180761303107608500f814226064a09403007848019a002452181e1080a01840d1032029285070b8001b803201307401400081c1480840c03103403403c2031030140d0041c03030180c02c04030300502424a03040f0f88034103000d10146059000c20f803542c01004226425008942c0c4982d00080e60310002c1c1d0300e1500380460341d480300c0b200104448003800080b006079907c40080c40054040e8403210f010604500f071003810280309080251150800b03801c200c405039003140500d85084030f00840090001000101501c03184a2520fa4800c49e001c0d03640d1420405800ca8030b000105841030f400c454180d92800d40c10f40b464807802d900035040e0a020b1040f445440160b80201d12040811b1408462802c41c000206084e80e141e070300078070a03030161907030201900d50344030400500500703041710341403028100103034110700b01c0014415040c004d400c1c440320300840c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 850261106 1250 850259856 850259863
    0x6111c0b060904180c0608060a03021c0c0b0c0f0102090112020a0905060c0d08060a060504031407090603140606032a15070b1008011a01051b2b0314070c0203 69
    0x1c514020f442030112070019038070b4580080c42210300b282c04204400000c1003507489090300d20301c01c00c0003409284040741983c00f04440d200340074040810140d025040d040000700b01c001500c00410404511a886030804400c01d424202c103500e1443d80d0703a00c10301c4403480d00d80e404100300103a8015a1350050b0381d1104d014084a114005800c402d401100024940c17071090300005c0c00c0e503034807440c55890b02d1541d11400c0402c40c1e42c222a02c40c1c10006941800b050002c170320350031510a0a100441c0480e13041c1035890f10307040e05540050780282d0707a00c0d04c3c00c00301e450b24010610000354401c20890141000c40b03940d4000f0110340b014440615010013840c060b045268494030802c065032a03010108503250505d500c0c107120300d01d03030446002c1030100344505d0028540340140509030b120021100c0c01c07002c100140c001103426401c081c034504503c44140c03200820601d030601c109c540b180d5103e2640ca0004043c0c941d00c4070369241c50342d03207101010300c0c025a06842c44101260942c100340c0381c0c81d282c8408030042c00000e28 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 850262356 1250 850261106 850261117
    0x504020105250b0f0a0f050f040303020c070f0906060807020604021f0903530d0b040213030308060a1d07020a081b0705061c0b01051c0906111c0b06 65
    0x10710f14615092100e10340160060307521900e21000e0611459050504520079a001540c28102e407510350004200000e000343c01034032344003d40380c0803922000d9480c420383c0f1010804d0b500031302500350f958000380909644481840d82c8110680010b01e054100740d40402c1410031100c81104841c020540b1101819200f0780c5440e005580000d03031640c0000740002448881c0148803005010110f141c00c0744c442e0782c81e40348150903011242031007082c05c0885800f07a001255014101e800c1c80c01e56280d42422a40c0c2e550710151002c0c1c42d01030198a207445c1103190142101c40064a060f10912941004000400c04201100c540c201d032002c7c0c00c581c0d41c44980b8164a00710b4010002014054045084078050040c1c0713641d802d100240c0030440e540c090b40c1b20709210305d51050014a11040001440c8648540110b4204c124a100180b404a1805081021086401d01c01284101c0410380325802081030000c50b004041700c0380c050301100da26003040f10000304031a24ac4011801e207030300d855009442c1b0343d0750baa1081c1d89 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 850263606 1250 850262356 850262363
    0xf010f020f0106062f0a12090e07020604050d03110d09050102070803090d0f0f080112020a03140c01030b0609010e0d030318060c1701080618120f040513050402010525 73
    0x44495111306010b0040b9a905412000b6454400390b000448501140180b8519201c940600440f10181d11100c81888009200b403041c00744814000a01000d0402000c3c440e070390a42c0504440c4c105842d00728144480301c1c40e49000c0600301042001e0f0500c980c0e003100c00350038404000040d600c1003032902c2c90190050910242c40e4880c040308104c03e141011038601c8580c1a1aa6086940f03280f640041d170f0150540094040010300741c6c00144103403510050381c0f03921140003c1034220100e65070358070a0441781c8804018102c0d5001241160920f50b054003908010020440e0701906020080d400240303c003103804022072051000740740204c2810702a900c400701c600c9540041c444032000c0e40c02c00354060600c1c01c0151001a88101e40000d0300b040381600035040c1c60781d041c0039003400c0d1154101c1eaa001d1200f01c0b0003072618002c02007010404014200149070090b90040c41c50b0321989042c0c03c00502c5103ca0507480c108500f42020000143c0e400360480d00c3c162902002148142c0da4071058500002c2c2c5000000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 850264856 1250 850263606 850263611
    0xa11010b0604090b15281b0809153c07050304230d0228090614030a030e04150312081503010605090411030c10050403030201060b04050f010f020f01 65
    0x1050f015400e800520380c2e2503055800c50084018051119498441c04100c50050701114a41044e4041660304100c4056000d141c00106001401780d20641064070f1141110401c02c0040c2e0610b20781400e8120240016034480c0c0e050500903801442c4044407081a00c0000178040811042c800c61042c00d22032031071050100140f40c0b2502646071040d500d07030060107411280e2400b00c01029103032413600084030040c60b0140425103864550303424031603c204642001d080740d107446012a0401480da4001000030242e4010100c0c085280c0080301050941e041041d90080d0001d00944000c2500480f03040502001510006400c9a2000c25000f03450090f4000401c60088884804040c0d54030920490141403500117140100b04402c04243c201c03443e03886560380200d1400002404100f400b40641d0081001400355107a440c48000019011031051000710f01043c0042014000d05909114140107080d006401500d850b04000004061710124040141007104402c902d0f84c2852003400661f0704404070030000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 850266106 1250 850264856 850264859
    0x602030304060f06140409060b1201050103020f01021c0c0309050604060f02070503010c1b081909030611091e18010f03290c180303160302011b02030a11010b0604 71
    0x2912684151020b0315454140300c1002c0c4070b8880c40c0305510880300c2c035207040320b980c031400d2040c0000f814140e101030340e489640d07842022458a444d80c4c240000c01c07260000242942c1148108660401c220740c0c114119400684041119200d2a685800c4410142000080c08403e450100d4402d90305801c52508100c001c1000111141c00c200003029101d41ea400342d88525844105150880f10615650000200600759180882c50b81110303000c4064000c1e035074586404180b032400c904840300703c400c0500154003070704104140410b6108040200c81d860901d41d103424045000030316281c0036020901345110141210348596030381d10384900c0e0200d4010b2620380c0030b51b940310050541903d061105a071050f600752000e500c03a0341c4010001012102c0e49a8001040d01c4250001075950000522044a41c40401c0030a25545d03040020380000040b03800011302e422101d181c000d0035140d1202e80b00190020701d40305806d102d074011043d200d40248528100481900c03000c003050240c0780100d10a904107400040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 850267356 1250 850266106 850266119
    0x1c08070f0605180c100e030708160302011220030702031306020f0705090f070807020304081501052134030f0201090602060c03190b100c1b08060628 65
    0x4114030844800f00c140f03151065a41585031901d00408041e903009040e1083c600d011401440180720710400a012a400b003915040c800f40341c26400a458406180105020002c41d0fa20218202c814010440300f4880c1d501c255a04005140300002500c13910382e80400000d520078402c0081e02d030200c1e4010419546155102d50180d100d42400c030b40d0003481d0041c02c07008249410041031040c00340450185c0d160083e61035200c1264040303009469003085000400002844100c200240b58828604600582c2e0651600382040800c81c0307445080401c5c0c10702110010415134010404000801d88102441c0410120300101c0780030301007810104030401c80c07040001c014030010a080b080c1c024400e80300d000c031280d00c07032005a035100c2088601500c01c1c081040082c26001c01004080a110008400880e486440400241000e42c045881400240d800503642c01802000700d1404445803031000c4080f42c0c58209050541c0302d03400141021300803400c580306610f40000a007040d02580b0b5600300c2c100700c0c01b5103518 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 850268606 1250 850267356 850267361
    0x30d061a070627140105010605160605041e14160302030c0f01110307060e15010806011809061407090b090a21320d1b0309050a09020909151c08070f06 66
    0x40e0403100c5d0300e00000810414003450449100f003040c2d015070040038480d5680c2c0c5002d0000188101e60343c249150825101100c060300c001c1c40144103011104003410340b48070342c903c0c1003041c0c07038049080c0c54650010405a103020451485180c0c0594181001035130b0180140e42d15184146a81e0300d62000144403c2448078a90025201c812003105450800002e4804802105004e004840450300028010481d240c9004040072240d4900a4003103400c4d580b68494000315487e80301e86083e0400f1a5081000c15035201030004007803c54a542c060800c3c1c1c2c01c1000c18184211405030796408056900702e82c035180030300c40c1ca144200307a0126003188442d014900c1d0038850320301054144512921194109450300700400c00c1c40701c1300d02a40c4c8101a40700361f220100b03800800c032038041d002e0000788500032410f6151814100043c240380c2202603078426403841400010304004000140010089401c002580d40d10143d82d280407030001020701880105050580003803180341d600804480405050204101c8a40c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 850269856 1250 850268606 850268633
    0x212010902011b05120c1002040608180a0b060f0d02040f2003010501050711010e030d092d060309020102030c0d03050a0605011704060507090e09030d061a070627 71
    0xb03a03500c0344030040f250b240b4507407111800303801071141c0c005c1901d901d841d220034000741040070400b03011200c003900329000c94800ca034419008400092001c2040110124401007000b41c0c0c01c034110028090b4065640700c40003a4800580640e1107400382501a03001565031a4072068800c0d0020710800c07403060b040c40300000404003150766001011a0500f80d0720f541c03c000d0203507070481c0c0060b1569450010644e0303030f11616001c001c0d5020b041c042180000d0740315850070401480c01c000c8a40700c5074546d03410f0040701d29074081c5500b4680b81d0b0102c0d607654451002c00408601089882504001c034000302c0c94801030f802e600480140d803440c0e21400741100308071940b40c0c002d41d000b04140441040f000d9210030044540400b030401c0380d190303421002d0202e800207840350710175a404005450100c10352516290394503c0e1120513140c5400e5948042001001303105c180c850303000107180203000050742d13000304400b00c03000d40a0b0400c0a032001ea9103c950007011036175254041188100300c3c0164081d06018901003241c400107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 850271106 1250 850269856 850269859
    0x9060501030c210203060402040e0906070212071110030e0f031c050106170c090301020f0d06270e0c150d0e03030112020909010b030f0a06050f0105090f070306030212010902 76
    0x10481a80a00b50081c0c1c1c1144020401c1c5500a850701c282c09225000780d40081c0180c0d40242d400c10000030000e585c2e40e80580101d6024018180e94200910000d1400007281c900d00f508210030010755000456007404600380c004180c61800010302114420f90040c01040006030090194032510718895a001c0018400c9510846034126604844215030007100e02c24080c02d008160304d022803481440b610340519900406020541d807a06031020040390980c1c203d801c442d00714510103d08403078a001140192800303171a41c201c9a05242008401c1c80c00144000c0c20040c85c0e0a554200304d100c40c1000340140c02004101030301c0e51469040c180d641e40c401e5070021252031021882c0c800080400d00021007100d04a0300030f0002410f00d568540c08000d80301202500c4601300c2d650f901c03428138880e00c0500030302c0701c0ca505001c040d099400c6e45040c1030b13060340ca0041170100b40c0007442d0f005011603038440d0412500140c20518003211781c0d0719041b054005284030b4001941c08419108180e01c140415085000214030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 850272356 1250 850271106 850271111
    0x30906080906010b160f0507080706030509010203060a0501110c030105040f02120f030406180e0f0103051e0a031d120f010b0d0804050135100b0307020d031e060906050103 75
    0xe41d040269114a000c0c06a0420407908114a804a0115941c0c04075014010307040d50071120701031303991340786000103035403244695401034441005602d4040c410f0990103000a0001d616610b410800103904070304502640b4180400000c1200c40008200b01c054200d080280c020002d0f400d0a080c440340d01c3c1482070089200e00d00340061103000302c0740440c804100c4080382000f1420281001c1c0292242c06502150303c81c000289880080d488003000812402140041180c00301075045042c50ba00f058081e25941e250b40000481c81107000c000000c400702480d8040c90181020200310840150140455802d964024406105075003549408225580801c1c511002040b0030400c42c0c0a10521070301d0490b0181c400d01080c84204841e50007031400000000d505100e0300144000303408600248200912a000401504c0040180004c885c00c03072107010700040c009607825407814800c001e545090300032a9008043d210750341030090031120290807140d4160341c0c0081c0009500c44da0300c40c001346518412240000d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 850273606 1250 850272356 850272361
    0x9041b0603020d1d060c03060121050103050106050303071a100e0f1f0e0f0405120301090615141606020d141605040506190c0f0506100911040315090f03090608 70
    0x10341d0041c4d40090780038500240c081940c440c50344005642004003c1c03030611003107130704504c0c0c5030105a180e0401c0b000150720009155046050042c21540c00e9003256010b03610801600c07000c0f400304181c1d05c90f64444005003070015a20036031445c1400303035aa802813100b80320400034000080c00c18600b8138072400400b46d81203413174504a100040708010602c100c140b44c10617180410103140c00c05d11143d034054050022600d82c0320050390f0100305a44260f1260600513074030802402101d007032007204908041d00e494a0301d8402d00c64500044c0304d10900c079180c2d83c0025001006c0c010088150152001c50003103802c2041031541003103290b070780c0090071900c003560310468105000506004500303880035030b0030160002e403d101c00d62510b6240c8074101e0417546c00b0711076090300700400600c00c0c09240e00301500c21030140c50745080c00140c0c5008101540c01081c00907040c0300300d100074810708070182c41c200c98000c82c1802000644ac2c0300c030703001442d110382c02411105019183d1003c1c590404070400883d10030f40d0340c2e9000c55 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 850274856 1250 850273606 850273631
    0x12030702012d03020f07020d0507290a030e0c04020313050c1822080409090308060109290405090a06180b0a03021528030c090e0609041b0603020d 64
    0x2c1e040b0071021500070503641e00b107410707220b5400340003071802c0c3c65041442c00010743c0001d522524026421940765015000611505652843e44c20100b0000085400754411200b51040c1c140900e03c100001c040e918580c681214604000030307108804041e00840d641c0c109070005003401c451281c000e039024031906240800300d05101103a00c0010700200d581406a480d240182502415048502c2c01c0301003c643c00780c0e0208000340000c05c0144003205001030315017610702d13029010750f03001488207061080c0003008012400c800606007212401140386140020701181d4407102c10f00031900f11a03003043c08030040008400080d8401c10946001c180840300049000412a060300c800c5800103412280508003000142040c40045107003090402100381002144c04860402850390708864280400615008038110340511031b19900442e586413030b41082d4100b59014030f4034200901324a0003915620300080a001d101c0c0912070070703144100101c0441c184e98401c010082d40040d821420020300d01618035107403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 850276106 1250 850274856 850274897
    0x906140604060803031003080304050f0123010e090715020f030c0a1703040c090c1e120507050a1418151e030402031005150a030c080c040212010b0a0903021203070201 73
    0xc0e081e000c0c01107038071b40c11b540c3c41420503007011304121a20310581c0c801280f684800c0c01500b10401ca085039203002502d52005150442d841a4000241d0111000034820700010215880040d540300000302c05a151745008224076001120b82100c0c020300011603540c0701c851012400e000c6640c091003040858091016560351644800ea90082402c085035208112104058020846180c040d0a100d40b00200700c40045143041c0b84400740d1400030b103001c2c03207501e030402c140e00c505900554140b5006081000c0800d02502d0880c003400095510400820f5501c11444200701c07800500c80c010340320030840d4040148c00541500030007038041c03200d415000703e8404080b810302a2407165800038001e0100324071600389840100005003100885407000611702101d5140c0341d2205c001140308000f1201500d2900039107134241005070241c82c1c812030040000f011240b0020b002c031419138400381c0b807481c3c0d10740c9500020354540000342d20081d003050f4844078100112714044050302c403481c000e0301c44200502c201e0111030070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 850277356 1250 850276106 850276111
    0x509010b21190b040b0901021c020706061502030307090b090a270501120309080105060d030f0c061109100e03030a0f1101020309030324090415090614060406080303 72
    0x100060076100101c0c0481604000e2001e510103141526107289060042202420101d5801d80350500a20103000070040034450160b8041c00ca00021800c0062140c681403843e080000030920042d00800e80c00c1c10300c10300341e00101c0101040d50901062800180f400303510380d04100e44140c040f6a83c4940000c034801c07520108c0740c142e800100800615402c04685010282d00b50081000340c516400c000700002250744202c5010301b400d0401c0d09002005c51070f004000444031f81100d50301c0d034106000e20a2644417410301440c00e030340c582810b01d8030b1500c030f0f0411510a85039000c0941036074144022640d191103ca401400c16040c01d407000134030f200c070581c000e482a200031840369406a20810107800c02d01e200d40c4814000c50810719040b41d85041c123000711801d98000b9140500b09400c00420310450a0810101540708002c2d800f61303811a4401100003015124000d1014003456809410031410318099800820301301d41c8034204008607040140d401241d0340003100c121b4003c070b14000d004100c42600109891 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 850278606 1250 850277356 850277359
    0x6090a050f010605070503160309050a050a030803040f021c06020307031b2a02060705010501060801061403150d1203060602070f0e0604020c030403020d150b04020307020a0f1e030504090509010b 85
    0x251543d19084080b250340c0d0069400380c44a020a00c000206d01c1e50000d54114500d00035a65207030300900700380420180c0c1200b039001071300c11410040101f00003800e5800752688290059401031200782c150011034a10101c403ca05403007070a4040c3c1c2710003004110340c0a5801040295000c100000900302c007204840c22149224004c6550100d85500d0380d420f000d43ca07000e10314520520b42d03900035568041909a00702c0f04003103900307944440050242036803008032203004012504d000350884651250310b440c1440043c16103043d400301c1c08109004c076101c401d45400c13415880707030320740d03841d6028614001c00802e101d026010042c0a918400107110210001e03400a49540380700d490720755225482004000d5000809079511800300303000000140e0f550303920f5032104901496200b4504211492118215400107041c20301c200e02c1401400396107903000511440c0e046c0d1048403c80c2149a0381003034440003003800300340d4502c0c800304190281007692100240040381c841c05014041a160407010034284c500810300036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 850279856 1250 850278606 850278631
    0x80a050c0115061b0c1203020a050c030c060703050708090a0305100b0102060c12130206040303090f1e0e040c0b040f0911040510180e070c030e0307050f01030b03010e0105010e06090a05 81
    0x103428061100004c40c84d880c45155013800482e902c500c40c00300304400d00d0b010380160704008081c07001c0c440144441a01008228090b04d03604d852100000d48500401101030f0807c4004610a4100400342d000c4950342c4900805000a8a51300d15240340d54583c000e20f0300d105541044d48522440d400060564000ca02083c0d08a051400b22154600d1003013005008074070482e46012607c015032582001800039501035a248080c107414081001050101680280484c030810a04402a101c01c40145c40c280c0344020890241d1340c981c4d0411010bd5070bc95048409030f04000100040c0164401e1040320880b820b41c2c01c2803049089030411070000e405107200e2607400c10f00c40840d448103144609054900082803100e56100c4685139204908041c0e022034480b004103050b6003080e418550040b1005016a0040f0001d0501a0400c03011855000c203038401241070685034030209000399001c1d00607803442507140008001c035694032500070032640d10542d2a18016002c41000c150307000c1881c003400e841a20707078280d41c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 850281106 1250 850279856 850279877
    0xa090501150f1512090804080601080a020603070503062e030c18030821100f050d030f1b08070f03090e090309060d020d1b0f030b0904120c080a050c011506 68
    0x221002d5200000f44007004680801c00c552420507109040945004040c0141c48608119142d40b9000c010b800014003075012a413000010f039191801c40307030b1010700f5103041da4490b201d900c04200c034010012000881080740c9031413003102030141c20740e4181f092082e54003807011070b45001098450f449100c403070500c4161204020700105998500802c0110340348041c01845905001c00090711441c2600c078000e001c103000604001c110b6010b0414006804102c40344104090302d990302134100000c4026507024031107a81c44c0f15843da1440303460500c50390b412514440e65078a003032a0210310381c4030768807086002c80c203018000702d04441c3e0f0086051180601c040114a40035109041080341e4200d0b030f0551022076001c1008980d011828062240b0340f9400d4035030005108030303018010301003440081c2840304061801c13604109680d524104c071600030342c00c016406220001d00e1001c84202d100c00502030002f46002504012841c1d03c00020f2050360100002040400050350f041d80000c0818482e03a80000c1030301d00c4d0f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 850282356 1250 850281106 850281119
    0x60118030605280501050f1503060118120506010f0b0708040b0304230109051522082812201c050702010207050f07080a14150a090501150f 61
    0x41140c00c001c0740f43c1e040c4005444202180000c00714490500052500c81c80100100d0138140d40c400d841c01700445a0711898070290300080468000144203d04008074100100c1e80c6404112a0b400170740000c41c1031002c1c03052a428955038a04003845061500301500c1030001e030540d4803005407101c4030f500500300c9280510700480b54415410280c01942e00e140301c0c08007508000b05001c1c1c090b0342258a0400401c41031b00d50b003415420300442c402c0044100b030340701041004000800f1840206040041d544810b11241070801c1079950040c0d000100c000e03201d030061003c42e441d03651800001513449945808480c2c00219041c1c05a4503200048103002400c00d9085030003540b040007421898522442600c00c20f040d0180e0901901c600f6580c440142c3d6000402401b072100512440407050012401800841c0c6040c460590703d4818440c045c1070711a076802c480380083c0c0d00740245e2540406460000400b4208104568010425001c08442641c0391180a058542100343e01008076031440d031018011526099 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 850283606 1250 850282356 850282361
    0x102070b0f0c010c0809010506010e090106030c050c01230c0408120901180308041406040506030a23011e092d02070b040c0f06020601080a030507020a050607060c080601180306 77
    0x10076040c22071414046102d074000d00f40704000351a2040c0e0741d11000c500313124040f2401c4a40c00380500741000101c090310f0305103450711071105046601a2400041c01070040c0001c0b02c05000f80d9001065550170210001d15460300c8981402d24011461035501c5142c490382e141800364480c07449012000e41000c8070f00b8440c1000740015103030b100d6060400c909150145c20380c820402155402c1200d020700041811300c51001d00f40d00c11383c9a1203041c0c4100c0d2a090524001402d5070100a00ea00c98158032004500110714074420910540d00445840c5001540c540000f4801500316041d6000b048840500018804480e80580921000b05080c50b0740c2c41100c7c2c1c01c0f11048400900d51085505800300a0440007a0104010b2881203000b0b142030110582400c41c44440c50002ea405501158403141c018070406c1004180e05800c1645420100e90300d00c0507201103050030805500890f07006102082d48414060180c01982c00a1513a99a180301661a2001503502c1c40c0c94510110001201c5001400001c100c1e5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 850284856 1250 850283606 850283617
    0x13050a1709060a090f06030e0a08090a0b0307081b0306010e0f1207140a0801060305060a090c1703090a0e090c010309170703051206061204080702010c0501050c09090f04020102070b 79
    0x104100e10346140800402c40e00c1c2d0201c08200005030400c082004581c441c054914060b00d2280b03028005c01c0710b400481941e501e10654041c1030510b0014400071183d0310380520100411070802c01070303280c3c0b42c10040a060140c0407500084007009014602c0da141c0b01c541c044a20996058403640400742d46e410034012403150107207000b07030000c1c81c440649a01c2101007080d4030081000d010f10207580034403041801420881035105180c607a0500c401070001034404100381b80d121080640005d2a00e1040c10003845481080c1c0c840c901d8920301074000c50380c0b1200440244242d00098030303010303181a40d0b100c0700360b10410122074100580c0c02c55004502d05620a80281c40000c3c058244e000700b103604919113201c10b0b84514004c5001c02c0700010082a8841c0f2003803019402103040b40c8071b600700500c43e56207081200c40100000c0c114034000920200b113a0040d16503000d1190440000c211030300e8500305110413907220f1640c02c2c1c4070308100c03c00140002200d03401075114503410ba01801103217250960403901034106 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 850286106 1250 850284856 850284893
    0x308060619170f06100c1b0f053d02101a012c0103020c0715050903060f01060504033008060f040506031221040507142d0102150a020307020613050a 65
    0x442610f0403410320707441f040d4005042c901d41d4200000f880c003010400315006c4200c444c200210380340064401038480e0301d4020014400040c558511a0503a02c08905105001484c1000145441c5418803410048142405410001c1c1c85603905c0a0010301e074115003900740c9040c41051003842595003106c0d4801d03006090030280b00b00440d52459150181030301a0f0b4030840b0100c0c0054008130f1a0709051400300b080036003091440041c4903455040210051891044d40405405603604007041ea000384041c1c114800d2019006003a05030891801800410b120018fc580c1885298440240350301807903c0d20400380134a400400a00080c2001e400178941d40d00003000b000326640488805a12a030100708400340709511031806419a1420410b0300c100040300035580d9405001c1005454081200d80c010f400003101d24080c00c03010f40700784200100c1c0341c0110200600e281404d01d8003800000348581d000303107000b400203800784d51040c0c1d02c040c6601100e011149020b0041ea00200e00500030070319034002ca6128211 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 850287356 1250 850286106 850286123
    0xc2a260a111804080a0f112814010e0c0a0524070213020a0305070827030904020c01090507050612040b0603011107030c02040b010f0c0308060619170f06100c 69
    0x40a040c4000ea110460f01070b0b600302c0c0005105818164041c1070441c5030402c2e410814640c80756001e006546401c41441c103c01c0800700320b00c0c1804200c04040303044040b030b07014100c1020300046806580c040e0010001e220310500c150440100d8502d1f0503402041a26030207401404002060a0419102120300e0408400481c00f0080600981c0383e56484074a444400f003000b503640e41401c10b00a0848100510794410811047e040c06003c200c0031020303d120920400d00d0b0844c9800c0ca59a0608511501104030b9000348006030756048070b54190086131000c0c0c0200305581d151035030380c410b2160070700c11804c40d1281c0d60a048002030008000501407a0010070240000862041400b220340c034680c4118015400b08406112903000c510b041c0c01928103082d020300e481c0721a0030f01004044c10b044240c0d17a00a09210303060300011b441c0d88641c029103090404001706108900311a01d0080c02c81061b0f1107440c4505440030001407030500c404944180075100c050404400609590701c12260501c00301c000711042c20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 850288606 1250 850287356 850287379
    0xf031801180e0f01061d060415110f0a020a090c02031b12070803090f0705010e01050d0e06040305031017070b0715050a0b0414040b0105010c2a260a11 66
    0xb40c4032940710312800541c0316401c001e50600c0c01c0640110a01e682c0949041c580302d9500c401521010183c404a80c0000c1500e40caa2420841c00da5411507141c1003138000380710b025581c80a40d440042c2d028580ea0080d1a0200b1254075200c143c01030368441c442d0440940d00410a070351103000d6141c82401a03644139002e680c229000000c031300c1d684e5445030b1400e0700d03c08404401d011a0460030701070340041c544d8034401402818074101c0017034000d050101e0202c0c1800b030049205002d0070304a401c40d0f00300c040d00005030f0b16107103054540905117800c140c2c0d01e4600741d51b10b9440441c40280f0814244141051a0020001e09141108070300640c1c1c070014045801c140d5802c03010407505014090700340501014440421442500d4040c0000c03250f103079542010106d414020b11001c6401841c5081c19141c0a07c4c0294480c4021308000e880e4000c0d000d0700c042d002c4645840304100c180090250810340389220911b031040c030310791610201c51802003208031b8150382051030703203000250360b4115008590ba4060b1174444d0b0361 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 850289856 1250 850288606 850288619
    0x7120e0d12090321020a0308091501030f030201050105241e070c09110717030603071203020703060b2d0f031504050c01091d0406110415020f03180118 66
    0x91100e000420003042c50464180304022039a403080003510310fa007020264200350712900950b60203040704060706020400c408240814400e11480e480706025492105840d6940d141c050000da00c08082503006528000c000310300c034a802c5c10750b00d841e1150780e014402c0340c001001c2e05140300e51205c01011200003c02181d138413a0f4400d000500f035680d00552103058521320345802001569001015114002003c122160008102d8184801080c107504d075865126680e0402203450000560011000000f001d01402c082690024801c0c0940784205014014140a80c1c01d100d1095203100c0e1a82000044800d00103c00ca01d0301410f402580c4002c21031400c06c05a0342c00720382000410741c10440072080712020402032240402407414840028a021030500707140c00c0c0084c02d0250807454039100301520102140a102141d0030241d0317a260300740c410a80d070759a15580c032885981c01110700c00160050044c03551041101109480114400103411014100c5250044032a01e90018003c01c00305501c1c0804902e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 850291106 1250 850289856 850289873
    0x3020c0a02180f150319060209030703080d0b031c12060f09090c0e0606070b1302190602060a0b1003090503070501020c01200f0a030f0e0d210207120e0d 67
    0x707081405502c000390504007880d40c40d40c3c0c0000c4c56107140100e003c1c2089a2038800092144405400351000ba01c030507103515004010b03200e08403400d07506105406c1e0200a11900307000800000352000030030001101c00e00241601c840b54400152250002c2110640a0b180074007240c41e4074452086002402c540c498500964806950300600c19450742c2d000c5010030800312070702400107001c9109001d2100c0c035100c80015514851018002e00480c101c001140100f10301401e0a8040d40c0d00605904d843d03c040034011852147c0d900c1840010703c540b43c0171401000342c62043d94111440138158408104c8900b0003600030b400c2000e0112900c2c481001035101090b020b1000d421829100d90001c580751141d48904107a0041c90300c0020b00701361007006482c18403030400301140c4a9011500300030030502100003401c001020b800e102240280201700c0c0c000e081d154000c850340c0c04900340c484030000d580200c0702c481e000c80c01011302c01040036500c0c068020259004101e0451040d500400f40500306880d035031042d04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 850292356 1250 850291106 850291129
    0x91506040f0e0313090608061f080304060203091f140901050906070b04020a0611030a1b21020610080a020d170d05100b12060405060616030c021512010603020c0a02 72
    0x780d07402c08101814200c044d00c80703180003086040c0e03090001c0d41c101003041c1c3d100c038400b5003c01603014060010640078101d14038043c004000040583e03450b0740c0d65020203900d0794000303030025100340900c0941300c25110301603072601c40417052a91603a401180380b9003a5552584144016818880300340020899030b903440707000702981ca10803c102290b070705140c41400301034480c40e04440d05001000c048030008034000001e8405118031813414041039409141e000c0f051445608019100d105154072000b81c0344003420501d02001d507168210303225075603440ba080b001c0030098010380342140c1040d81d1490151600d500080c500502a80751750010b4072143e02c0e074034030301c3e4444515580c0d01a1107404006071008204d030200020721b44c09d10000d2038641d44c20349440d88101d008004900c20380e0b03504045509500d59806941c40c5421251602003400c503130b0705001c2c2510b0350120089104042503444062500300402c207689400001c01070885c03481c0d003001000e801070f4000e2041e80c0510310540d100100940e0702d4044450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 850293606 1250 850292356 850292381
    0x1a0c1c180303060906060206070c12030b0a090518060105030c010302031506030115030e0309010c030305130204021c1505010e010822081b01150b090a1508010617091506040f 76
    0x14210b440c291041302552844e030300000c1550051000c1107075aa8015188074404c40c0e0005082d020701420000a42c0100301c50515107401a05a60b0080350b05c04295100902881004000c00c50a5035501e1000b40d5509003405450b80641042036200803c1d4004c0c2c010f544c11507280c08007280280c0c032041c045030b0f4540003640300d14040501300f07904018803074040c46500004000300300a5444c00c0c00d0f03140060b0910000c07001c0101059650800120010000d24101605235402002555a901d46179078a501611444052502d07031071030200b40c1c50340b0150040500e030480d541a180c9014440256005482c0d481d8002e20428000c502c0098140e0281c20f180c00242000788520742c0e0343e4580210050340c19006d0804101c001450303140455250305030070441c00c01d9084a80840d090390f520001900400c40d03494a60380321107010709203490100b907900e07006554941070362040d61b1403403c520340d0680030b01302e000b10640d203013030480c0c00c020180d1009504403082e150b0301010182c004203a40c0402441c040440d00c818080b41e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 850294856 1250 850293606 850293611
    0x2032e05150a05090d24021810110604030e0a24030213030c03061401050118050f010c02030303131415070f0905060a02060a0608070b0f090a030b0c071a0c1c180303 72
    0x6c40b884a210345454007280c82d05821414102d561010b514040c8803c640c16105014504890a80c0c0b440754030301440c019503141c00e0b00c000303040c20b02c1c004d800700a0556041344240707000d140100340b014100c400300c120584440c01c0295084107112041e0000c1d1301160542c1c0003144584800700c0410382045003080154440c00700001c1048030001642c20642c010380095041044021b28000b40c0c20007083e030300007500c108807448031403207003e0070050710303004007100d4025010301000c02040f01401c05a042c100003030b0300500b159100c2c80c1840c8200c5032100c48610714620b90700c00442c080b80102e445059491035415580c1030040e40142ca407400243c03a0b4024185e1180142e20000c01c02104481c00d000304c00041903220000c24050341019103982560252202c800001c401c08191a1540d07907030710618100a6401c0642f2030b000d401c040c101c52107143c1c066042520380c2103544558401410808103d24820740d4054200c5090507a28201c0726507042003101e520502940710184010031100c03810b04920354500c00e4400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 850296106 1250 850294856 850294883
    0x2030a120215060604151809090c080106150c1b0b0408030a1d031f11121605070201170709090213080f03031303180902032e05150a05090d 61
    0x10640c0040d0300a0120340100d405200410105c040100038901c2c0c81801d040c541c0c000c2076041e40302071800130b02c7d48c4902c902c01e08000050301402a02103031101030702e214000030301425444003c03481624a16002140c001902c5031000e00115031401c506603180d5805515106050fa590451038403030381c0054201d280260000504c1000040d080700c3c0498400101841c0e036086a012500001c3d2111900801350240b2102078110880070388407036000c4c0c84440103c0e60308a1b2074142d8400c42160300441101d08000a040c2c00744441000c0c0c2c0600107a50009605a40c0c0080c0d0058148030100304080181c52001032140100b008100760036640007034000480750703112480149103801216454884413000503546a00208280030200030000320010603d5050f04100d4079134002c4807484040425568881c207480d074408001d11110b40141980d0b9404815034010109030344a20b00501007480d100c91103026404a6200d403a900d07200c14200c0642040ca5450030414104040900811082426908101c2d54011020368 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 850297356 1250 850296106 850296133
    0x50612010308070311060c181f050c010b0a0303020c0310151412011b02070f2616080a1a07090e0a0b0d0c03020102061609050d020411070f05010b1e060702030a1202 72
    0x4000540f180203c4604889c0c0c5e600341041c1800500e07209000c1d04214000580c2c0030407400135084080c10340c102074608038001d603032400d0094882e501150464440c1c0175907406032406484501401602240303400b44595018500315405502c5003004032001e8101d01e04103840c480342c941c01e02c585061020300c80781c4041d480c080000000d003002a01c0d0454074110030100c1d02400302e0032481c04140721880b40030122520a07100e44901c28500aa41b149022600d828188042480c0a0104200c48058030941c942440045440f10100044d0710840d05480021401e140821640c49140c502e20303041224424001908003035140401c41c4e01c00c1402c8152100b5540c03035000c0085590402c41280e000060000d01030307003250054030050240c0b070b25100d070724498150080c0309002d40d034407a400290445481c000e402d9980a503850000c05082c0301100c16900d952a005820501c0c2c01d085088840100b49600312046080d03002c020007841d03070407600c0107a03098403404807500e0005502c1803011010301c03903940040c014041c2c60030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 850298606 1250 850297356 850297387
    0xe1314010e06011d0f040c031502090f060c0d211107120305010302030a031101110d05041403090607080717030c030f01091a220f06030201020106050612010308070311060c 75
    0x24400c0c0080283d680c98540100c03541d2112542005c984003c4440c1c5480703e0610700d414543c1c50708098030030307050792800320a02e90741a401465810001d8a8150002b80b04000704190707401342c0414031003d600200d240341c0d001441507081c54803d40b00340550401c508500c0d0240c0c02110710440704107868440000307074034040c007581591151807038002c2d2809200e5903047d640440d4441501300d9008051020b01041031000001c2034010150024241c03071402d2321000c1c1900548060002505c0a0300c0d1254013070449031080780c002c011100302802c090002440d01c402a600c0b920198002032003510804216840740c441400f88100541c02080394401e410746038100781030030040081040c2c1c04070425034a0b00c0c03130100480000e02d000b1124110101c61041040901c0d01c02c80b001a4400002e415603145440350190f4040c0540d0b0008080d40e0003039000b084029100d41c1403200710f1140011444100854000410014200000403c42240700345025800000c192a90500d080380954041da00d203400451805170b92071041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 850299856 1250 850298606 850298609
    0xc2d02100e030a0503040f1b030b0f01030b010b180a09051801020a0c2904391a0706060b1801031e0e0a050a1202010c02030f040e1314010e0601 63
    0x810200301240c0910596a524810302c3d40c04800c1c00000300c005828401515640c01079140c221280103e084006811011515040d0000b1030740a001e510210303160000313060a4a040c0c0c0d5015200030340503401d02141403510b8000305803000781580c0c40da00415050700d03071408107001011901c201080c94141854072140c41e620914045886a1040c001c0240032540400f04021213070300003000310800142c420160303614103825241140204544014401002402141078075400b502c44100c20105101d0840300d0034096009401451400300e0350405d001340f01030f2200710304100c400c2401d0640340840558451003550185e901101c681c440c040344901500f56490003400c500d01c801d207002c22120b4082001c150300041f14004280c201559240304a1282100300000da0140f42c1040458a000d0342c2d80c07800080e4004054180e000550030642c62103181030002080e100710a070b480e80315605150030400c0c1a540c00300d00a0034120040c42c556000b0021403548200c0a0401c3c003410004030304020420207143c50280103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 850301106 1250 850299856 850299883
    0x60c030d0606260103020f011b0c1a0c2104170109020f10120b0f03030706050a0609060f060c03090f121a071205090a02040c05030108010501080a0b01090c2d02 70
    0x102c000d0140b0301e100c0d44a5480c1525811100e0141c6887c3c0c402c0100c41c1c030298500c0c0b20b008903000141080601c000440e0207004c50301001401c40d1040602d040007251030140030003400c81c0d984607148035a02062034070700c0403401801d00e00c281802d080e5512a40c46d080f10b013410b1510b01c665034078490b50095040191020040e21002e803110501c503111250018900ba200c0309001d0400c80e50752040460b1a51520210b040320f4000034201ea46a1109090000042109503415010a40b41020000d0701d0501800350300121002242182d450031301c3d0500a503156200078004801f04811650045035004203500000d028000348100d10121820a282a04070303500900000341c8503100c2c21007009046035205400446040c131500020540e61504128980380103001c08000394414201003225a22640c0000518102e940c000000d01950b6603c003501900c601160901030720034040c0c1070061200481e80e8110445a107040e2504d2a903260085c40030303401d010090840d18019100080d0214413041e410081c84051016 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 850302356 1250 850301106 850301147
    0x3030a170c03040c1403100221090c010c17120708070210060b0a0c08090303040b03040b1305030d02090d020d1b050108010b071e080f03010306050106110705010e060c030d0606 77
    0xc054030303924882c4c10380d4401c200c1080d8031806a20326607141070100004a264445044d901d0f1842940d0460816280d00034560540c1801000a90604000544148061720603102e00301203403d640c0310582c51180340240441005000c224007006a6003a19202d88076003e10b03070b9204490709008800a060481580307102070002d0034000300388903001c40c2030100c514440441c204401d00c5001850015414001d0100d1590306000108000400424440007188103d110b1548000e081c0e031981d10b0707400a5911040003a10310b500501c40318070007103000d50040440010040448080d10060307400901d0101d50b8007422110340e8042c803162801c560746c401102c0d018040c01d080007801036050141c4500d403405041005001d013681562204407000410140b030f1089500445100d42d219505481c46046500a21080700d000d490003000080692041d40255585011813018002c668600801107034170030880c850860384a042040410281c20f802c000400d09030404180110b40540350050152030154448a4540401d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 850303606 1250 850302356 850302361
    0x90209061801052416050114070c23010507030b1c1718090103080403020910030218071b0317060a03030c080f0d09030203070c0b090a0612090203030a170c03 69
    0x14801c0c8001d6064502c01c0d00c0980c810102c1c0c4040e03990403d1989035205140f100002c07007003503a1480b40c02c04050540200000d01002050260000b101a800c851a000080000e840240010002d100081c501c80c070322080c0500038100e40300b4540c02c68006030b03001c0340402d40d180100001820031007540024803001d0305031588048165203900c007801d400000d140d41a40000100c000c07115030621500204400c015000101d80e40c0c481c501401c0f03c0d4864001a4420704a110000310349100c042010015241d014015000c0c0d05c1403841c00d10010003001e80103406105410078401441808601d05001e0316010781c0c1c42d125840d81440354200d0301c2e9400381c0885d00590503c01c003400440d0b0040110f1210f43da00c0015a5620000028405820b0141c030741c00400031418006014181540000504840e034050328070310030b40780d544161018491281141c042e07000b0300389080401c00140945c581c40903107200d4203008100c1d0445603000a05661240c0d548102191400d06072840b0800c140c21110780c007201d090029450350 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 850304856 1250 850303606 850303639
    0x40309150504090506040f05040b0714181e1005120f0f04300809010b01021f020903070b0f0a020d030b0109030b06182e0f060509180a09020906 63
    0x14850b034050b0380b0700c658407072000c20303034586599100750211811000e0801c03a034101440d00340c5141c0010b45214001136485165011400c00240840d00b040285001c010350311800e000c2881551107154000e0010031500311448541500c1c1c8040c0790030b2302c440c0c0e41e58660b6036007408040e214021202914101921208504101e04850820012a00540c1100f40d170322240c0710304a8582c040070241510b55951041c07a100007890190440803082c000c1108a00030710a03420200c004903611312000f5001c09803000801d80c2d50702030308c0f000d60007070004010107800e41d0ba20680300c0c0284400c0c1e610080c418201c2800c0002c14642265060000320119a030318902880701c0541d540000b084401d041c000601440000c90108601c1d40c2c2e052140c1604c00403440c8259894504482e4000c040e5030602840c120805129070040e186440c40c408050982e0050f0102541e074505100c000c65131500304003442030700b20400100c80030702d41d8460100c040c801c0c4071307451000c104a8150310501000800241403140109401008030151 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 850306106 1250 850304856 850304867
    0x10917030a11120a022a010213060e0d030f11010e03180108040b0c09010905101e02030a140f2208070f08300d050f1e0a0b040b100804030915 62
    0xe01e40c4000d80c550706d48924054034100d001d80030303511342520400c030b03450040d4064000e0a54114000180f00c0300b2036550405550040718409840c1c0d00c8032040040000080c0101461617688030280b600014040c02c10141d142110316203d42d40717080d9403001c00d052490280c0300c030b1800242a800c0c43e02c1202c80c100769981103036140b4080c107140074000000c100c01020764415002040140300c000c240223200d000252001d0070644d42c00d14650400c01103c40701e18030aa0001040b9203200801350f448410405c4c600740c510710305401c122403041030300004124003481e040d00088500c140900e02da22200c2ca46160542040c51700d0305a03448450342940504040004280c0494810040410303038915620803844441c1c200c55400015504c084502c0020a552104488503840503204140264544049854008550706400e40308454050a0240c0d200050890350640c0c000e101084806080030415107008030001d180c4400661b00380c800903060300100000c0c10340c402c036000000c088859410a40640c10311001300b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 850307356 1250 850306106 850306111
    0xc03121303150216240b1e0424090f2c070e1303020c0f060702010c051011091e0105180d05010504120215010f0e0405010917030a1112 59
    0x8503080b001e03a0b610031038090f50119104d4400a03100041c5510051400c2001c12800b01d5038180d103d69030a151180f10b00d07140c4141c1c180183c1c0288440400c0803564402c600000240103840d0b042a00c501d0000307180190458602d0118070028a125102820308401c20b0440714042000b490040c18981c0d422440364400300340d034065030202c1c03d068605003c02d0340202c0c0340003c80c0d4081140e40b44820100900c080c840000a03400c50301caa420340d108200034204002e04e00c1008100079038000000c101290042d8000c01110755180d1080e4140c82d0b1952201c8803050454074008003910b003411000613074074074074581000e12626001200090b844061812030009002d402201c54070b0101480380d100c541e00c1d035a244200c8890140d481002070106103450318080070300c1079100c0301040161140244004070800b03c0750202d81a503041840e007100d100c3c50941e03003650929028005803055540c50081b4004699500c01c5006280d0102a150b6542d04021034504100d920006070f055040d04240300141c0400d204176201c54 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 850308606 1250 850307356 850307363
    0x8071215060f050d051c1d040b0901120212030a0e01110610230402180102010b1804030f050c060f090705030307030503150a050a120b010b03061309051006080c03121303 74
    0x40d0030880d1031428030706e800b080c2c50141413941030380b68011904a9209601c440350b080c1c0601c0c21139500705800107101c2a901a81c14955100c0101c9005004542040350310041031030006000000401c507035603495040d039000c0b03030404001403c040d0f80004156008900c1c4007070303001038800610981c50718000e10b00b41100c2c0e90082e1f50000d2281104003c030180c803550b40310200707a8010000c5588500450110310001c19040009000d5400c06000504910704490f410820b0b00b0050340c16075495442c1e039000c45510120000440c103200045c0140901060100710561203469990446041c9081c85000c26140c40d99a6024610075481081218000707588101502e400a076420391000d4a0320740d400010752500f440750480b40d0440624500000c0108485031a5409240038002816281c5d0320396042070203a10044940d1500402c8541100c01460080d503c1014600d000c6e4003507034060b180740080c000640d15654083c44540d401196400000d180c18042c00d48010105410146800000395000150359407074030014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 850309856 1250 850308606 850308619
    0x904020103050612070f08011508100203071205010815090f0a03110703080c061b07020612070e0a090605121605061612090314120d0f020408071215060f05 68
    0x42c0207480d41c10545040f410048141c840094030741c21b1807858038481d442104401e40c2410040361900c003806911109581d10980903002d01c103040682c1c00041d60001d80b41408004c030085c01da00300030b02c2a1040034043c01140c009418002141a4103100300403015007429841e40090204200f202000141d00c2c458a615041c4454015004030302036050800561000e8100d850008294500d0400400c0d00c1d48562605165141c800e0a070101d103070300034014080000d400c080e0400c1048422808681c000750b00500e40d2500c0614100804041048000c031517002000722512910140400d10304141442280702c0880010000804c4440864a00091a1141c18016400083d070b610b200d4000207580c46116400007000440c1046008000300703591518481038480c40700c4a682d96400c800045111400b0140850050781005212050000245040100139941d6582000700044031513080c0114001000141880d913544280c9040c800c6041d100c404064260034a016030500880802e07441240581d202600c00303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 850311106 1250 850309856 850309861
    0x2404120320070614040312030e0f010c02010b0102150c09060903120a0f0f03050412111f0f050606120109050a0207020925030c05041a040f120b010e06090402010305 72
    0x5030307441d48200300705914680928500c0d4103851000180c0c1011074030305560782d0081c600315240e8005540100d000041240b0b840039114104c1074071070b801030380a50183c0d40645075841c185012550071500002c4035100544d44846850700c8a41c2c0602900c0c510481c41e4440c00c07481d01d04029031042d50b1055800c170b58421107002c19505015101040545d81d007000d009006ea5403060811405002c0100f442003580014024440360b41d01d990cc24040c02d40100ea000030781c0d4060503d040020b03075103d0301c140e02d005041e00c11019820301c0e0741d424a250605403030760700000060404150b20200c0c10395000404090044c0c2c000c100e221f100031040344495045484000000915031502100c0c8030207803081b140003941c40041c44081c0040e43c03140c00d203003090f01c842402c0400390040c040d03201501507170b040c103a095010503400d010130090501a000340d486540b003861105840c5c00d403220075204450b00144c006140246103c0050410098140c1465000d00003e5988055900d4054006400180700500083c10952101e01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 850312356 1250 850311106 850311113
    0x9090408041d010e160c060e030d0c0302280c110d021f111c0c080c120a030b03060606041e210c090b090c030709091505240412 56
    0x703032405005000690040c400c0d20400003406000d0038041c031840c5502500100358013400011886007100a951660020b90b45107403180340c002c21081c442c5402c2c50004006015401200307124922852095072030040e110403003a8040b040014402410300c00c05d051288030880c003541c0001d140710f050ba62001000005401e0341000c55544806844001e400c0ba00c603c4440c060b500c0101c1c000078100c0c225513114401452400381a40d512b003201020b40885409580c0c1a01c0c00e40c1c450725207100040c3c0561042850039001e80000c0346031038415800840c03002e070b01103440c101541d170600500301111422402003c0c0c50500c6000245203114038411409142ca040b00896210004555540000c042c2c8070000c1c500e0740544040801d80043d0340c04100e41d465000036011942c801140f00b900c80f0207001a02c140050f603620009180540d0002e040003051051560340041c0054a5000d041340c070802038020103061519103070034400c120109000c1c0d5005044410034041c0c00c0c17141072081d01c04491441080c90010449400e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 850313606 1250 850312356 850312373
    0xb03150a060905090a021f0309060c1e03110a0c0f120c05160311044b050903040b0c2b09060e0d06240e0412090e131e030903060b060a05090904 63
    0x180c0081580d81012f103844081d5030001e22880800e242c50b8190070816034007000403000c503500e071002595102d2090206a40c001d21500810f041c15210300308511340700750140c81d01080c080300003030103100140708001c0340b00c200442848204038243c0700d40300c50020203081d40c1d5200001d05034200e41c5801642d44008544461880744100f10b114094030f0310b0542000700440c42c4c0c0703540b030310400c400c00c6004070211a444001201849941e21503007112010354101802c02d15080c280d507001c0f15540600d4411000038440045c000c160040c00d6941c81003030b00407480341401c40035004190070380c896030a200003802e10300b83d1078943c1c0180054a907032061000445a04401130400d15500f900e03c1129801c00031400030580c43c500e16410340c0030314040c03801040482071882c0c04541c1e1100750301602080c80c0070903010030000c1c9481c030200018548500001c10407054040c0d0003680007051030a00ba000a44104400c00912610744211046001c080d5851441d19141601c01b400e9071040c600f4080c05010068002030510032281c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 850314856 1250 850313606 850313621
    0x70308061903061e05070e01050904020306011707020303071e0206040f06200705070509071d0d142b090e0903040f032003031201090b03150a060905090a021f03 70
    0x280c00c21402401501c8a000c50300d450404c255218038050120304480c5c015291000500c1c0305941e8503190030700071802d12010b50405090b15040c005002a0707040070088110825120f00d1042d801103841c3d1a100f10003c10a509940031204151103021444601c00e40c041031403039201c0e030011b111096554261400d8001040303a0b445224041e070a0006002d11104400014046280110100d074445a2540100000e105c0d050341c8200120701c44c4d102200900c0c0751403200300c50f500d1004051900800e540d840d1041180c3e01c51500d00e1540d0407080318000c01ca244015a807015010601c2002c01c0807422180c040d00d51f100c03a005d4902c100210b0000140500703403c0080318003038024080c1c0901078940e64500400175640d00101c040205507040c50340700c81814000260307103041034040d942c040c00340d02c0d0011140051611202d040e0709406010b00c86280d000d50306042034010789114000207030039480c0c0215801121006016a106030b004024460003503070b82e094081400109043e54060b2192511005a00800301c0703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 850316106 1250 850314856 850314863
    0x1a0f1b030a230a0e1c020315061206011a0c0307060e0d021005191e0518010c020307020f09060d0b04030903030809011e0507090b07050c15070308061903 67
    0x40c0018085034402d03420110304074022960822401d48240c510041d0003018000390020302c03400b00420041c035102021071174240300c074585926022141d13004a410041003004150039154a81c05102903800c2c040b810b00034684100d4060015035040402c10796244640e55440a1100341c0070680c4000e40d14280111403055500039810400001007074242c58a0719400e02c072800141c0607441d1008010a054055641f2400390340e4121255504204880001401c8009450002d41020803041c09640c1061040d14026050f0300030703281c0030381040070040d400d40c9ca58810900854206109032030043c0c84030b11500c2c10f4000115031424081e5a00d2011038105208141c0c05080c198000e000c0c881456000f0306440140c0c0d009030b890611560f200c8044500381c030b03400e00c4601240100b444140501c40c5495010035002080c03490301c6e010855417200203086681150a083e185070b00100c8502c0c109207804c030b80030403004100d00300181c204121a02c1c090306000c0d000308070500aa02c500c2008105141c94410600515403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 850317356 1250 850316106 850316113
    0xa0c063f0b01110a031809021201080d0908070b16050a032d08130318030302010f0e15180a060e1b19140607050f161a0f1b 54
    0x240c52500965521440d00c825580c0351600d900c0c00941d5214014008421400100428034150035640c11100f0b00424900c221017000c0005001c200e81442e80020407060b00e01107400c6440c1c0d410448032900300f11045483c00184901444c0c100f000c03d81c0841c50310b003221191805903482340301441562418401d0b0b200018018052640b0074410150014082c1001c181c0000000c081e81303212094004604282e040040040380c60400000e0000801201348480c80d071103458000703648982d01001e07011240f0b041d003046000d0f07511100541d6420040703100d801c1403004203100401c02400c00700700341440000081d020188905002d0f142000002d420458900049d600c030034100711a800c203032012074581102e010300c4c0c05420248040d20380d0700d1410b01c007441d00c00746903119010845458864105180d80020140da45c1041042c0140400710b0424801048050403540281001c2c0c0c0560b040b0000090075600406440440c40d0b05120f010035410040d070310340e150314080b41c03a51107560103001c0c0388080b40d03180030603901c0c403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 850318606 1250 850317356 850317437
    0xf011821081911030306010c0204020d0b100521100302010c0303230f060904020f12120f1b011503080a120f0b0f04050910090807060510170a0c06 64
    0x3005100e107000b480416641c0e42e020ba40d00c0c415019224030050703030b4590000e0300350004800949002c0c0e0040103a900b00110010b5440c01c0000812995000c1160140100d00c001ca0300c0d007810210010000d188169019220481d4a00b40f18031038107403440ca00001c0d040208600d520f074201400381c0c1c40708030301360403400951902c98030202c03041042e160200e8a010081c0b401001180650400c42d01080c052a40280210392003549607041c02040540380b2400c0d4501c1c801d21111003036815101009004e034080146081c0d56907141010740024040060200018a80c507000c00702036032207086007581007581e91000703a890f540c410011040f101e803280312090000043c6000d070001c49501c0b1580c80190710740c0040d154a1240b05e400000c020458804172801045d81c0c011321082403440907a5403003520780601c9030009a091030301c10346a0f40c08035041120202c0c2c1015205000b40031922510388030060302c18900004121030056030340c40da12040f0540c407070003052007030700c0d02008500411703100f22010024192a1159001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 850319856 1250 850318606 850318627
    0xa08091201061e080d0206360d09051002060714040b18010801050315010b090a1805220f12030b0316090f0207080f03090a140c0f01182108 61
    0xa8540c0040095000e4801000144d190000700784600b852100e50041c1200d655a80001c006001140d6800c14403a4030046a140c0381402034082d42800c650300f803005040d08000201c001e07110250790340045200700d000820304402075034001070031640650503141c198001d015170740407842c0e60f00582c1c2000800d420040b80300102d10031f030540c41e468059000d99655216903a124141902c0d0303005141010f0384002080014440e4038030100003070106210107000d0116035652007501420500306004090410344c5c80e5001c1c05404041482c661008501401c409501d021040d514180c01002c0c0795801410803001d600d14461a5002e640035400c001d2020701500d02d0040084440100700c6c7c2e103406994030311845c150b03113020895824401d45100c203900c1108945442d852807207180098000800f00e14491107480c1e15000092644004940007070741d40802080042500410000082e010342d0000e07041000800b01c03c006500082c201c03000310b81401d550010017a00d0095100c403141da040101414003080001d491651 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 850321106 1250 850319856 850319879
    0x60d090b1b0a14040e071e0f2a0b2406040e070e010207150c031d0f0d050106090f0b03010c0e0307210f0803010602070b0f04051c050d0807030c030501080a0809120106 73
    0x201c0801900061f00c80e03801001503900791442c0042c5070004203501407652080180c2405c1510007802413a06c1186054540d50340d6400320412603c80110034040c603681d210b200c1504010940a420499400b800c0504240084194800080c500010000c2c01c465036005a4004c5c0032100c041e01e0000807020910160802c0907000c80080c501c114001181440e01d2000a07040a502c440120402007600070301c04404030401410781c0110784151190b5580f0314000400007080e1040c21040554018041054100c8100f014210340b03944131107c0a011791030584500039500400c580c0c041c2e8000b09810400c0c130090150480f001c100782c0c8401804500c22042190901c110100658100c460342d07030880e0201529050343d14107502406805400020313040c0018000c03441c01050140c41842110b4140c421030078103449407031415440c02c1d95140480c0d05c44040c0821503505000d0304e107008150b4141400305524140b002c0b90b0321209100701814100300070a10500996940c42c0c0390f10f2070b4100c00c001340800b9880f0481201c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 850322356 1250 850321106 850321127
    0x90309090423010b19050319051905010b0406120c03080a09050d0809030f1603060c030e0d0c0606050f090f0c1204051f230c09060d090b1b0a14040e07 66
    0x305000898000c2d24604900710321740d00b56180a0701602d0124083c420410300948000c03021940d17130103213804000440d4409882c0300e1095015100106a007101030701804200c0f4960742000125160361141580402c90303a004030030441794050403080e030b00c000d00f00013101c0312219a0003169000900100102c1840307190400741c8180700c000c40c2035a83e40f09072180200e582d048800c2c40c0420270615000704001080040c1d006005a002034100410050521a80302d03061444900304070001c1515003090348140800ea1141c0005810160781005104801600140e01c84200900700850b0001950010f560b000f0984240c448580000d1402002420303e443c002c3e0b20f8100c40e03000e15206020342c05a8000c2042c181c014541c0340812813040342c00343c80101d84480036103c3e004040d540082070412842c0c0d05616050020201ea040e80f00000450b02224600444142c0e800f0b4182103410340342054030301c50340d00850100e49441c4102c0c00c046100020b9200b090040b806a0750000e039032400400200b00c18190808200389 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 850323606 1250 850322356 850322359
    0x1207120b061206130c1d090d05090f040527031c090213050403092c310c18020309010e0721080c01020315030f06090309090423010b 58
    0xca190744100c1030100780c1c0d0190840c405254020800314a502000f842400c903030501514190b140285c13915280080c45001c01a0a203130400303074104010b00041c083c81024819581464814a400400070019464458103e0b00ea0304c110b0782c034404036a9150a22411402540080c1d81e40c0d190300c01d98081058130303a0005100680e8201d003650701c1c4203100c00d103441401c0711a0760007407440484218440040c0c00601d0000c20890a05c1482000810b03500c44c0d00101014580385400d04032038501d6841c0c0742c034840303010252480d110096a00e00c0c0c01c0c0c0311070f0501185056200040352016448245042c0a002c4682c81d0740318010240144007181c1003030304290021842919400028498010740c61400d50ba200f240b441a56043c400e11054002d0303070386141d592801003a006e146000d040a031b40040041c01c80c0d201361410b40c00c0042c51004500d80741000e009407441c0c0d030341107005001e0618003034120035164071450718054420701803030000034204216829801004000c40340100d4031074541e006c2c2d2600804200c1001c0c2d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 850324856 1250 850323606 850323623
    0xe070f06020a0309060503010b030406020304051f061a040e01090b0d080c07030c0611120d0906060f03050607142a1f0b0f010909050405030c0a030e0a0e071d120712 72
    0x5c6581c0b8041c000f206d0485404240c424a160345644444000790806002121580100004507130319441c0c2c2a07102640404c010340c002003061801222020b00c3d007503013030803051101080c0800c1001c40c1180f603029044601d1a02c0200e0622408800038085a0401400030464000800c20081c000300004031502920b100307007554000d0075240c1c2c170103a44520142441c81d1055011120b0000c04400110140c10540049040450008820f68412080d0358043d08480340d0a170000382c0420600c0301c1044000d41000803401c2003c04440721581544180c40f6807400c000e2842241003202c100315000c00001c040100005094811145002c40d404074080e882000c450109070074550280e180d0318007403685184028058417002980d52902c2c020202034140240152024001404429400c1006018180d600b134403d6860b424411940c004000311003c4a80081140760011802c110b603454001304000300b001032100c60300d2040c018040000f4914a480c07100c4422600a4250010342c0214565640c4161031048414 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 850326106 1250 850324856 850324859
    0x100507060c0504031104110f1b0c090f0a05070c02090a0b0406060f0c0b19021306140a0f081b0d060801060806060a1701020f033405030a0e070f06020a0309 68
    0x1201c0600442c08054031700d24890049003460300e0a640000080000391201c1d81c101410303040750400680050b401482e0449402c1c00c0038501d17810521100c1c6224400322840c00b054107101211640c0d11000030185030f0b4996403000402d101c1800740480c0c10300e86900a01c00750451030b000d0407403006031032102201805107003050b1002c500300d4010320b14100820b00c15580c02410400e00c0c5c883c0c00008a02070410562021080e1500e01e0030342d0140000c2c40d81c4109601242c0400d0b1802000401c4d4090f8000343c104414410b101610280354094102c08601d022880c0c00011521a409420380715a1060f0480301c039448001140030590125800100495500350000c20500ba43c81202644440b030032200154071071103488080c000c00342c406900c1c64038149020001410049a144018071540c025102c1010f00c148196910792151414180f8800c0d450001e10100c03000c450050003e00580809801e95070304c580c8401148151301010032a0200414a081f9030b2503082c0da071410301940f01c003a152002c1d800500c0c01d550 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 850327356 1250 850326106 850326131
    0x5150c010c11030f2506050f100e060f040b130c020f0307050304060c030c0c060806040e010902130b1201060f260601120602090433030203060f0402040b10050706 71
    0x241c100c00b8550002640c5001c02116194109500c00200004120540d0260400448068486071106840343c140040c10b402c0c292244440c212000b40a0741d041421100305006c4001000c43d0707190000400c0e260700b42aa0041800039019025810105420852075140c0480f10201900044200a0980c00f5200307018800e503003031901c1e80708a00c400703030880c1e004000030025103205000d0300048074040e2514208407091540c46900741d400b583d101da4001500c080500800e898540700780b40c540c8096100030000800240c2c00310b03210b8034a9030041000b0320760361200c1c480c0d02e49400103006904903043e40200312090300e030012003c3d1b1181074040d0300740f0f0b8003145495600d00070110815201740c034460401400907038070740299050625006541242c180703030207001101e815107d5014810365040c1c0030703255250100c14462071f41440c81d804c40d50520043c03050881040940c80100d400c542109040d40c01820581e2a0300215000c1c14960711001d400400c07441d0a160500d03440006810010b21440c41800102d00020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 850328606 1250 850327356 850327367
    0x412030b0402090d141212190c0c061e060b0d0b01030605150721081501030614040509190803192304050f030301090e06241905150c010c 60
    0x394000d80040c1120721040100d0400300c1200781d0036201004a88102c00c201b009025260031110505007030001e541d060281c00b0312035441d41c41104080c20704c1000082c4241d20001c0180750443c0e030150655544140781503000070114a01e1007844600c0b40d01f0f002c11071340d0b04030501203035000d00841140540b03040d0510405621900900c0c0031200f0040049410400c0112401c94503804520100c40400403040e44042044000140030300212041d150400744d89051152800110045031045040620f050000d01143d20706034102c403015401030302d00181c0c0e40d86005071245080c0d070380828050301403c0b07180c1500c1040310101c0294410407841da6102516006a5102c20590300384030030301c5a200c0388402c80c001001c0420651142e115002d8811106a11ba00310152420750f030023038000008040c2c072034000030307500841040065000318003142c0c80e0700c00794041c1200d04484024940e01c68810900c4041c1034050308040901400a410700a180e0322021810311003072000c40c3d11581e44140d0319424805904807860051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 850329856 1250 850328606 850328617
    0x2071a03040b04020907170a06060e180c0915032a13030809030a23120c0c19080303010f0315020304050a021002250806060306010312031e050412030b0402 68
    0xb0355414081e15641d003000301c200c6008000d5001c2240c2603850441240541d1002e074001c0d140003000240e501e0a00c2001041c0341e0090070a280240341020b0310075003606001e0112580000d20000b01034950412000065111510b0589800114404018032070101aa03640c0c2d8684483c416050b9155045e0600b0140da0a0080600710b140340c80c82d0400810200304400001c00c0004d40040a80305042107550754920b4042e03115522414071fa41d0240c0c28034003202c1c1040b142c1031005828040742d0600311898031840d601d02e40c880390b5501a101044e40e00304100001401840500101c2060342d40380d603101d4070400c0300081d41d44416200d60800301074174048a80341d8030881e4080c0d504200a812040070b01e809002c4031006003a1000c04501c20001102c0f528204d443c4080e100e40c1c02507480c2c41100b4600941c040c944540900f5107482034111000410000b2410b40905008401c1400d001c80d504005050310961320000c10f4203048030303606140c20001003007100c80b443d01418620362030410850502c0310500c4200d0045 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 850331106 1250 850329856 850329863
    0x1d1003030215060a243207031106151504060503061e1206160201050705042d12020405011505090913050f10050f28150602071a0304 58
    0x442c1003203242e510850042940b00340b001d0007128886694111501420711000e10402d0300241d100d40c070b41d07600c542c001e40000b101d0001100480c600601d20030600c1340f51801d00d40350040ba9200140704010940074006142c804480c1409603030b2145031035417014841031614a01c10b48601c44400c6103064006041007914140e407010b5588608580e0703220280139421801c4401c0b400c6401c2e010503000282c0c1d6540c5d80780b03c401c071680405800d46042840342d280c07450a111400906690404041103101035208003a1360407140d000c07598507401940544440010000c0440702d01c420418660003203280c0c40e400461121061090300c00b048580c1e45d9616110070704260301c9211f00005c0b030402401006142c0320400340e80040c410401c400c0340d090140d46451030001e00d002c80c6403203038003d20710300c2620112a1250f0340c2e000c87c3d07403445d21055140070518054134921012204c41c0c010303504442c1c0100c24400d1382c0040302170554126040b450f5a11442d01070350366119031003a0307980b010108009510180000003640d0180e0360 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 850332356 1250 850331106 850331113
    0xe030c06100608041205070f0c060c0b01120f080d02040f060806010f0201050118021c05040c180519331404061a0f0f0d0902120c03070905061201061d10030302 70
    0x140500119038070347c0f01c8030b010f450051644003100c0c081100d02e07840c080103101c56151116880c00ca440c042c43d0184059008103034240305482c4200114002d0b14800042581c0007001a9460360744005941c002c0c003880e00a00da40c10101180840c0854101c1103481c01500c00340c8405440c44c1e15904100c0c00c1c0d950034082c0f4000194030324841501c035200d83d00905444170b151a01c80900c0e031a82400102207a108403030036260000e89400800c101038603890800c503003140350b600c184218a00340c3c0001601013108003002e40196610059510a42035001e0746a645142070800c02026650b407032030940740c4424902407071001c2700341222010401d14207031041908a4014400108405104121190031900b081920414520080140006081c890001424820600c00e00010030341058010f0040050402d200c0882c154401d5401041c941c0d0700094070412101c5403e0003062564500002c81c0d8070201d4040c04c04003035030038018003052890000224405403003035051341b0720030f5598004001e6181d00c61448040c0c0940c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 850333606 1250 850332356 850332383
    0x1020c01050c011e020a0f1701031e0f0501090233030a06080f07080610051309030504082406010503160509030102070f1103010c050405150c010e030c0610060804 71
    0x5010708007418a540c00301c07000040080f2600031004400c166201501c642070303400031b0440c1c0c6030360300072440340420001440d1074035021070000501c409401044c0400b60462300040c0c0d4050001c00401c1c040360803594421000304040c1c0e09441c00074041e01d82d450b41280b040703c5106100c0b00da0840d2903c1d01e000001c01d21403070401d580d000d0400424941c0080c00e5a250a5143c10022400780b00411146081c2c0590500501001c0d187c900035908014000d440c0240e0b007081c0210411850340c8001070b13520600c052020000e2400f40781c2c60203441e544140c0d4800ba90600611040c010804010000c00c4c85045020341001555500d20004445610045030080000b804424070a0b00d014441e50140480c0407000d0b0005280c8100340c0c81d07803048080700b45811180300300d410495020504080c016000c0890382402d0442c109820a00080d00b1240c410390840ca8507940072465054842094200c503811203c06002d899a03424102c0c0403039252401200c1c0d00254500340c131800a01d19100d000028441c9801c0070007001c981 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 850334856 1250 850333606 850333609
    0x720131a04090c08060405160e010b1902010b03070611060c0c0607050c070506372a06020d05060a0e0403051b1623010302040509070e010c080c0d030b040b01020c 71
    0x10942e00030240c51102034000c01041144080040b54082c034010001031031610616070f04d441d030501881e08a441900050001001401103800554031000710208250082680300c0500700d0060600c03964865140c271840c2000903015801000050386078a400c415114903a5809882c12001e125031040b40403141e100f0400215143d205001600c1807007402070603181d07a69603540c00650703650440d25200c440004204001030051801121992170102001c18541c034121070498080e11608080c241050300160562808150105040210100960012086450398444080c00c00180b1301141c085024400140c0c010540f158175103030652017158103583e09490400259003101c58200d4221f0400703020310a00c202c3d94440040030702c9500140a544550050101503065040c0b004441e04001030f050502c100824019515a051100e62150160401406195407040100c60780c410510001c3e1031f040d80071900032604500465001c0a40c07a181e41d00303004842c4000700700002c80394003040031400350303000b54400300c0107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 850336106 1250 850334856 850334861
    0x7140609060c1e010c080105010c0b010501030f0f050408040e060901030b01090b131a0901120f110f1915140702010e040b060a0c050f07030b1503030720131a04 70
    0x3003140107403ea82c2c000c65985102c20740000c00400d44510399456024043c20b46501900050040c0001d03c0c1200614207651070b8141d1142d418024541010303241c11388100c001c01950415950b0301c0c01c500c4100102c0c6014181607000d40c005004040c01040d20700c002c2003580c5050f254450607640c011000c2d0b041d6901c0e00c84200000c2078046411600201e22105400c0d9006892140c1910b080c1700144010079000104100403c4820507004004c0801c0007954001c003062060b08007191050748000550b0039035402d0000126100200f00c03103143e219006801d40522045003114000444900c0c0d000b9118030b03034802d6000d95a403c02c150344000b000005100c15005503201c0d6400809a0701c002d040001c007105c4080c082586603010900003400708038040c00280800c2000c0000841048608019055072421640c940744804405451441c506d5800b003030300140c0c1e0350113000b140c035100d41c803c0ca08600035280d88000c266102140507818458106800484051b0045001d50080c20302e258107440b001106180c01c0100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 850337356 1250 850336106 850336117
    0x390303160c0c0509010b0d2703050c070b1b061b12070909020d02070c05060c0604021e040f0e100e0607050a14031005030d03020703020a0b040303020c1b030714060906 73
    0x300c10550140000c1c4640304d028000f8040c3c1003083d1071030f9039404501c0602c0b0903152a0703054450303a04130700d10082c0f0340c80d2140302d8501040343d81890001c1c2d0b10040301010700d15015a580002940c1440013403000406079500d00d145200031010f8041c1d034526179400c449400c450403902c2c5c18540e0240200182080c0b0045440ca040c1d20941d181055640c464813030380000100d0700724041d4040c50030303030003c4d4800a2042a444140c01007504a40b41c62a10003c01d20032071f20b48402900007401605950303001c5003ea038148080d08804140680204802c80f000da0a00c4080d06000c4190001d6005007140c180e200c03113050080701d04514018005100c10780f2030003401c80d0607922071404141000380c180d400f0480d10780900c006600a8a9908021080b0742c103160415091521100a00702031510410030600003a030007054100010f43c100e0740003285c0b6076032070a06402030320403844050100c1c00b80340d101d04034100d0300c0c03440c10604030b00940486921039110340701c01c62030341100c10a050740114144403016080c60103100625 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 850338606 1250 850337356 850337363
    0x60709030b0a1d01051f050405061315090507030f0501050f01020718020c030c070914090a020d060905030304120905031b04050606130b1c05010b1e390303160c 70
    0x702d80c9030840300c2090860f001a146c01020312031114030345a400250070b100c00c029001c22502041a8240940040d401c0002003034003600254503500000d03044002251400b00400568100344810314240400400070300c009003100c07404902d07090000c1510b0410b00151f060000040e0018840d850424500d4000e8801d03035850366015076000c00003a00c200400344094141c00001c8401011010304106220b0309450340110140c0040810f441080489040000e230198038a405980303400b441075542c100744024005081b0040d00c244030010a010400800040d40058038040359140315030750303807079030100741c0c40d0805010000c4a9511761440b030784480c44d10394000c6801c40c80c010035041c50404030301480170503a920b59125030b034680c42c003050107040c01103083d216907010302d02e00c0401c0106605091700d1010380e010740c02d11f9003411103a461191405117611011030311440c0e6142c6500f80e8450013203e850200d1102c940b420b841440c1c03183d0f400400c1900c00000c1c0c070b00591140041d080864009d4000312159118a841038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 850339856 1250 850338606 850338641
    0x3180605062b05060a0506030304140105310e06103f0608030f180f030f0705030f070e130f0605010909060b1002061f05130e060709030b0a 61
    0x8460101c0d640b8807024194110344050700342c100c0203003000d03800c0240007800d9038841810407040000c030b90707004011601501c1030101c0c010b000c2070b00d002c01214580224070422501c241c60303406a01d412030b50303041030142610800d02219040c50b00c031100700c0d40e401010b4070800e03046800b4080c015100b038015240108016000003c0c1d44c44164064641080c1c0a0407a040c0760929500f488d00c03101420722409810082d0070000020740c504024140051403d210755903000503400c0d03184a1020056407994514025040c2c000c04541013000c10104040d2116454410700784240b14100051402c0d01d0003161160442c1c0c820020700f8401c1d641c1c03580b1000c1d44410720000b16005540d4901d031000091140c424180039001c15500090b0440840c6458022145070514044c07051400b2001040419800260640d11180030030b55410310391108402c55006081c250032441d800099004003400d81d891940c00000328004100803145240c4409074156241c14290102921501c203e0b8001428105960021034120401d403520 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 850341106 1250 850339856 850339879
    0x5040b030115170102280809061e0901090c18150f0501030c021006091a03031801031509050a1a060f03060609011e0e010305010f060815030f25060318060506 69
    0x500c906040e885254001704000c01b081c01015030b0340450390552000441c0018042030402181d00640680030248a1845d041d1a400007594481c080d0440c828007944005102c0030252030781076080304e841ca035108022036546000741c003c0d1014864903200e40ac4540891484142604001c01140a0010b100190096110785410703c41a40c80902ca580001c00c6c0e04a00080c1f010804002201d9035a00003401610950050100049030111b820300ca185401e024240090080c91002c030001070000b195200121040c03504c02042224001a0002010100c0b60031410b29031007103040070045035001d00420340300c0700e40003803000a15a0400e4001000105014100300c1c1e422142c140d164030034079200400520000b500420072102950301402003d014040070480303041c1160604034000c00c404801000040082581001c0340c2003510280402e420000d801816184805040d000010182e80c441e1842c80840d0150307d0b0004a0301d100b4803e42c01c002e14081c1c00241c04a00c59220b8201404029080d01d5011820704074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 850342356 1250 850341106 850341127
    0x3040614010f030209070f0509012109110f1017040c0e0103030c170436050705030711060402010e010e031e0a060e010606090b0d020d060f05040b030115170102 70
    0x1441402081441c02c42c004203421032061110072a400340c0703600c0034020f40140315080c1c0740e0850b054900348107003840d00c0c0c500110100003041c1d2200c00c0c03641450416142c801d15100380304569402030381e152020b0340c0e044c20b031300300b80740901c000c2c841c03110b0601000a9600b40401a00e954603100c440c0c0083c00340302e000306050340710020254907801c01e80c8114082010390407440200041c0340b03800300415995504050402d03244c001700c49012056031b80070303403203072510900c511012004a031441500000c102200b08614030b003041001d016580160751035400f05d0030b0010000015440000d0003489240c0c103940c0e041038400c41d0001500d103a10741c40341c25035050107860b01c00090010b01a0360807408000c40c0c8000c045034640e500300a001ca55260000313900e243d0420109104181d004a11141114507030b000b600e9440e5000114070f4003d0040c4110310741e0060030b1080000c0c1c0d0000c5a41c06006841003104c5c20003030a10510b041500300c641104140c061545a010308101da50f00000a044500929000240c6450b64a81c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 850343606 1250 850342356 850342391
    0x90627130e1005040510020c010e030a0305390f1b07061403100605030403020a0c030c030215120612070306230105180a0c2607180b0708030406 63
    0x24012500595a285441051407080094040500000000300842d081c0341c0c9132181c0302e0000c1c0c1c2581a4061b000106881c1d6840c0944c4001e03000f08038003080e40d40b100003110006000d84010307920641801c440c00000780c00c140c0703407140111174030170411610b40341841d6030600c03032007190085000c5403096001404440fa00101d03242c440c11142d00100090400142407131310280ca403031100690055000740030b104010050009807840c005441181c1011034903540c0e2460100d18103400980000d2110403148800010001580441c070250707032003100c3c1c9050810700c0c0400c00c0701a020b044001079089100300b02040240c14551400c010990907030301503405c200d480e078881100f5070b0b1903003c5442c1592041d100c11080305001a00460141c01c00300c80014840d803041c001d94403001f41c06044071015543c3c509103c42d41e42d0295040106a4110f4010110b11100220304203050304c1040f079240c4041200240c8240301c414400f041001901c0e2604003032802d00b0101d844490081d00b00901c101c41c541d40d01d10040035003d0000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 850344856 1250 850343606 850343629
    0x6070f0e151902010c090807050f04050a060503070608070e0117071211120a0f020a0207180f0c0503070201060504051e0919120f09050d060b03070506030c04140303090627 75
    0x40c3c00114218807250301c024806002ea40c0494140c0c1c0240c030060021756030f10010b0101d4804100c1c0c0114407038072201045401015183d01007540340c49243c0c000540340c0e800192051060300d9581315120168228001540c0d40190a41e54004100104000039611801000c00f0290000004400244081e00411450003035000041c0c60b4000d0401c0000c200d0100b0107402807030245403141205606201c100e42c000703551002240221507c038800041c0d030424103102c81e80003600030262640300744140f01c52008007078010351040d181c10b4019400c15001040e5402d082c041c10740103441001e4041c0c1800521a01030103041c070b0140c00410140103035112146085408031442190b14000e03103070721042d4611100040d1144e400d614082041c07006144042000350380d000c1540100a410080200342c042c114400242000b01c6a0049540943c02009206c001c1407041d0140050303590400c0b1aa503861503100405a0f42d0040c510358641c8070204100c3d1080c02650002d603030000d07802d414440801907450000040911800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 850346106 1250 850344856 850344907
    0x19020c0d11101e170a020c030a081f0902121b1b07081506030f07050f010e0d020901090b04061706040201110703120302030a1404030207301406070f0e15 67
    0xc6082d41030340c2d8108454101200400c110b1a081f0305038400c0740ca82c012036001200b80800340700050303200c0214a101e62019858a94094650794880340702ea0001d40290141c04190400600095a480000300c1a40a549003165049080ca4403105c0511840c00040083c200c1a010304ca00004018408100303010600c00d400c1c10410382490120145880d00e520290a90345640c00f144040040d9100c08440d289102000e00c2c0c00c102548040307006c142411210080250080061800003881d09a29402032880c21011182481410f0341c9101c2100083c884080030714040d005070303001c940158080d12075400e0480e080c2d820b0340c68466a94035030301948900a8a41c101080d000820030020760120720442403403600c2500a00d501d4101034500960b030b04030300e016001130165100000d103042c0b84100c00404050319614a0002402c001e850140d0300030b50305c0302c0e904165108001c04207010303034095010109450790f1070303803a05d03041c2d20807004100702030034a40c10288034010204865440100e45c1044440c85100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 850347356 1250 850346106 850346117
    0x302060a05090d060e0f060f040b0403210f0f0b06120916030807030912030f11070f03060b040b060909040f03050d050f060f060405010923030319020c0d11101e 70
    0x400b41c54a400c20701c5e0010003051b1a08050300300140001c0e5000c0c5140c000c2d030401c0082c1e001d030740c0e146800e84940c044e041c01c80c400c106016a205104103c680c212401400341b10005001d1458600e4281080d44c580188582e4800d00a02c041903010002c0b640e400d50102d0514121410584416900c0c46100081c1d042a05c44500000e2000103050f00b11811a0044c91202c00300260507101d5100180081078444401d8108440b0200c00580310b0410040c0c8030140c50724500c2c0f40c80d241da0724a401c400915400e03002600550514001269500e0301030181d032440080682040841d94640e502e5114460b12910b0440034484140200d441c00700403407280501c14414880441600d050803810082c403021100000c41c80740310200400e12559a0040d1100b0072142008000d494000d43c071240d01001220140030680c15200c0401c00c0880904030100c140c01880081d001c2d6220b400300d01e41409500c2c1148240949200ba4400e04180705051511440d403140f032052038850550100007505008922400d1000302c0085d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 850348606 1250 850347356 850347371
    0xc12130c06021b0f0609040506040b1005090117061020070e010305010f0501060e060901091701060e3301170c04060f080907090b01050c06100f0b0909010302060a05090d06 75
    0x40d1000d4500c0d21030f410403038410711200c0e4810000354003841303682c610740e000d04c0d1079001003266074445401140121100510030340b1441e4021800420540028588500084800c0c0003a445030548205076406803201400040c08000d0b58042030360711681881c1b01c1e843c401c004200c0660f4800051242c180a03140d00d0003604034039491801c015003520152550300300c0091808004010407600f001c0b903440d14880981d1507a454660700c10050b9591013256000c0000744a1203505450401b80644c07042c829912541c5041610f038032295241c500d8864080c112825105500b410200a00c803080d2000c14502e40500d80301c01c040746076010180501605076980c0c1c1d52003030b001c58240560790f0401542402d41103185000b40180c48c000d4101035542c01d40d4450050101da445094400301e9216404036181d00310030201f00e1b2003034144604131146444c040d10850300c11410042021500646c8407003164180e090003072400300c03c5d90941e02040031540c40000c0c0503042c00800c100004030f0391540600841c0007801010b0001f03500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 850349856 1250 850348606 850348633
    0x91e0106060905190509060303091203090306101401050d0605041505040b0102010c17060607080c03130e0702030a03050709080d020a020315091002030a090804090e150c12130c0602 79
    0xd0b00300ea00403901ca520700c003a1080034412900d01101c01c80b102101c10f0740068071048003103404d41c40f42880700c036000840d0662481c0314040c00001013010b80403d07800c4401c0ca5842943c440c5143d403140c010700030f9443c0002441412503114101411140e000c1c4c180004056a5400019003202d001d410754010311a1000c4c000c01207490300c1e00c6118032016003800240041c50000c003005010f08103000120040200000105005494400c00c1d01c08855105516541d600d0740c0f00f40459694004421101246c984c2c0000860100c2c3d2000d400c9000d81040e40045003880200c0c2019409403000030006e004000c043c2c1c0d80013940100401c81c2e510602c1b0160058441511680181030070100028030742200075444900340800ca18001650041c0805080401612512986040c50103880c02c40300c09410804003040104110f40154000c0e0812000f4400b1294034006182840400c100304480c6084c0041003840702880c41a080444c0c90361140c820b0400080340d03403559480311480b00490300904c005030301c850020000e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 850351106 1250 850349856 850349867
    0x81207020d0f1d011202040801050c070606090c08070309140601120c120c0b0a03061a03220203030d0b0f04050103080a08010605040503063603031504060e040308091e010606 76
    0x51151526101c0755080140c0000f01e56107025040d80c504004c424620013880c4240c07541614040c008031002845030b820145c000380007139009590291912468040f000800100034841c000f0129030585508089940d071709410380c01000c9040c002ea43e8414419245003050780d0500ca140e0180c01d87e2841c447c441d44240c180072901e010150840d084c03502d13030450080b011511000360982214000e40e240c6540701c0c071100c001c40c081c20175548401551208440c0342e980707d0721410083c51103000c1e00b501051514135000390801046018441c003940607002041078801146c41030b0800003107400301801400d030440442010500300c48090f40252900c100104601c03151039841902940140a9460401d082c5400c2400280d207885014244481d1038008010a850034443d0782100c840c1241c2c40d801500700511003030300c0c00b034407030744121524505010350b08500101440d05220348025241c00c40701e4920179580b079a5095030300c03a0300074101404611038607071000300100103025050130380c1c0c90610002c546a460040003130032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 850352356 1250 850351106 850351127
    0x100c080a0c0903020303030f1e2a0a080a150302030f01020901140304170307120c120b0a08060a0b0607020607050a030e0618010e0a080304060315121e081207020d 71
    0x81010b00d4034100f026913000820b480e08442041201c5907691101810082c000354403c410602044080040014a4141a0350f000c6580c1c1585c201102d00c103c0319410324600c1c842d4180d0080484e0301c61000ca0412610b03544400154910f0282104e610754690b00000c1c64080318002c042c0c090380d0001001a1035580c4600d180081306903c4e50381c5030441c1000e030703956883c000c21a004507240c00004070010740c4085c40307104400c001000041040129101d01c00c4000c01c40300c4c0400b85e112019007000a05045801c00300154011100c80300e026042d0358076454002006070a00301c020950050080c0907080150340d90000410a240c81040208003845041c5405096103800d41c20451240c401403000e02000d00310101d01c84403034017091034020034140d5800005055242581c21101007448003003404115540c0660280c40c1111050200b8012551783d0890342d00d44144405005141070502c240200002030b003005041561440341007814204001c02280302504a402c07516100164404100f071000310b0340006140c403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 850353606 1250 850352356 850352381
    0xe0a0f020f1201050a0f060f050a140706090512040803120606070c0e090c01030b0a03020909070b04080c09060a03050304051005040308070f030806010c1106070201030f1d12030115050903100c080a 86
    0x2d0289103003080c094004502c030702809060000c00038800c04100e2069900d02032a10713880c0b0bc41a180c0c0d0307060034504001c0c00e1086017194544201c008004866001d43d0580341210540700042d440c00c1000d4020012505c4080e0095401c03031424010100007840004104002d00240c900d5800c0a18041216074a01200031903000d040c11310344030f4492100c1d2110a40103054035019070352010b4a44610000300d182101c00e034000311031900c0100f00031411660104080154070801c980c4500c803a00c0b0390381040060b80c4c4502c0020080d0780100001c10003070500380056005040e09040450130103540e070729000039a03404100222034040800900e81c04254100c0f071f40f250818400e180100e01c1c540e00c0e07905d0456440c2e0052403144a120045405402c5a119411545050300d0504051101c0b03810845c07004021081054070b00c0c414020344584200154081003030701d040758114280c1c0750f940001c901040d500c90b07125080158041c002d0211103c000031450103081824011591894486c2c136080074844110703041c407980c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 850354856 1250 850353606 850353629
    0xc0909010207120302180d0809040c020d02070807051f050c070602010c0914030a0b130c0f05011e0e040903120207030c02041503020307031502041203270e0a0f020f1201050a 76
    0x801d0f15141c0c01b4001520180f042d0750001d1804250309220650740500da9229a10a023468020b980c102d901140004882005400b00c0349402e460b40e80903a100c1a01d801501e030010b600c1044d424000704045001035100c0100c0c02d18500e0700300c502c44401e091000c290044030162391280d08040b07200e0707132107096480100555094080f001d01e5600009440759015080035001d0072004001c10303085001c00c01403400007503001184c120416031310140f030012003810b482042d01040729540b010078181c001d0204200c1206079a900c8500440b1260b04000080510b02010b070100b05400c8030000ca030041c5440101601c0d4000d407a00d48801920307104102c1520709002592030800380840c0d0400c0141c900069140640354424002c14102c1040340908009004070703406625010742d00c50f5108140f541011400311205105d460b03241c0c81d102a0500b014100240307221702c0400410300000542ea41c0070316440b040c40c4019860026240c06004020fa28507508140c4400210511200042181d46060396550004010a8086 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 850356106 1250 850354856 850354867
    0x470a0914070f05040203060d0f0602090d052406011b030c0605041104060b0a1209020f040623031b10020f1e010f05040206090105070f0f0f03080f040b0610020c0909010207120302 78
    0x49149035203c0f2360024208102c840c103a000304111034040d100c00e4100688000e01c100c881d400d00c243c0d900b00582c0184040e440b840011480317000702481c0c9510441e0113031a01207490490248141d0540e01c0600b040d4100074032491441700145040c0a01c80c001e9008050701e1612000080801003104d009038403000880d50b0400581614a40181071210f404044040004280c2c3e80c45c000701d01d50414003402e10758071510348100414080c610211103007420304808204408a455801415a10f26802201c0c0300003140b54aa004024513040c007a410425580d0300c143d90340104e80c4101c0c10f05d400881000e24010000e0f07145002001c8400744245e00c413060324888188040c3c280341c0c000c01c880d48200c00c0c1640c1003100008841050040081c400e44845601c46402c141d510050b08200c0c2d02c1503144201140010a0301c0e002c144241c10130341c0130900881d0842002e081c42d8032010108031003007040301c1c4105c05501951a00f0070055503103403155442446248005a0754034030314500001040641e01d403e0040c1072040c0071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 850357356 1250 850356106 850356109
    0x302091e011701090c06020a0b0a1505060c032a1614010507031707050706240527040b010801230114010318470a0914070f0504020306 59
    0x41680c110b600301d5500b450740d05400c0c8541c070702614020b44050040c108041000a07801c0d40052000d1f02036000b202900100d848000d40101039036941d0080c8107520b00803100900c480d00c0c0201c024040012140122460550062244039245842c02000c84070308000c0080d00e982e281c014012140e800c00507103083c000003424105015034842d901e40e2068100140440e03508100350140ca4040000b00a1001c5041c0500d01458000e20079444070350211419424201004441c141105900030b0391289074200040c568109814010310380c1c6e280e01d0754084126000014940d0303420384203000d40214026074a00081e5170401c040142500c080c00b40e1449451003101414540c100340c01480c03415030351580b803101c000b1220900100e018043c102800741e0380200c42d640010030030040c0501c0c89032007010151415160740c1c85200c4151503601d1290380001c03041c100152002211103ca070354960148035404005108030058841c0607070041c03409440241c65101c00400e010b200b140e00740c0b560003080d04503025451854000f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 850358606 1250 850357356 850357411
    0x80714030411011106180709060305060a2a2006100623040b0a0f050f04060309080f120702060603120a05030703140a0b0f03391009030209 61
    0x100050012000380d1941101a07206080341e500c4c20507814201ea805040249200c202d0038101d0340740c545903200341407000174a8000c50017400116a00035010301416965403081c5800343c00d40403003240020100c018210800c0014104068143d00d0310f03601d83d441d5102e00ea08034424420390b04185101a03100204000318413446c0481c05059a400b841c0a4180300c46420ac8400c0c2c1c0d10b9200142d00daa402c02040115081485101420900c0e04d1a5500e100410300505c0c10b445501c10103511b4a4010002c01050207414000d400c06010188152070081c41d042c420200303c1c03155000712108c44c440840c2c04051150266040001c680c0140045011b0804c2040e50114188070384221006101030140100c00914054025885000f00350342030310500c1214a050806000242583d00c0c4043c400c52260a8101e8241000900503106500301c0902183d10001850318030401c40c0340c80c840c140300c1c940c5901100550b481305080803440c40c15a031503500c0498210310421034102d000502440340700305002c003800c00149800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 850359712 1106 850358606 850358611
    0x170a0e030a11030d0c200d0f12091a042310021e0c28030501061212030504050c01120902090f0f01060c11010806060909041208071403 59
    0x5907800c0c0c903805070340b18001d4464002c28014810078608800f080300780c03200c028402c00c1080000c1e234a038440c4000b80001160590101003e0040c001d420844080145c0112000d003400420450441f50315400b0b01d20450702045050700b0910b12960950307104038182d1754050421400c0041c1c200c80655a42c0d842030300803114001c041100b9200c500046095001031100410012a01c9441102840b9200861400c20f2035070b0034180000000500901c50400140000080954062410309105414000300021681818146400c1000182c4081424000ca40003401d110404880d1030320142c0c010520140c0003500582113000748282000d4048607540310756074100031404280c3e01c8540466035102900401015a82c08040d80310003580220f902550094001d407940c1d00349100400090301658040e139080e2500203800710b0041419500c1200c4640c0300001d07090660034000c00c58070042207440300 = true := by decide +kernel

theorem cover : BRFrame.Cov 850179856 850359712 := by
  have h0 := BRFrame.cov_init 850179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 850179856 ≤ n) (h2 : n < 850359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
