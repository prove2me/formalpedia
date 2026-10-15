-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5503
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:05:00.025231+00:00
-- url     : https://prove2.me/submissions/7c667855-0f10-4f92-9e1a-69e91ba432f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 989568345 ≤ n < 989748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 989569595 1250 989568345 989568347
    0x1b070807020907021c140c010c030b0114071104050a0f0603080307030e01060e0105210d031b020c0907030f060306140603071a121e04030306032120070e07 68
    0x146100d80c402c0c2da10141ca40d40e0b0000483c0c0360684840380d030000e888814016400a84101d141000c4189041031135850b15800600342421510300c0d4100c240402d40391680b500030780d80c01c5001c44c0c103966000b5610328544400e641d42e0b00440050700d900385104a03070314000b28550540710707070082c1c0d06594441010428240c030381c01e1001301600111400c0001a08110004240601c103014440454400c06001a140d0b42007030b0030005012140d600400d68181c07598808140d030f1030200f0019402d0210b5442c0020b88036074a41e40006401aa103003241d056500081d1071480945584c0416540001e240c9000175000c6200354800c405040c49a10280195050030b42d200740c124004802e0034081c4404408454909a0301e01d8102c4601002c0440c580000da014030010320014007843c4056841910b0b8100200c0101c001545e03200c080340141c405400103a56402e0034020403c980d040b40c00e9503480300340703c8100d03084440e6001300304000d43c0d101080c032046a600540e400d01c4c130030031004019005400f41d150061400d104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 989570845 1250 989569595 989569597
    0x90803070c0f09180f030c02060310030308180619060b070b1005091303080c07021203071202011503080c16030b1009020a350117010e12121b0708 64
    0x9810707000003440e200010f103860107100b10f408401c00d10840d402c9050311a10b8174000f0b10f45010303040e000d0210300b0716000016510381000318410000c0d501400da00c103080d0300300204891001005107980040051800710f445000260a59101c0044900d0131004851104401c1c06401c482d1310154410070301080502c10410000001485604010341c2d9607103440e13071541000f582d100f00707071500002e008101c034514002c203105d00709d00ea40c8940ba02036010b00d4a089680807c0c008515154100d0302901701161400801042c02007501695034a44001c1c004000c0f02c1c510506180700522000300301d83c0300001e4401161109200442d121a041280a410160b4a00348000c2049048924855040c8004004030388081603109417100c25031a40c2c1c1d035840daa012107411001d481100c00d8070078007d054603846c860040d02c08905242c042d04e000b1100d40906107098010740d0035580620007540e070340c4e081054490141200481681c014013414070140c5410386070301d0f401145406603000c052051040024054050020004c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 989572095 1250 989570845 989570849
    0x602070602100b0901050d0602090a0603020c011d06190603060e060615040e060108060f0409080a170112061e06060513143f06090705030724090803070c 67
    0x50281e0307007003024110303810b401c440610035001d0340401300c00018060750806c0301c580300380c8501c9202c0051170261280c00141110310983e1001001036000154001105403c1c01085000000c5264403003004801c2500d40d92180300003800d50300c2181241991100d8000d454010400450700010108600100d0100c9142c583c90f0031554140a40041c804030341942280204440888519018101513a2a07200044a054030003802150744600450b005a029a41c2c2d07100c1c4000c2c0b1172040c1034196545030024000f0380600180c80c03803c210707010100010031099002614030400035030b00450008142d00522007108451076a841e090044514003003002c514560484000d18440e00c2981c020613002e603487d82044c15000807002c0700ca82140c20b0040000c441d4400303800091464041c08010300440714080390400340842c10190002041d800750b001d102100c04280310a4000e000240d010344101070422580d01c81d54102e010806000307400d00b0190401461088000001410190781903035034845407414115117114280c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 989573345 1250 989572095 989572097
    0xc040f1410150309030e0405090601051c030c02040c021c0e1e0d0201030906200426031204111002010507080c04060e060c011d07081009030504091d030406020706 71
    0x400d001c144040c1038410100112980d94803480900c0c0b07030b00d031021409044020412001e2280299139000c01c0e560b40d0082070310400740200101900d41c5000204240034082c0442180356580c60b449400100ba0701040742104290103603070114450700401e904074500080c2c443c07030002c182000f054141c1041d038825403940c02c4100803034003a0701c2000c40062040d074100781c00c40140d42c4101c080d0b41000055009800100175240641000107080b011000d4022641e2100c543c400d00038100042c0070300c64000d04c01000c100106040f0240c3d00740041031070405580c1d02c1807003d00726a0311008000242003010041e40b140b2407a074081e01c03510213144d45280180c0030b402c00b90359100119201c00c00294100c9144001d8030101d40c440d603501304008840b182480010b52000380031403c25500c0300d654111003400c44916144246c400300007440b0a620384448a8102000d26041e1419142020f0101022a42c031000356010313162404000140d0307806542c04248040a200d90020041c04046000180d094002c0340d544100c2d50b40d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 989574595 1250 989573345 989573381
    0x30e040506010f26010f18090c061b0c0b030901050703051006030906060b2d0405300a053003070513080a1b050603160e030c040f 57
    0x14004000030350308100c4001c0e001032101d10340c4000451140d0030030984520500080c4508020b0748102d86081e02007600115038013150b1407010010002c03102c03030590808031064001c115140840c1d40700174064441d80300d4142088004041301000000224000700d250350f100c16042161550b8115840d29900200d8045085510700000210024003034040c6a101e00c54005003200300340d007025030a41c0280151041a603800b655004086540b4008900400f2000040d0f845a210307400c20641081081d0a6158401500036051104008076103d07070340c400d820511446490700b00110415010b0301d0034820100304610a01c01c1540c6c420501030041050014481d01d0203040c0d602107140343d02e10a401012903c54400c8100400004000f2445a80036002c1060b41400a40602d0b9680101900e04994654180d403102c1c216440210440310050400c1c000300816903609007546440d0520310060312401e80b00c1c1d0107000d100c4244048a90301401000e1440c81e00400c10042110701101010061884404a04030748407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 989575845 1250 989574595 989574617
    0x20303211012031e030e070b0316020d0503010501031a030316050c0411071203150303050d0507110a1101031d1e03030906150a0b0703051314010906200102040e0403 72
    0x500c4528110070b07560940c54400e00800d144960b41107544030b1000c203a04160b40c2d070480740360078102070190300d0080c0b21404e0502c4d16411b250f40c09034481003400d1018000c2d94419a60b010400d600101942d044420900700003a0b000481459080026003103d4003030750501002805100104004907a42d5200c0c3c051411541007024600c144000c80d4100d5860070030182044c030000f400a2050f100e0711207001100e141c007240201548000001710fa60765041140854000f2544402114981c81880d07802040c0c0d24100ca0720741e0b001e42201d80c40d15090140585420302120004406074001d0b00901c900c520300000f140724501500300c60302e803100310584101e503002c80341600d4892503110000541e4010040c200c0501540d0701d41704628034000e814601201e40200008074001460b210020140203401c1c0030383c03191507549070102d003e0110a5401e822064240100d414441d003c0d0740d0104140e02920700350f05104260040f80c00300107600d01511412000198000078002c56244c4200300c850b805a03201c0c0e141c01d41500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 989577095 1250 989575845 989575859
    0x160b0307050d0906020c060708040b0f04080a05131503020a35040302010b04050a0b030c03120a0f020307060207110306010b16113d02070f120203032110 67
    0x44816114100019070602c501d44075040294018081140b09030b1006240200214900341030800885152000c260302c2000c001c20301410158413644014007038600c0065240556428800d030080000c0d103400c00802103040c40c001c0e0411072003000a0010060310090103501c1c400c004020b13500101500e0300003614038210500303442e400c0450200d01089400802886000c00b03603170321400480100194115034803502e0b5001e443d20b0301c0c0714040c0601d01152010441400c80c0040c10714001240c000c0c0c1d03000340e001902c2c1c0320851640b1002e441072200c07103103045034244a000783d00700c0c510300a116016010074070006060040221324170070f060115405809840c0076a0b6141c904002d03e00902c4201444034135030500890001d04148820511040000e20400540c001c601c028038034000300c480040a40384c807211a48050444892211610360b40c2e910041080c14200201203028080301d21503d491031008011001c1155414000c1c5d0780035208801040d41104101100c40894110603195014030303440440c0085160 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 989578345 1250 989577095 989577097
    0x815160e0901142403010504020a17010608010e0106110d0e0d0c080d0f0216050d03031428090834030201021c110a080c040f0807080d02030406021527160b 68
    0x180504001a1741517030302e843c09100296016100744c00400c9010880f02c5102c80f02c0611007400ba007140c0e6582c04083d13040c811006090340c3c0680202d814018210000c0c000d8200c0040c00748400460743c5000c22440c00c2c00000304494060f8001c004000d05a1928003140b50100020b107118204da4940c3c5140031103916100c11390f11100d0299a40c56403454002007400542800482c0c20001d0b07200380f40010b07004c035034123940303280b03001007a0303004600d0320000000404002c0c8034500342100042c001d40200003014582e59030141921954840c3c0f442030310100341030910f0b000385410f1180c40070a20001d104900890b440c00038000c0d80b1045101d2003c1d180125088124900c0e440380b0705826007c006503515010800e4003e480c5118010310003001000d01300000318040d9007036a0120011b10a04009254803810030105508200d20030202c2c1d0215032003403004010301c0d507000030f08280d181c1c10309a08104641300c80035030804010b010595400300c2c40e010405c1070240280010b041c2d40c01280c40c40360301501a110101c0c4540307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 989579595 1250 989578345 989578399
    0x19060219090f091a060309010b0a050406050d14100908070308280b0a0503030406020c130203131403090a0311030d03061a130807090903090815160e090114 68
    0x5404516005104442050784007100e0140584d020a61002c0c40b80700007142640111040d41c040c2c2d4560306a082103085c885013100c041c2404590601415041c000810090a0921000f40c0070001015041908800901c01e114900203405000e109502079410402c41035401030108500045d0251b00140c00c09901d040c90b6940c0c18032015607030800c40a0082d00001510446030707496400b940400e00042c96030380400040c0014200c1c0d40150210340c4d200c0c4100400303100b211544500445c0100200304014541e091010441e0307920100d0132030031350650402986103000c0c210721142c201d9a40403000c0140704583c1000e460701e0808601700e901e001202c03e000c800303071445440745040034184854500a1902c3e0440a0160004500100095240d507240790a01c2c005080d07000c600031640d9161710700145640000c80b00701908004000380f0032a03034005201450b4000040507000000b2215402d411424071483c04c44409000040030400340d03517102c0603d0405000c016407aa03100f0304041003403403180c195041c52000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 989580845 1250 989579595 989579609
    0x60213030807151b08090f06070305010602010b04090519051f051012050a030e132a09060c030509130c021b0a030b1501020102041701020c0c0a14040e1906021909 71
    0x103101071582000d8032517100280514006004100c44580c202e0f000b000001c1c400d0303c4543d00800c055141090287c00c580c0312000306030080b4209400394022a00000b9a1054400c0c64512060500f02ea82051414005e0f800c941034007144448060716805c941316004980a85428164116160360780e1280030340e0040e0130503000b04150480708290300401d008811501782803101810b130762650074490340c1110407103510f18203e01007040d019a0340721120a82141514101581d400c2c0940c0700d03402d0000280200e100c40400070104500000e0f07080b00d948880b4010444014000785c14446400240e50103511000081251850031000c03100300c030241e01d808411102203d422014803c1c40e0b40350000c50455100d10312000a041d59000c00000503c46002d00c60003090171900300c00141c4481000710410b040c032000440140c415900e00206103e1080c05038142c422203407003210006030880f0480d010a0501002d520480003c403010590b03601404400e400501680700c00b501000f010901c2135205585040b11409191 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 989582095 1250 989580845 989580881
    0x13090b0609060f060708030108010c0203070b0a1104030c0b1e1e0f0909040507060f092d051c030305130804030201110c10050a080f1b0706021303080715 67
    0x2944038280081c1c515045400900b840c0d0348001050080f81990780202c1040780d1805000004100410003031080008401d500e10240d85007009980b1041608400640300180c06903a504175861009909001c4038021640511038540c1d0680e00d0010707820f83c0d0003000b0802000e003130307401d159010a040901110b80f000c9103116449404a40301c5200119508440403c41c076105040001d071302c0603552032040070f100358800c6009200301801c08500170300f80380d1281075110a00c1300ca041c00340b0031283e843c1d0b604142051041c1c2c5803c54101c000c44509010f000650155401c41044410b43d00c0f01500e20801d0b841607030003918203004903201c0f000e030800404103d460180c0140c409000a0005611171001c0c40f510301d441d40e08803801e0740344003030000b1244001001d0810224100160002d4110741011900b03070b000602004602c06460149100b000548400c0c0d100209140d0000358042080030030307030664400354003800350407003803d481e46852411940b00b45c0b03060303030701c0241da108441c9100e200d80110114003030541240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 989583345 1250 989582095 989582101
    0x6040f630c02010b012a080706090809010f030b030307020d080d06060807020f070503070605220b0301210506010620060a05100f06020d14120915150102060c0d060e070e13090b 77
    0x5070f041c511b130110080310001030800410020031240e025148903103014448865440c3c5040e00007421608035030900d0b03c01d05082c00213000c1196400f01c1595411901540e8203103815000c3e1800a80510504d00003011042c0b8191020031020b42c0f00c2002c3d4400c50a540031180c0c08100c26421568071901449060391560150805104c00c40c81480a080c181441075050311b8244600782c1910802c8440390080d103802e0310040010040c1c00078001012054005011442c4115034044d11019140d013814003840301800b00302d4400502d402030b044c1c00c200c03e6a030380000f9210f26040c180d1450024000c141c40303e01da0032200801c0420141c40102114085038050740091802c3c04a040c1d099070328511180c0100042e04040c08060000e0718160b1036030748603510340c0004e407412004010040350303002009060922840211542c0f91482e98001441e180c1016080c5546a2520041841c441c05005580c200181d07510982062041e400c0e0080e50312903841004030b60000007004a42d01c480112000ca00014001c400800c1c08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 989584595 1250 989583345 989583407
    0xa03080f160f20010525020f10170c0a0203040603200301060f110609030f0c0316030c2d0809010e06040f630c02010b01 53
    0x1000000c1074440d50741032501d09030326001c00a82e0090380540e031042000c807249207210070003c40380310122000d0810a0810282034150080c0002060b00800c0c1d096480081e0f906540d200c040c0740403210002444814201d0328644010000d504c11070203403d04000e8000810b511184500a44888441d01c0d4000d605080c68540103c016120741c05810600d410301c00000c200c1b000e4600000d5001c2c0a42d916218a00074002e2002462a5554554120507030483c0c0305008424001208030780074092401e440e9515465400075031400c6128154a441d8050b03500500502003503000394035100d100d401034040307402e000303075101d020140880c240307007802e14202042d80c414001440c620080e014550061401415035280040400c0c0740c0d0707006c0d40049030310803003230309007008008162b4a40c41d03c0101c1030360007100480b04a416280000001c20749108202340407460311040302e29414000d4025842411002c1d10f01c000002b2a2001001c0c1454510015402c250301d14013036500503201c1d0394179110041440401e024500d15 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 989585845 1250 989584595 989584597
    0x1110a11010818010504120210060303082406040f060f080402010e011101020c071e170d0804021306120c0501030c0c0201141c0f0507141603120c08090c0a03080f 71
    0x400001c200b4202c2d01c800040f80000d12949101e2841000038072030449602d03070080c0c90202c91122500072582072600505c000790f886080550004004180f0401030200c0808041c09150420030f119000040031030000b03140355503004002c1c21260302d91284880355440200441c1c0c0d8400450313001c1e000c600c852156034510351055200128529015000500b00124401a5818003c0d0780d03106d008064030904542d100140401c100c50300502d81000a4130b0401c006083c0d0350b8807400304121074000d00030004002415501c5154a00f4a55403900c3d10030487c003a100c0080d280a6010904280c034044400c11006c26103501a1166481b0740c102500c45e14220b078015401195100c42040040300c807154140304501250341c103007115811010008501142c20108140312400326100208003c080085180014000b50115400c58018002001101c01c0080d510b060039111006007942c08054645041c0c50324200c55803040110340203001e07400907124034180081c100401040140005010003004201c0d07120490a010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 989587095 1250 989585845 989585851
    0x181302060702100207080706020a0b0f060d023d081528051215012c070c30080402040e0d1701060306060c020402090f040e030901110a110108 62
    0x103040615101d802c0e400304211502030460b440c0540d1120302e09200300b180034444d60300581050302c0103040703076103290301c84a9008a029251502d040c40081c042031042d291032026541c2aa0080d045005680c0300c0550f100e1225090b4041000f001c1030b40341042d01100c00882010380c2407441d03945455240c1c170ba540c002160704a92801c00c540c4040c01484c11002040000901c880d50026120b102c840c1502e05030074000203200f411000c1c001c940040346002e40c480759001400c0c0c1554403400e204220048203c40800c5075128042c0251203246003602041111a03200e00d0001c0964480c07101802d02c2c10b040c2e655039445081501041c0b003800071641031107035940e00c19154154802c1c00100b022401000303500c00a41000c0042030b440000817481e5030980d1101c0045030a0600501c1c252608001d00e524100004010840c034000081c891500010140d03001d070f41e0700b580fa022100c1c0003002004000401d103000d07580c907440003214601040741003480d0544941d000c030b01c8100356a0001c0484144c44101d600441e4409001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 989588345 1250 989587095 989587099
    0x6091b1909050c09090603030304021807020313091a01030509032508070501052a03181c05040503010b04180605060307080f030a1d011706060f180f181302 68
    0x380c000040e0031401806040d01a19030360032002e6550555800b030042d100c1e0000d1800b4005c0d0310401c20301c00143c03500b414240e000b820804801407292503030078003282184911041e0600b801100d5001240420280d804191501c06014200210346100390041d003c1e40d03012240354030a81c0060100100c00000c070642c40c00030400703040410081c01c1949d6501c8100350040301b4242c51981d9103a0820060400c40451a00c1c2040860142c4559403a200324022142c40020040c4114400d0481141e540304410060051030515025002510801900008156820504c80d0b28425820844081c010b82442d2048101680c5110440254203106849440107040081c0c102505403089010000d0007150500c884a80e2300c001e4000341d07907140d12845005001c200007803600607032092070500d000401e03030b00040c03940100c0c0e80d9264560881c0c4e440300300003401405194a1100b10800c0052094010680c100d03003111050783c1154640054090401031000d060300c1e0450520001d0b240c480030a103038080181100c103a50b440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 989589595 1250 989588345 989588389
    0x60301060902040b2101030b010b1b0f0d0f0905030714010e1801090c0504060f0f03110a0c0506090316080705070f0909030e09092a040c0f0206091b 65
    0x40c45034001c089910a41c4a0855040301084003401200e440750410190038904503540215411912046e000f00010702c50003400020010b9001204103549001d107500b0b5440c1c10554080f10070f6500019114090000442c00203510604d0450707640b4040c40506060703600107002001070702c0c02c00c5052400d5811071030303246050003e0b50060b12040d58482e40010182f140410803075100754540ba0301c44060b00c3c940b20b4108103026040c0820f1062992107030481494800a00c2d1007001c20404075001d800901120701803a0010f680000c40204403500105402d000034031540403102d450703481d0405203443e4012a0b1070040c900c070040592501290040d0017500300a405541940c000303655601c56032013041e40030380c022002a51034800100503d5042002e181c0f400c00140d070040e503903180c4005000d80707510b43d590500c00004c0701e205940150345400c001810110202500801c81c0040798200a040521038001410040c416640040d030040f4000c41d949103511802c03c0b1301001c818400e010072000d212200171042c1e801c0c00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 989590845 1250 989589595 989589599
    0x703030e0d060507050a0207144212060d120f0207081f0c0c03090b0f0f0a021516080109050a0207061506020c0f03121b070306050618070f0806030106 66
    0x20300c0383e14010861911001d0340c540011a011341445141d901002c20a21505000d4219480d20401941c04900c90310b81584101800c1020100078113408001032400503202c69003022000c040706c014131050724280324401c0140d07261401c211300f507401d501d030060510180d1610140c0d5140200c1140c94404d07081c0c0184c80c0c24903121501589402941c019044885050154142c000545442006804521840d042006145944001d0101040c611501c038444c1d50004007e1101d050110a84078011081071410340e0340c90789490000e603210424002c14007407c2c00d42002c6000c0169036202d010261105c2d80340d22000ba8a0078005c04c005200c01817010045540030020341002942e40e102e122a04400011280c2c40a0304222000b07241c014188041c900401e030104a0750b89560f000100010700340f0899150a9640d00031400380010484241c881c101076116030300d800b00800c540d54000500c81c40094071301ea0034145000c2c20078000d80b00161001c40200300c2540c5412102c0344600020f03a030003140540042a80c40d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 989592095 1250 989590845 989590853
    0x1e0e01111b10140115030b2101091502040305010507020a050c04050a1803090f05010e0d080702010201111306030c0507030f0c02270f0106020a02130510170d030e06090703030e0d 78
    0x5501c4040103d10344416801030000080211040f5600716062404021528041004c504090340c040700d0304001550041400c0041c1d04d094114000c1280d201d031868000c800c0d9200309001070340160004607055400d00000580140c400103461280319007040c010a5495110000d100061038094141004a0b0300c03001e48040384031000041c000700620a5450070301451515040d82050b01c0d880e08902d04010141e441c43c826942c41d000d001038a00e8001002c4d556038920303440140d004080020316200d11040105001410700542149001107502584083c001d10401c0306040700c451141c407030001e02040744000803003100d5205400c4000c801c0c2c030160420f90b459512410345003030048400391000036164964100b1806c4008040001e00400050000b4a0b08a0540c0d00046244040d144480c14550303079000003403202c0c17169140c084020b10b200c0c01000c900301c12104c0142c0d04d40b500004281c0101c0d0416201803080720740020203d10415580300580300742070844e50116200000b16580c640d1003012099500c001c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 989593345 1250 989592095 989592101
    0x5040f1e0b01060509090106090b0418020c0105010b040906090b09130302120c0307020f030c0d12030f02311809060b060c0f06070f020d051c1e0e01111b10 68
    0x1070150fa0700d50036201c40d18141040800d00050b0448010844201c0b400c118400c00202540d086d80c860030700b03250384100c112110500034015030100580543c00c120001500c1d079003020041040e141031000a00409840703001d080261004200081c4c3c2041c40100010b40c0200c07225500d01400340302c0d10641d240600705100203d001d4018030007810040e08001000b0781185005e4902c2c450600041d4058690811300c0d1000440007e09400003074006462035902c0c0303185d54420f0b4004041a0094001151992494038981e62914a07082c201da6002501c403090301448445001507000311a40c041c0703500d49103111101c041015221114040300d400c3e840300208035140e91900040d1003103ca0a000510107441003134081407401c1006401c40c42030001d108421940c0381c1d40440c40504000c0305050032540d0714040300400300000c1225404070185c0303142030900d8a045191280d032112480d0f004009004810b16074100070700b01e410315140780c21950000c0200500049008180342c42e15a55842a29095840c1e42c45010039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 989594595 1250 989593345 989593349
    0x151c0504060227031914030a020105040c090510030204021606061203140c030403110d050604050601080c01030606080a240303050703030507031b140c01020a030203040c060305040f1e0b01 82
    0x94640101e5030030340c00c280b081d14014581849a0b6018052081c50700425103d980011040005259801117034040c09100911360b842500b2010072643e43d5240e82100a000b840c06075000c0350021a002c10011b0000b00f1401158050f000c040800040c1ca865035080000030360201000c2480c040c8035048103804207500b41314440040c10150511108a102458003c240c051040031010344407005001034002000b001003950b003a0b950012040c900030080d0f4000070f1222005c404000c11a04c164010030040040206565040329200300481d0000403801c00190140c8045d80210300c001848400010a4084d0a4100141a640820054040001080c1c3d0514035050580041e4045000005c2402c201036141c41115881202441d0420540684000f620300c0743e000035900004000300400c40c4441c1c0e035804800c0704c030802440b40c000c541d40c2c03248490183c0a0741041350244d9201040c148001080e5009009052040e54085a800c00742e509540d9550049200090515017010f21481b42d0b80014007001c0e800c0740 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 989595845 1250 989594595 989594603
    0x18041b080a1407120f0203122a061303030b0a032a05040213030b071404080a050c0402040806130f1b090f0b0a05010f02010f050f040b0f06151c0504 65
    0x45400604000160b451400e8180ea5650310041c1c007007140b0b036105007010000c50751180c2c1d0703000c4441d41800040d14007060070300c2d248800319000501d84400b03415140030b082030300201901030780c0c00d0b4910354030380b61500d4040700c603000d030060400e41100c0040c2c071030b0f44505223460700282000000358490316040050081109002d598400310781c4014112400d091103000100401c490541c5020802103a0a06442280c80001c1c4107603800d60202d16401d00405505088000c0010f020f9112039a405400d0780d1003600030780a407524090107524240d1410507008490a4654410052445485085898542c4000000152a805a9450346030300041402041c8804102c500d18004c018905291841e030442d214001d01107d101c1c900350455000351168032a0100700d0f0b00c00d0800403030182c0040b5003a4007415080503c402418941400c00c2400c90400118501550042160042959507492110220714055806039404007007290807c012520440003015200308a14071741481590030302c4084143c810966040f5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 989597095 1250 989595845 989595853
    0xc130e07030804030c0801060609030206210916060503040b060f01021c090f060309050a02060a090e0a050a0c050a0c0f0f080d0603050c010c03050409020c0f1b0f0103060518041b08 79
    0x2080c02030017800c01019005480c02003103001d00e41038014128440d13912000b8000c0c000850400b00ca0030800740201d40b200700c40380a01000e0718042c910151201905140d01c100c041e015079010414500c1981500e00c40c0d68030032a0908162a904d08104040e41149040c90441c410820802801c2c0c1455403598002c2e41c068582c948a1030405024551020454101004140c2350021410204a0003c1c403880c4258042e00d16030350b1001000300444407c0c00941000107651260720a00905003910b900c00d6110b030b020b0710f0041003000c0040608a4181c41081d03000800200101c0740c0401041e03246810782000382c400c514130b03a1740301100c1d507500c44540c10850303088840c1e6650380e408005125050001d102c0020f424a000f0150701e030b0340da0b0060242e0182d80110108582d0108031022407143c1041080c2683c46840c0c212030b80c1c400ca4991043c101617000310301c240100580d40840241d54001d018040560700003c1c4042c0064494900c0d01c1c1c0102c01c010025507401c2c0040ca1260003500c103400519002e050b902c4050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 989598345 1250 989597095 989597099
    0x1030f0c0b0a03060807150f1409120304090617060403052b090510110a1101060f1e080115142d010809060f0103170904050a060e090c01020c130e07030804 68
    0x6402c21b01540d03c00030400c00000c408010007a448040b0000712912404c090920013040c691680440c05610502600016800401c511140000024004071400c000007400307a9074272180e40b00348400d01d1707496002d8541d2040c0e01040001e4040d002606001e9040c08010322255400c0c885080d082d09100742100d0741035500c41c40c040900805200002c9075078920802808105c40e20a030b0001e2500c01c0303d50b40f4080010040750540014800c1d005400200042d003503842904e41c507a500441ca1803548080b80d40031007100c070000608420103005a0311051094a2403102003890314001c0002c1320201005690301c005019074451420f48998214001111822041341c550f40c240c1d0005041e940014048076000d512000807c4400c49510b00200c1c1500d40c000f0189248000102c54480c02d40291100684d200f810442041113104e0746a0001d02102c45a000d00090307500c03902e81c0180c81d9840d40358201d005030000f12041c030702c0d4184003648180b03501c40c1400004840d004d48541c503040102507002180d60140000b82 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 989599595 1250 989598345 989598359
    0x90c1403010e012a02070e040515130507050402160c06111605240403061a010e09150111280209010608011d040809030604030918090b01030f0c0b0a0306 67
    0x680c000300d190400200035a0a00702e00500855101c040c0032012204441d00e4560045c0c42400a90014200e45903c650709003410300c0d010380c442c0c59548000d0401500039000520304400000c0e200c0c2000c0d040409441b80700d040805210182d4020090003c5241031454004001103000681e40020010b60b50703842c81d8503901085803130070001a841502c4c011948100d007030203595200ca1080c1c0200b409201c1000c000d0312a2480405140180d500181c50703185441c2c00d600070314458806803803030044242d80b1108824204800c010702c12034242c410034114007623800f101c0740c00d50203a004407440e500c01c0c1007168110100c2c4610201d07040400307069a901c90160201a40442c2401400a805001d00b4101141198148a098000da520301c940306a03036000c2c0e03180490140322000d0112800c103100a0240c800b40c1c50f00381070251030200c0300d00c19220406d00300001d849403251903200b41001c0981c40500a00280d18607100c2505a851514064500c2501c96000180c09a45c8400405d0300c042c09850100c1e0841c41d01003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 989600845 1250 989599595 989599601
    0xa0206060405010b07050331090902011e050d0b0105090604080313090603030c0809010c0605010b0c0745021605010c0f17070c0c080f0c0a05101101090c140301 70
    0x403000712111000e10280c0002040807082c1e880301c8038141040c2d40e03458100103d0000c6420390012812188e040048003084e60125038001070a41c9000307803900d01907052120140f1141a400c40c400c000000c1040c000051040c00f0f43d000030f81e4100052410340d04180c4402e0005100da841548000c0c5503034400141e1680403e659180180244824441000080d01e142c5000e0451707415624020030190700011100c03a668080c180340310005412035402c00c001d40e12007564109550125101941c140b250300400580d211038170b03a0301d10300102c541c648040c020124010b1200003400c0c411a07a0a03c041501180c8401142840604404d40441d40c000c41c0c02241414846d00711459502180104020541c107504055084520308641c40310441030701c01c0b142c0e50036000316100c0c0c0b2000c4004101c841414400610b480380000e420182000702c00c1660884030b25042000100a6130b03105094009911807610b60005014090306103451219100100c1d00010564943e0a29002a00034401c10701d00f10071401da050500744 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 989602095 1250 989600845 989600849
    0x10c0c06030626071802070c0b03040201080901091707051f051e01060905010806030a0b0a1d0705090a110c190b090312010311010c0f0507031103030f0d02030a110a020606040501 78
    0x800c00d1400c0b41d0300301c842c9803248081d0045c084020390b01d98400d40f01460395070455010300d4102ca142c1c21550b8944041901540c016181070713000403011750226086540602c10320445903480f07051a503042c4240c10890741c1d60b030010a81590b690060b141c4203505103001c81380781081c42601c004006280d00d09034011100c90117006044c00f91f103021040040c007000d50803d4600c42658000d080c0f420940c0d49400c00646410003500b8000c101031080014082c00d03001700d40100000680c1528024412400740315020baa03134035984100e69009100c240824034100069000421001d4180001441c00b000824602e01c6c2030035440c03083c0c07e50b000d20800801805440107180c1d40150007000554038150041d0880000d14106000c0a44801450314a1060741c0c5e002c6d500e01181a607008a5503449001e1070705209842d030406200c150307202c400450901d105d0f0315009c422120742e81000d00006050030108680c420003900000c00001416a6078200c40d0088803218000e00828032055000305510700d002400c0c40241c80e81031b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 989603345 1250 989602095 989602139
    0x51504022811060c03100305010c02060a0e03071e0501090c14011418010f021c030501090b03060c0a1b080f0309010e0601140d1104090804060801141e010c0c060306 72
    0x2070700b0b4070100660007090141e08040070b60a03082d20703078076031241204070425980e0000f45150328251014840a4011074040d00c01c0307050400070004c1c4840e0394011612417117074020080c010600c4e0000545850310940154006900541c0001501c50055540c0b044171101c6801c0103100024102e604a5250b90103c5120711080c25410094182020394032045000c24180d0002414020b00c0412555400d1081005007808030362140010f80f020882c060160040000780a035850243c10022505410704000401d20300448101c0034551034000c020001f1929507946031410b13030701448074404060110700004082d0421a102035440ca0382c03070402035100c44c01c580540390108120b80017100100804564075000f204250019251042c4a20700e0b4a00600004080c68003a03601c246009409014000e000e805001034541d1512203002c0d60340c9480d50300070200f80320348400d640b0451001e550030f90030307100360001d408400d41810030020400030740d41c81108500040e00b10000099481004028481070404c01e11402000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 989604595 1250 989603345 989603357
    0x70c0605151e151605070504060b0703050d06082e06030809041e02040303090e0a0203370906150b0301120b07020a080d020310090b130515040228 64
    0x18401c045040c4403142d05040c0000030a10300500203e8880800c034100c0c00d8481d0ba500c40d40c2e10041491125038254200c1c082c1c840740f08409000c9564201481100c050343d500c030800343d04100881e90112060340c000c0c0700f504030322034541d4000108060100302e440d640341c11907007252001102da418001d90900800c503904900500b869000c00116001404a46010380d06803004500040562542007011100c454000e8130144001400010b1640c8003c840090f1054641d0005d1030391201c115207400d81c001070311001c0d55080e011903040b410202e02991b9500c926440365042e0480d9078041c070042c040f40d000d070106403150f03a1583d070404444131801d170041000e00041c0b51014150350402c0f001d075004da0143c98004050340e03419800f050b0074034020401180c20381c1e44105483e0740c032400300403850040c3d0000d44180407101044140414001058003500e51450710150191040461500301c20b8040c00020300104211070f16002000600c2d1954001403112030608100380d60501006103540102c108018503940070050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 989605845 1250 989604595 989604631
    0x3090c120d090e060102010b030f060a06060f050301060c02010c0209070309020f0103110f03090c0603090d020c2d060904060b030f01050415170c22060501030e07090203041a070c0605 80
    0x50010780c2c5200f03507400480440540ea0701e910050340144180c03820a6854402c204000c44520000900c584c03103014121003d05c8019a9880140c8950220044000c00b0403410b01c01800201e01c0344d25400d041d0f500524255011003555004200400c000b66003002c00203480f2082481942041c0307410440c8d040c020f2034100000406040541000d00070700c450050603800000c04656102c200304004013800701c0040c842d80c1e4a00748112629510700140483c00054003a400407d07500303160058105241d040c03424007451a02600d141a0a01910080d400c8e50740000d091108600079100c1d0302c6084c01a1514075101c81d56828400050200201d051348641c1c800c41c14801c0415441e14056140021150907824215011042e100300d90304006e00d03011140d030444000f0101d1040c03c850464210300b403890001b800c0000d01c0c0c4580045040e41c1400994140d1a0300a43c0200000c507469801540d000340070f510f040105260040c00c01d100840107883c410005030350300015405000a80c46941d400c410b5800850001803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 989607095 1250 989605845 989605847
    0x2030f0f0703150b06040b0a0e01080105010e01050a0212040b120108190b10030b0a091e05030f0901180b03010e0c0c0604020f010c05060a05090708070b04090e0307060203090c120d 79
    0x1c407450000a20a00c0385580d50390a1801da0f40000d15201030042c1415122615800001c003150808034503000002d203070700350381c10317031540181c107800e060f18030695850000b100c0d51001981c2e00d6005078181ca007103204c1c002a1601510806001c1c101500e13110656982d900d00e640c52441d400708040e00700d000700741c20146d010001d54510100c40b400807940211242d409039503040310b00b40c1080d902d620103400406140c00700400d206c04e641c81084003c0c4500c1c005011100d0080c5034040340c503400400188213078810030070282d8108094011f00707480e000502d4006c8100b451042e40e02c0700300482ea1b101c942d220b48040f0040c411000f0075207c060348031400c20745403070405a030350b4029544c0e124007400c00303400307030044610099840e4403039101c148101f42c000044840a0821071115001003a0444100350b0074012440e0102c2c01d083c012031850b0444456071a81e40c01c1c0b038108a4204024540c500c4403411a200130003204000400500245201c0c4207084041c043c0d541d045070070f00110203200314011060350031000d4903030401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 989608345 1250 989607095 989607103
    0x110f0118020f0604031a04060c0c170d0b0d05070306050c070f03080a020f03041a1302010c021207030b07081009060b0a0c141005060415061403040203011b02030702030f0f 75
    0x5601103032420301ea019800042143e43c031640e003000d0464901b0455102c640f400000c282805580700c2d200030068680328281c00c0b1640d1400c048014403510501d50303011201c0d00d06801811240d51500c0001400d1140000003075121061041c0c1210b6039002004208107002d183d01c540c1e507009a4440c20030346080c07001c0d138034045081c1a610006040c40f50140101d0b803002e0065040d20000b0040700b0300303142c1d2420142808a144040210001040c031800000612100c00550009a4142e0b041e116901504003507400c12428000303940c41400184a507070000808200e150b0381c514050300e51901d036104282401c111a202d54407a0382c00c0041c06a00300300081065100d03600c12100040d03c0303450413000140c004d04d0301a0940d600c02c0c0c0d02891034412490488050405540407a02481302100c08000400300f6003000401108503101d03204c08242e0703004400525502c10b4000f03643c024801000085c03961100280708200390b0001c2581401030340081080c0d000c41c14104610486c0303503041e40090040d0000308290302d0307036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 989609595 1250 989608345 989608391
    0x51e0105210c0a0314060109061a030604020903032d07030906030b0f19050405060d020607080c030c0a0f020306090a1e030507021216120f06020a1e110f01 68
    0x1c41c1480145a800a010030320101040803002071003c6a425524180b40d4094101c611107600355008042c00000e54601521074901140c5000d180140c40c00420341400441d40c2004203aa50007640820100d12566414030003056a904200d80071500c407803407900380020740342102d4590018810200003103404603400011480440355189004680c444140c004203e401200c0c0300416081551002d51b020040c0c40b050008090b150240d8ec01c125540e112070800c134143d8450b10000e074111104024040c0403a0304a00103060039400c000407a4606096201c03014941075a480741170b2500d030803a00f00f0070114642804071a03082505580185180d80c0c460300d401d107501c100402c00300c10400842440204241c0548141c1b0b141580081000c0e0b80300301c0341c1e003807141c44445460751401041e400f42000f0a03184224020145402d800030b1400d00100001d6a5260080d8002c1c090384051003400309d1800c8846d091410300005810081e5607190044030200e00d2685064508110398480d0b9041007400d042c0205c01d2804204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 989610845 1250 989609595 989609629
    0x9070602060414160b19050906040b030705070b090703110303120a15050d260705030a080a090602070f0204180b0412090803030c0a09090b01080f100513051e0105 71
    0x8500704204180a03d0f0410303036281400131080840c07000034480d480c40050200052210052406501c4800044503079100e18001d007948407a051000740b0403035880c1c101555200b4140d003069894580c5540307030540322400c2101d100085030300c2000148100300c0c9012290f4207500040e4025401d10824200504010b50018046000349507207640540f405450100d008004040227855107042d007100341001c10346403080410142c040d111101140340c0804100080343c481c0783c0c01001550510402010484401401070599075141e40c65a0300c044c080364051000340081c2e446050070300d82045091042c001034609030b06203403880b801a0700c85003000c6000d550030954007503400958045482c000e0b4a0031399042c06140c002d1020341c400402084403c0f0340c3d0750f000f03100700d4440d505c40c490219603420007141500e100f0054640003c4281e404100d02071621502550008081032024000d15116404190500050301300442403a0701c6105202540b0b104c2e0481c0a0710f00f0400350011565814200822007159921344651 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 989612095 1250 989610845 989610863
    0x1e0c0a1a19020c12060402030c0904030c0b0702030d0c03050a1415010509150406021b10140309010e060a02120609040515040318030f061a130207030e030102040605030f090706020604 80
    0x10328442d00c00d0202980c2000c0081c595200c503041201203640d03911044408038000d00c16030b040040c01e49407240c0550301c501d6050f07a42e8110414a80c0e0740009440c0090710380c601358401400219012249800f03600050b00682c2c0c2e0004080c1713440b400e45001d4803400d40c80420b1790100c00042c80243e60b1703450b0b107490081000303081c52070ba20820b03400402e81d01d400d030301c50151480c04081404201c0c01c0e804901202c40d0b000c20500f540c00d08183c90300b0805400139075030f00c000c00300302200818000c02800d80d0113140d00407214030000a01c4c080d01c1d1034050404804440c1c09045503800150b451032010318061440c2c01c020284c032451141d242075664a966500002c0b1040f00c41c24181c4009800c041c80f542c5400c01000400000142c410b1782c80c50146007840340c04004132601030070300d5600f0800c07080c40c204924a00c0b0000f00361694503082c00000311300a40c400741040c5d0400501d51100104c585007400208028422070359400c2e40c918298020340c1f020311000e080582d241e041041300300451507000404d0340c1c006400100c0c85e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 989613345 1250 989612095 989612137
    0x4020331150903080718140d060e0a05100e06070c0f0c080d030c051903110403080a0f030b0103150302091e0c040305151e0c04050d1b0510080c0c1e0c0a1a 68
    0x30b0232240004100825090070078550540b4201c01160b03800300144207404980761100c1c0300e200c410907507081481c82c51440d0310001c002249244174070b985c0c0161900619043e00160541d8541461000190b04015100d500002c80100c00ba40e0522072a02d0600e0316181990410260708415412011070340f00380ca0401da00c540d901c5c04a408144215801554008401582c2d41c2d03904401818000141880c01b003c01d203031054299055020380100000d5034006602914081d09607402c1141c0c508000c0d040384e407480d03802c03204407080390060f0203410700034420002815100d614600e401880c21000300166003419041c103050000001d110380e26420b88001c961202207980e0750b5500d01170700704e0003590321256200f0125030912044c40300351401c40d031040d44650710501c800350301c0d035050002c4106090306003400607210000082140340014080c043c9212424159030311442e00044d2a0f16040d40300f0002d03ca01e0304018518140c40c07404064240060203241d043c81404a499283d845080c0034401c8002182d00c910501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 989614595 1250 989613345 989613349
    0x109050a170c032e110912010e011a0a0b0f0d0f02120a090314040b0409090c05040501030b0708100b09060703020a05100f0b0402033115090308071814 66
    0x415a003184058110361200c0d042c203002c940070540c0d52101c90744d1070714484155580c11209004d4134002c2a0040b0840d0700d41300240701406454000d5251100c2c1c03555944070341c0c6041040a00410a40d403000220fa00c440144032410011007494651201081d05003c103c140641516001641d40c2041851320000b50791900c200c900019200c5e20704110440001c04040025102047d8030100c3c3c254000d42e201d0019241c0b5090292880c801c0740107030200d14000f400300304105151038003c0c244407403041704012040341e07442000c0307029104d089c5c008580411030f42c420001e02d6030707000780000d501c201c0c492041c0d07081d24602960409640300350600356008060018117001814003c0050a07800c0741c0c80011101940a0410003c0003080702c4010700211a0904130408203a1a01c0d0003602c1c01810b00341024403010801c4030140030a004502a12441c1d403c001c0c01110200358208610240c5048249002c1602c081c5450018200d00e0018264400d000651603200d14040f41030883c401504e62090841c0f80b10128600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 989615845 1250 989614595 989614603
    0x2060f07080402241c0e0c0603060409020a090609020a021c0f08040f1505060f010306050a05012307030e09011d0c0d061205071509140f0d082101050109050a17 70
    0x25000c50340700c400203a00d04144818221880d0b000405c501d040044840010900d9129480c90b09015032040060001c1445071030240d110420080c0b0003080016403a80d14130380081940c0300e030351000c60965404100c044085070113200503a070000d00d02010b0240000320040c094080d00c401c0d082e1404101c048000101004040c100306121103811004a59100344071141e00c4001d048202d60143c000c1642c508802a02e50003802104140c4200400c12203026040100440325403000340040a4003e550812002d0101038060003884194040d943e1001c118500c80309000c03401c00180c0c004888100400c152004c03d0001200c035030f80101e1081c070420764416159041401070121500007041c9004a09209030800c8800150141207942186400c9006d4860385000d40310f00206105030000303180d1069840314185000e5060a80070500140340709665950780d16680d04540050a03118183c81e420754039102500c810400d03182c0100002d02e4204801800c0c88085200050b40d40700e070b09000070f01c80f2100907116100348 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 989617095 1250 989615845 989615899
    0xe0415200c0a0c050303120604050408090907080103020117060d060b040f1e27080a0921051e12070203071508010e0906010b040509071709010c02060f07080402 70
    0x5284140c075149000c0d401034942590390ba040320003184002000440b81008019280482d0041c110038855a80341020b00c00600310040c02140c40304000c100c90718480d030b24080014001c1c010340e0360b03c1003150304520015080824854243d0444a07002c2c0411000795281c40c1ca00c8800c5920590129080181001143c0503084240c0410341031824801250000c02d00c1c0c000894144645910901c01121751702003c401825048442000e0b210b80c0440f4240428504401010301e0103191038010607040d83c80c2d101e140e00c4074001c9441d0a8010700000c400c028004100034000c404000900d8680680c505075401642da01311033034805205107004a401c00942d503003440607100409121690071b114845035003008107191424043c008212440c0c101084041c0c100052140c103039100c1502023450241480e0400810000080203001000903030721640742001500703c1300500a00c101c0e80089101d40c00114080d04090300202980060882a010000350b154405030268119406485100c0b44240302e041d0845000605 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 989618345 1250 989617095 989617151
    0x901180f0606030e060f0f06060708040b03070305160e0f0d050f03180a060207060219081303050c040c14030c1b030a0c0b01080309030d050f0d0908070c0e0415 70
    0x1200c0ea0140c21044003000d40d00c060b1078642e030700c0d00071b4035030780d003405440c144462241c51000a0842c00d26034003e0520a01070580b0b01e08045d40d0f0605107010381c3c8112141000a505d50301841001c913062550003003c00074a04243c2d03841c111900226581e9064915841c3c402c0c0a5519a80103208051041d0200c0810480907640e0f14004810040d50200c800346009002d03400f0038500180003031010410909650080d40a803401000308055035080302906002565020420050980841c011210000080d131007000501071030941c0004000894116068000921100a951001000030314048030ba10540c0780306c65a0300c501120801440ea1074880c4881e041f18400002c888800c203800181c0003110612603665880301d82e803648031440d140e000d0394055942551000010f072001d04d000e20040c101d51030310f101c0d00c030b030030709036500c88140555000308003c1e54000b100062040a100084017000003504055207203404906042e81c2e40c1c0c0d94144842d089841c92075880900c6280000a40c803250640c04034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 989619595 1250 989618345 989618351
    0xc0905030a06090201110f0604150f0905060601230306041805030a08250206062803061409010b010c1509230c120703140a0602030c270901180f 63
    0x100d490030b0340040802d143d0581c04103440802500764400001041655541580c0141080780c40d00d5880303054807000b00c4201d41c0b0064031101e411840c00e40a124110420340580300074882801c100001400e00d664a0441c01c001c60700861559a400010f40c046a400002c19a8000b80c1c0001d049085085020b050800800328000040c1d4410140d40c0500c0e224003407e0b048012204043d0806075401c00042030b0a02800582c021800180c840e2604071088130035a108003000c0d44080549901002201c4c0182d04101d440c15610714800301c0e00342174007040035400700400c002040140c04140000c1e1403445250750081c003a0020150f0b03800c1d0207941e50040d5814075882800008440d01d011524034403401c100c5200d44903403240195030b106a00d400d09012980900050250107040e0858650742c81c10480c0c510000002e214008250000940ca4801107100d9020000d01940781c40020b101c0e4207210541c003e440b6088600494140521382c0c07191070082c11034000d04a0302d0003c501010050014101d04810801014a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 989620845 1250 989619595 989619613
    0x8090102130b130501020610090b120105160801080d02060f041a310c05150405060310080601141e010309050a0302010606020d1409012001020d060f060c11040c090503 73
    0x202e0788080e20b4040d8601c1038042c102a15900126514402110b803400c19141d514010000c1c040c4580c4a4061418040d00016081c0c41034a00c0314203560b81500c04d00c0164045040c01e40800d58011102409014040d020340a46c84c0070341c100039540d41000d00740440c203012a0011408004008040f000507848140d450901460036403039485c0316075800c034180041100b8100c40c149070404441d03a03400909500045c0b500c000381c14402400150101c91800d092115010000030a003662500c001e0352003200c1107d44a20642e081481e003505021040e400080b40041c1d0300e002020694a0085080d041004004181008030320540104c014012001001d8420302441c0600030616a06401c15425280c40d5004c880807800d03c01c0084034080c0e2084100e8060714000d004040144d80300f4907140c0102c8000d080210803010000070810308a80c45044204e00301a55103c01304054903060350b0307900090800c0d04010790b50002c1034842c01c96108104449a200320ba03103c2c8684190390103001030130094030300074007124803843d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 989622095 1250 989620845 989620859
    0x1b090603081306170109020c150a02071b0315020a1704230a1e030309080408060402030601060509030303040f0c0b0a020106140d02030706080a0209060f03041b150809010213 76
    0x75100251110b8002544500800d600e4011082d80132559880e82455401d41e1030042000d000b900243c0700003119000d01c03480402a40b680d001440c0c012079800c0001a900c01852800d00010540e18041d56a0f4281000c01040414001118080c09510007100582d452071110012100c85603071081e400e10700b0702d5900c144030034400d8000c1000301c000c0c0703500380d09004606c009541641e1440c048130b0003040301c1160308a0f0300c0d4040d0400c05025605100e403c0200e990b010a40e40c20b50701c3c0e0130540100030070b6840f14042000f50f2074100440c4e4010552818064507142a0601007912440000d1001c0d08025040040608001090480c00010250419211b450b01e05080c4002e000e0070381c41c840c003803440802c6000d4000624195507510035281c0d00400510101d481e14209a9800303000a0102516917030901291003983c80d04002420b0400760518015036a150910744a80300403110081141e040500b02c00501c40441000b1024400e1b07000380c00c0244c801c0e51510012406446400081c0052450186001641e4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 989623345 1250 989622095 989622097
    0x809010201060504050c070f14010c05190512150111120c16051f0203191205070306180b060d0609090212120d0e2401060e0d020307031b09060308 64
    0x40000364001d101540c0d03600b08000689800365a051443d850420001000403441401e1400882c03040119188410f2085030541c210f5107030300260800b00703400180d00c55083e0048441e02c113580ad01402c1040c200a070070240003500c01c03001031040200d02c01e001192809607000d21029218241d9174404c40301713400301c0400c0d030850070b42188000c25954480d0380440f145103c0c5032602c2c5c1041d2440985050b54140080d800484400d024106200541c0020041024030320122000c2c000292295210b209403980400c900308129030005001030209403410105025400c85980e40030030305a0a18004544140d0420010f8460f20811480c0c2c4038151400000140000c002e07000141072500071030f210340e4900e404c051902e840d1905d000d02c60521a504103c11040c40030180d1008150050b440c044035261130f4268050713411012403502c0045401e0307201e001044410b40c043c1059030010004d40310300c074000700c640e03000c2651000203010003001c1ca008030820042d1100c801d4140d500411000106110303190741c07418400c2003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 989624595 1250 989623345 989623357
    0xc0f07050a0611040f0603061d1e01030b07110f0a1101090b041d060102030c03041a19020619150905040f0503040906150503160e06040f0807170d02030d0b0a1208 71
    0x1219180d05c0002004d0703000744a203d044a03200d40510040008400c0240d06250700101440c410301c0099465140050a81610a0185100d0340e69042c0508100c0005401d09141c00280c007002d40c00142e00300085a00801c6070b000456000c04594940d800f4003006076100c42c400e401c610740602001c03c0020348001800c01c60704038107084070311403070a9403164801240c9901c66008440d400d680100301c104040303269850f448018025a4076114100080102c200d2440d14078420100010707030100c0d05114220780c85c07a4042003941d923504020084c81c008024510700089151080e100300b5540c5000041c140120b034104185000da024080e00e0b40da0b07844021000060580e4013641442c2d8401c0c2d0b00100e100ca0160044070700036035040300394070840303003600398211280710301200032581009040c080081c1c8440d400380808060300c8608042d205503801c00c0210700ad41103084048410380d0340000f004003640354020086495807100c0032404941c8500c804045011211150320024002d02d41c4010306007402050005421 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 989625845 1250 989624595 989624609
    0x11107081315081b1b0105100807050d030809102a090f170109060606030605012616140a05030f130b06100e0a0e01030c0e0c0f07050a061104 62
    0x2041901e6020b1038419001540450010541c41c10102d55241040301801c500d02c0c408461551400483d5801c0c8480e244643c50490000d030345030350a020385d0080c02003410f800340c2403c0f001026054580360005861110f2030b40c01a042c042c1d2a804950803420a000c42c1c6000c1800c0c1105001c901d20b001503c0000300b8240c100001c125040e400c072800320601c00c0030100129240d660418201c681410502c200b0340d00808584d48080d0341e207194a900181c2d5500440009166507100000c200c0d00c2c0c0000075000141c103142007046280f000c2d0b4000780c0031010141150f040610b80e041d40940500d03905055031504401c0d41d06c0100d42d5404150403076602e61082c0218480d00b01d502d6038400a4840c0d0520030840450740304000c080e00d0603074001405a040400200512880b10311384800301050003c00705101d1105900900302200c0114010300c140500c0b54212002805040504051071501d150710740d10034060400b9000d81c0d544001002c4081c001d0402c04400640e420040c200212100010441410741c49807041c50 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 989627095 1250 989625845 989625877
    0x3020f060108010504080906090f04060b0307090801090f03140f030a1b11060f06010e1908010e1605010507080f130303110a0f0803100f060224091e01110708 69
    0x1140001c2c040c00342c0d900660f03103c000c0c60706141804c1e0070028546c0041c0d0b010354020700360035101c10a83d9144e00a90006007500090300e666400c0c1140001c002c19070035000b002250b0306261204001407126078030003100d01d0b003504d020740e034044095407100003520230311040c0d040006021007440201c212540c02040d500310000100811400d506109a94040400720070140caa08035800240b40e00c042c07191071aa003c001450907800300d580e12000200220100b00007040080301000d41402040e9007440380001e581c0c0e00e1b200801001c04002da0350402c4603180c0c042c1904004010845104000004c2d0541e45105a4a0150307500c500c402c000f4411004403a1100741d0020303a00c1482c0900200b00070812030222500301107100510790303454540b01c00d56403000c0c00b0044900d581010018000b90034035034488c081d0006034085c000c0700681c0005860010714061001c0c075030094239001e000511100141d010b80c000094160401030303039a0448554018000b06102c45c1c491030300043c03003008004080008000d01c2c510400e5003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 989628345 1250 989627095 989627099
    0x14030a020d2f01020906070311070f121103011d0a12030608030a1d030105070807031a011b05070512030c0f030f0a0c060e0d030f1b05030c0714060403020f0601 70
    0x445000808090300210502c89800140301c0c0c4081102d002401c518100c0050325055404000c0b8406610500701900011803448200640b014280400700003402c41c6594000b4403400c0c410085500d0f200d20b07900a1032403103048803d08694800f074100b07803842d8110440c440c0502a080b10342c1910740040840440382071090f00d200c1d807002c40c003e1099034107484501c2d0080d8202410f808042d5200100d96100c0390189070801c4140c40c0c269024050383e031264440f41c1e14031803039040900000d070594420040389091034901c0045a481030f40c1c4804115482030680381c00583c00c400c035050a03030403e8440e41010b600301b4021a40c04d034004800200505240503003100321740c031182c3c0404109440e802401340e41c03d400c4400b0030803595401d01c1079100c9011903010300000241103600d224005d141a41d074940e90408a9224840d0849040181c0710300c000503503a549024560407022074009205110080c01114007250104411090101040b81c2c81e80d1400c0d08805c0f81c4a41c201070401030740d60b503a00b48004085100b80000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 989629595 1250 989628345 989628347
    0x4090b0a2a0e0d0209010f0510020c06030a0f020705100615020a05150718060206010515180405090106030807061d120403030819020d0c1803170f0714030a020d 70
    0x140059040c41c1410200584034165800c9500390801d0000701d6209560680c4400540e0316400350703500078041892007005151500c0d060080f034040102d010000e541001040425988409081302d07802030f464400041d0442c02c03030020034003e005203107001c4c2491041081002c0c042a40354810826107800100b282d04000320500200d80e03e52454100400c29042045c6014415543c048156003100032420610001032248001c1c0d8459880c035489000180d00501c0100640d041815101844c2c00c00341380a1850b001070071007407540078010000218000c42e62040061032124081d4017400142d07902500c000da0710b0095091072405040c85d400703c0c0504070042e050701329403188005a1f04c0750b154243e600d50360a09141d500c06a41685000f044040c1180b0f03c03075154032400000c0c0c40207028118007003074005800d1000f0403000f003a6240000922260038a440003c1c4040380b480c0301118902422650b00c5641c0d01d0440800000d2401030000040005d602101d54000060707001c00501000d442507421540010740c4220 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 989630845 1250 989629595 989629631
    0x5100f0b12070b09031c0903030f080c030f1008010c200303060a090c120507200606030c0d020f03010915050f040f03110a02030f0a23030405120c04090b0a 68
    0x1014007055444040c041018107090ba000d0b121034140101031b503045c944001c028030040c001a40d03540000036031500b41441010341060f09050705041318503100c4010701e085992400c4610011b801d0003012012000021100c0b25031400d484080c09400d4020710581000c0000904080e02c14084d00784a210000e0301544203c00001c03d40e44911001010710306070a107804010750013082e100d1020800c01040418045000e80a4001c65009641654030b000075950140c98141c1c810078154102400b035003020080c800903540006403101c020310116a0700c0346074050b5100040540c01c4040c85070343c0550130441c0c45d40c240001b00c02405204c81101c081442543c0c1c40035480000d03584103d8005010340d10128150011a104807440b101d18040b060403281001601c0d000245084010356400301185d2080701e40a0810410b20381000340d45a00c0340c43c40d06d080c200407617000d80701e0090740a00c601900740d6020120305180208000302e04c4040140040240300d0385414094007185080701c2e02000c50f400e000310041c407018100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 989632095 1250 989630845 989630869
    0x8030708091507060c080106020c03010902010801060f020709050108070611060103031b02040902120d031a0d022707022107034109090117070b090105040305100f0b 72
    0x4440d941c90010800c0030040410b00340c04800201c03003024408000001c1031445a060030300e80d40c2e102e0100b05e600d881d00091070701c01507002d4a800790b41003268800050340c0040b40c0906407126410222001c051029040f03182a240b80e20050490f4200780001408007008a02039042d500d140d41c6a0903190900070100e66980c90038400140003070496815403505211002840c0340c8184024000301e54900305800140391b42c0a04400104940c0061040c060006d81611484510310070039290540b41c5954217002030b5060042d108007a006600194441d10400c0d0036640180c44803035004224101424107400096865415000c0c140d460344001c1c2c40303115451850415600310316403540c1d40e6001c0c100c2207200840207800d03820b141c80d52214444c0188000340708240d00e00284490035001951141070903c01c002e0301000c180d204c3c071004052418030050440021403014103682201c655150758000c1280104c0f03143c030555001400034011616152420001d5421032109088000002c0c0100c0840b0000c01001c400c0300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 989633345 1250 989632095 989632103
    0x3070206070804020d1b091d0604141e03040501090605091f1e030207150902030d0e0f0a0612060e01080a0b13060905060901060801050705070b06190602010b0a080307 73
    0x184002034440748580c10b0981e01a1020f0000c0000d40c01c43ea030744010000f81b03404240c418015441080c00031a1651190b5141081095000d109100045a00586030f19020b040604030190152880350b05500400c581d6021182c1c5582c604200c4003032112680e101e4206006040c0000c0e0b85000020b05a40310b081a503a40f9800201811900e00003c50408490890440607a040c0600303401c26506040c103003c42048144140d0f1009a2742d02400c1c6480c40303100c00384051060906141041ca0381c0980c800040c40b03015400741c0d08003004000c3c24140080c03520342120500320307800701103c40d000c00c0f02a444160381c040a20f02600c01e000040e05c072400180d400340d090180b032003d5131082c60510003080b070500210750400038010380a02c011805499550907164404800c0c0d409071f0000c4288a40b0f410309110350341c01071005d0002002942813005008045108602014000001c007102040c04c45e43c48003032a101c0402e0f000e203007881c555940c201c007070b020340f80c000c40d840d11801148500190001c400f0044520341940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 989634595 1250 989633345 989633353
    0x40b06040605100503070c0c080304050f040c0903030c080c240603120a300e070803030c0405040b120a121d0a061b06090b06130902100302030603010f0612020f0303030702 75
    0x10f040400c83d66030704024591410000000341110120380c09a1116010b0150b4001542d5101e0802c014004042010003240c1d0140d440d10030318515076680318840000780c0b50306103001034607003e0904241225000f006084e40310380c0a42d005100400f03130043c0642650006ca0304840c1134990b600c800300f60311a21902c00d160786500b070800206903060b1050048810b0000032003485c04c00701130f041010003030315180f01c4a10328034683e03511039001440e0010062000100b049400852940c90b10003500800d41c01f0354400c61780030342d407920049a40c0f940ca01c1d401024014040c01169003040560800034110301c2d00706a0100414038504050b482c9040b00700031502103100141c4030400c106d18090003110108400f00322100390300e689a1004002924601400d01d8040c0580000c0d4036900308074003000000c1e010002004403407460700310b02c0001600d520014060310030b00c6040044c0c0342e07612071007c2401341000d4040c41039010700c2c1203400f1640d007500285401219000f80d0308820350482020501d9500d2000b910740c1005a40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 989635845 1250 989634595 989634619
    0x80706080105041b140c19050d032d0b06120403180503011103160e03030c0a1502070f030c150e071d0402030a0f0c0306020c010e0c0109050d02150f12040b06040605 72
    0x710f05c000409200e42d20004460740b1152001c94129265101c0004441c141c002c0200752000c103506019035661081051441d05010a0f0501f0320900140641d0588410940740c80101820781d4412090382c2c203076007040641c042285410300e40201402d003146030800105400c0000031a0034103052042d1006620130340c0606107941c0b110f46508a00700325a0300800b00300b107050100103e02e038500740301409145812a009116164161400c04184407500881c0184e6510600c5a000401c0c036462003c9090750309810f01680311100d0742841c07207006045410880340c103410105100c0d800c21000034414126140c00705400740d803501070200008a89826640a03501d940700315070b00000b280000d010051103600c80c100d8420700a90fa940d8540503a000100d41c61001d0755101c00e60034840340305002031801c20109203403200c0c5c0c0e40e04100000307034154141c08019005110415205d21a0701a001c100c9051076005860941c48407054225895410011641110800003141c0862843d081600840040e00c6009201c1c1101030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 989637095 1250 989635845 989635877
    0xf100b0a060e03031e1903110406050c070e01060509090f01050f1519050403051b060a03111e0405100c1a0c070c0602010522121404080706080105041b 66
    0x515094650300d80400c1003103040050031100020036000c5011a17040d140d0505480550f080b0080358002800d0505001680d40049003000031074058a9840c20701c82e44805c07403d10351500d003000d160402030003611000004144a504040640079041d003c81c0e0f00c0c81035680da420b0a000342500be115440d0456041307802404c02d45071007508050ba400041d04200d0038564403120381610070f0a508000c001250b00040d041c420702c4000d004e644041c0b03548101842030122203101042d96482807000000401d695404000540b501400c101d892440ca0b02c4403026001540d0038121038036600c43d12820340f2600811031188145d9016204401c10240c12107003641080040750344a1390024001803403066200c104011400001c1d42107080310000e00415400022540b0f08516100c2000c600d4000655440d4031030b55042e0000b800300d40f02481074071414540900c004410300740c103c0d02401150043d071401c1c042d5032000304049900500541c100e0768121410300c40c07803490344900000348801410880c00912500007019140d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 989638345 1250 989637095 989637107
    0x60c0a230301260a120215070305182a01031107061b02070f060e04060b03040606030308010504451505060406050d12110304080a0b0c0306010f08041a090f100b0a06 72
    0x5178a94010f54201d4500e95800d1100c5900458400c1c010030781e00c0080c010b004c0ba285507000c1c0d181054030018040e03682702001c041080c0500b8819803641040303014110107964131a42058188007040107030143c07034244514060010304030007804009082c282200041440c4e100190507400c030354411195181d564103188003120f018488440c030f65000381d00d88400060300001c02004501c694012140010418103618004000c90810f82c425441603090a040308030400421410968041681a000d001c42c4001c80c2840d8071150510380c1d207080d502d05101b0316402c0c4010714280d1010890700c00c504000360360b6003004010848080313000c0c540e040a000024500000c0030119280b0060340c003410140c00c0d03801c1c0a2019441e40d8019000754525800006051b82001500032117076030081d015071025410340c03620600007000e0480d055080002c208451012a05120282c8a001454020244041080e240440030142e9650103e000c2c4445841024100441c1c00d480748100e0b520034000400310307100e00d4a062022245 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 989639595 1250 989638345 989638373
    0x6020703091701020a27051e040e0f011b09090b0103060b0a020a35070809040207110118140103020703090e0a0504020918060c0a230301260a 62
    0x344001c0031804200c2e01002200300c01030aa06200140e680c03220041c0007000000d000702c1600703040880c00c000c1400300100703005110039183e041c1d803002c8000804034020440301d440358034840e07003003442c05c5910050311002050101d01c6c401664028011020640014403155890410079400194002420310810301560032065004c00e05150205d80c180d150001001c3d036500c0640c5290240e0300440154041154180d08611043c06001c1c64802c9003401c040c0f010400b00700041051003c2a0004041c01000301c0030003611241c071009081192600c51620740030358042c0c01140128081240a244450744001c0001c080d0300360b0701c905400000c01200880150065040203004405010340800c0c08215007031075000051040074610701c00300342030600c1c0c0140002801c3c003404190300c92440302014010b41c800000d0390388d0000403034142113654501d04481110440040b16810161100390701705c405181c001c20f13010710b058628041400300400080c1003602454107502141c42c081e82c1083c0345c1900170940480f20740308 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 989640845 1250 989639595 989639597
    0x4090813030f140c09041e0b18010608060c0f0903070911071419020114041d01051516110a0306090b0405060c090109180e032704060617090c060a0302120f07080406020703 75
    0x2407d04036681702242c00c40206c46c00b044010034184210903428007401007500509440c405840107081520155115200e480f080100740c00340000e006180d51020840c0000501b41c00e6403c2009059841900030117070b01c005e00903102030300c2220154956541c0071444040d841101000e03584240741644c0107403901552081e0a09800c5030034040001c0d1858400920300c0301000c08019468203605050030840500c542e2103400f030030640d00340521480d818008005450090304282d03c9480c3c400104d0001c1c41c0c0b50300e26040201031600b880c24000c02c000142b2540d078000c5102d47c080d10403580d1080d00408250040c10344c25800030324581ca0400c00401c2c207001071820070400100114803504480c0d00c1030324650021045000081e00c12801c0c045202d4098000c00e0445411202400744d1441c2480040420f48000406008070000c540450104c12081200f406102009040303151103050b1014050000c0d00311010892410781c1102c0042d10004041079a0391007640c050322550344684454032441700a40040300220 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 989642095 1250 989640845 989640893
    0x60904020420120a060e04030512090a06110c2104090504050102070f120f05032503140108010b0a0b0a08010e0a0b03070b041508011404090813030f140c0904 69
    0x542c40074000d004140300e2040c8040c400190500814000889140f544007049001c0314406102c0080c0e4000c0c22602d50280040e81c0105544a549039030307041524103500144001d285c55140740400c68042c0c043c3c0071940c102e2090320000765002440c0006070740c0700c980c2d008041108110500c07076030805600440c1c019010300001420b000165850106900100e001580d07e0302c051102c02c4142940001c6070f0802c10454500b0034254109034904040e4912054004a0812003100d2011080c621a9002c4010f8030303c0303140c200c102035958560242c000c26000380d4450050300f403210042440d0700318504588a104c040e94a10095038a02390020354003800c06844c03808000c0e110710010f8456941007152501800c0342d1140705540d82d1405081c943ea2103e4042201d0601039940300400034405c0401802c45144801d54010030f5801c458600034442d40715143c030020101014202c007005200607015038400540c13180f25800c01c201c51001c11150b40745440c0520f10343c40b6a2480024001a4000305113040d6084003a24003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 989643345 1250 989642095 989642141
    0x24030111042117030907061404030f0f0b1512010b031510090603060b040b01030b0d0206162406081f2703020f10060302030a0204020f1204081c050609040204 69
    0x3c030703216a169990b51040f403080072007070042d06002404048005c11490a2004000347e401590502c0390065100c05000388481c1d40c264014405041c3d2418440e65100c08001401d1400c170003c2c0100c4006209141c0c00b0741811500086151414414500c0d2003400800504401e9100c0804901118004143d04807a050020000684100d2802004051840341d01c0104207614040d003407104844055251780d04042c2420309540d03590b100d00b024048015019505103569039400a8030f14105007030001c0052082002010342052451501210622140ca45206201d4203540d40312090780c50031a038294401d40203800700c64003c502d5081d8014045007001c1c00c0c485603a1100115049444d00c80341d0415030140c0c10030b1200481c1c800c010322002c0001c1c044007104008990441e00481d94881040000a024560000e0041460582d40050b180d084240e0178030b0344204d01d02481e1410050b0170544140a0004c0300d07010300b20b0810707103034084d8a2084401501c140340c1c4c2e41d1039400700009000381b90b4145205003000800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 989644595 1250 989643345 989643353
    0xf0a0306080d0f02060f251e080910151202040f090803060f090903040e090304030204050103151401050d030e0f1302130512030f03100e240301110421 66
    0x2054503140c00341c88840711030781c20140185c14000003c1002881851003004c10404884448400c03240040342041d00165031480c0c2c50641e90780425500c1c0c51f114684d5445658101c0750300407a040c0c4035282c032078256201d00071400304482c25200000c040c070b44402d40c044810b1224a0032a0620340300c441c002480442c0c030002000c2c550f8101c0b0080c42041c0c52414002040001508010348c602211010a90355440f00e490203810140e1640184d0140240310a250700205030030390b07030030402e0306c0155400400400095075a4030f00030105c0c0103108864054a8184944094903424074500759048801c090043e11141d0599134040796411103540d41698407c42108107000306845550301000c80864800c40169100c42c0b0001d03a10b64003295610180c0303c0c400c42100360b0100309010003566001c240c21081c564403170703c51b031200424003c2c1541022404042e00b0303007080b04982509070041c40098908054032801d542d410b05041c240c44900c40c00c2040f49004102c03c010220491000a80c1e000c5075580c0c0c0c40180c045030351 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 989645845 1250 989644595 989644603
    0x2070506070b0601080601090315021b1002190e0f0d02010507050111041a1e0306180c070308061804170f0309070515070b061903150f0b150f0a030608 66
    0x100580382c0d521a001081019604055540d1b081002400c0c0b1a0f201c174919a90900280c84c1001c14402094003c00c00118000b052a108190100c2030702c19102c0780740044410100039042582010107113004401e1a81e10b01d4000c42800030041409415030201844200600c06c080742c480d10128100181007201102041080c071030940065180c03545241d40300e252610005402c0d40d001105000c030782c01004403d031801103403140180180280c080540d02e0380d03510400a000b4070741380c1c0c212240e0a95241c1c00c01026821000050150601c00d887e01c0203562241e806000a8030b400c0e0a00980600850000c1008500788690004100920a04443c508641d4512001e0391750030543d0702c082954000e0b001030055161601c1501454178070402e82500b042c400303440e400a82d80c000b034001406240c041c400d550301c1c0e41c0703a001804003847d042807031070769400c7d41d9010010040150301e0b001040546004c94007851440e000c5440c040f8a40a0b10480c1e0601689040000301c0b54071038034545080c5566554000b89081080c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 989647095 1250 989645845 989645857
    0x1051012020c0f0c15041404020f0703080109050c0306010804030810080a0b0f09030a0207120f022d0a06124b1e230c0c1c050901080702070506 63
    0x10020b41041d03d055140203144c0f0004030f0704c0d540f203000d4000205002c5001041500c08580c00700c41308403c4c4241c0e80021a0080c0b1818403e458a84000039403070f020300d074002d6a26070403104c40038810402540c902600c0303409030009441d0719000601c03000c0400c010034810b00c1310710b0f001400c469070318500d665200c0d20f09140c000707040d404032540a5103034104110b41503103000383e544c004501d1018500d810940301c0002d40300d00c2076000f07107400c008011000038140f103401a06051055806840350030350003c102c03054000000101403400d06002d001410001504202220904492060b110000d008464501540191000d00050840224802d01c1c0d041c096201e2403100c24162400d227809200354101c00501c3d0b12042045400036100f60428210408041d44446000b5000703043d0709000031410a9000404205030060304160200c1c2e00900a1243d1043d120005080c41d40a41c0126410794100d451803410300c000040d00480803c1d001d219186183d40a02643d070307401100c9205560240e500c5100040d1a60051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 989648345 1250 989647095 989647117
    0x1230402131a041514120f0709050121151a0a0e091b010905090a0b12010f06080a110607020102030c060708012606010303030e0c060c0604030306050105120105101202 73
    0x24050240c1400e0920981c1c4c868100b10100403800c40c1441c481c040482240611540a0600c528503004900c0090082d024501014402e846490343d9400c0710381d003d41400e00403442c0e1050201d8249200401d1f844c581542582e004c581d220300c3c2501d00f4120802001413245501540d008d03494030611598690f04054090300c89241c503804581024010300d8508a1990003030083d24500515400c11a0b03000411601141c0044900668540e10104448081e146500203d504081d1000d03044034400019008455020b10965007008a1603407405070343c0e81e130b154000010740790300c40d100b11000c0d00d410b0040040c404140180122407610001c2200070380350486c22165040007035500001030007180803100100503a8540f01e110107100440080d0004e0300c0c0c3c081880001c05265a90a24070302e01c803414407100f10007280c01080306031180d001401060310340d00c0c01c441c00c8000a190410104507580548181c4e00c0303101754980120003c0c0e08040920000320641e1200401380f21000c03414201c0c01040340010010500e203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 989649595 1250 989648345 989648381
    0x7020301061e0b07081206040204081504020916051605010e031605070603091101030c02190602070b0a0207080d0905120304081306051c090f020303190807020123040213 74
    0x360b0007044141d010303030000d01220070100812000300e02098169040d50a2044460110342c81c1c0d480054028469030340040068021880c3c2c0f0a0004030361070003075200780c1c0281d80d0344400d81d4400503610300d10804001c03240c0c0412014403045d090001c076460300701d400500c00c000015160300a0074449203542c008880410100e21007621803010000309012003802404282010700c45003481b552042c83ca02000700595041556480c40107580340e10821140d140d8246400300608003580c107081200c082c0d4000001980c044d0000008200c0417035080c800c40707050640003501d40d414502c008204101902c205a8240c03a0f074400c112043c4692803c1c5001540618807868165035a80c03081207030f103044009294803c5085c00414003580c0d02901800580001d04000300c0300004540c01c9900d003e01e0202d82714074011350944804a2850502d800e00c0c04403000c2640a40c851584d1550b80c1c030012801c0e44d100500f800083ca042880c0205010107403040c054000d0f1006024081509101940741c0850340b00e04038101c1207080c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 989650845 1250 989649595 989649629
    0x210f02070819060f110c010b030a03082811070201090e010617090705060f0c0c0a05090a0905030c030c010608070e060105191e02061b03040c14010c080408011508031813020702030106 80
    0x2400d214232282000f054001d48003200c02510050562080281f58440501b5009684854212104103016985407040700c10080910140a1609150014031049020a417001404149100c10101c500c1c12601e01c1e58588101095104d14404d1600d4040d0400a09100d1070a02241c207503a0440a040321110078840f10b91202d0300d5000c81031405419110b514000c1e0180c2000b0b00c142c0e29201c2740594420760031040421780d8246450300c0f0b4a5031080c1480450309010209070a06807641c1034126404031080042140e40c0e20703448040c0010207000585146000c98820003070740d0104504484c0a0302092400e003045420162480f500121610000c1c2d00e000c01a0406820000c40d01250002c039020142c24000160640c078040d81c03004030b5a4402d01500d60034241c501e201d00181e038447c203400c03902940d100740c1c03503a01c43c0c0e55195514003808041100c152041140d41b4003180300300d80001510401c1c540b04c058600b0f00801c2e601030144100d034010f00c8400c995020000307407005d43c03030900075500107002c480c00c0500700b04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 989652095 1250 989650845 989650867
    0x2101080a06060b0c0a0206090607021c050c011b12030605090a060e13150f02090d05030301050a150c1407051011010c1103040b0f07210f02070819060f11 67
    0xb01290000740303030860309010f149440240040c1c13640700240e06945090740c138810b100007e00c5c94015810025401240c9e9410100a000310404050382103200b0400c80c0d000040050040d5951100802c14030300c0140f009400b24081000d0404070800c0381003038200010b015403200c0108411a50843c2c1c03a0180350741b46e0303034200813030510304c64070301da119129004c02c1c1641140d0b40d46810307a40c68030342032007801a500c036103141e15003504036411981207050003000340300c940b5010b05e011900d0790000d00c20148501c0300308000280303038003560140002e1f43d04140d0b030b800b200c900503569403401952400b4941e1014482c62201007005c0d1201002c00e8414101d82d00c0c0c032010855468441c0d4203581181c000c02040010786031551940760000001d0b94151103003208c245e600c400c042c01d1404154003c070900a001174100c0344400e2581c088208280040b5401640c1d00f400d0030f52051001c1e82c0c1e40609105170712040d8820480c40014013038070110244018070030000810034051903c41401526290140c59641110010350b850b500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 989653345 1250 989652095 989652101
    0x18090408070c150906030905070509040318050324070309080c2802010804120c1b080c0d02030714150c0d0f02060103120503090313090221010b03010b2101080a06 71
    0x1041500034143c6030460040d8001d0095880744110300174103454000080030040309018800207490007804038071080c64203003801004141c84a03050000048400008505401c0c0403a0b049004030004041c0020780c0b41c1901c1c01d180c46900108001d04041d61040e003080010f820314010000c0c14203500003000385d1980031a0705426004802c003030003146181041c0703003001030b43c01200b55540180c1100d14103011296980c0140c40c20840c0354002040d081c0350b040c0005101000054039010380d0080e00c00c0780d00c060072308000d000011540f0100070798907a002100030020a9031003190070516510141003244400a800e421848070b070020a0658440c0d003100e1a007107207155001c8200e000d80c082501c020209d0354919150300040c03405a407850801c100c000000281c4106c4200110f40d54410707110303034420300e00d41c0c3c40582200079002015510030000b1038604144441d036548810324103813401c0c5400903103540d1070900d402c0207a43c841c0d4900d0003480100c18a80711075070381e10710546000f0400c4101030485400306140c01d80c00c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 989654595 1250 989653345 989653349
    0x7050301080f190813030b0a1a0409050a080a0216080303160f0c060b060f07031101050703200304060e060406062c07200d022104120818090408070c 65
    0x82c1d035101500c00c0004881520301001c10744d402501d0345076100407041224903504125080500713980d55000a0090640c195800341e4034202c5084001c03040d424004c0e007007100303444030340c800601254000181c9802084482000b0081c0c188a4011541c400005920100388003040f5840400540c00c040700f0445410505444240b441d161481c0507805c61401c8040509820403408015080554801d40381038982c07960400c60b81e04080800c4001d44402280c03400422461040400140e030394240004101d019020340075450107289503110030407201506450790011034000820030707240e0985903041e07211814130a2200e180900c0c080e010124480b810b107020340c0c400300c0441c0ca8104c8800055400e0082489440440310303004031080c982003e6000500b1006840341002d07020f601030602462a05800042c0c0000d2080b00140014151440b94403d804820f600c5000b1842101c0390381030080c1d0282d00088041c0014074082d135943c051262402d2901c00496003c001c1101d04440c808000912801030141401190380 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 989655845 1250 989654595 989654623
    0x20f060603070f12050a02510c0a0804060804051623040b121b09071b0503070503070f1506060e040b060c0d211802010e03030c060705030108 62
    0x2410070b03e0070540b400744521034031a01c2405440d001c2d44004114007400000c1806030010005015013038000d80c40c144003041d00c9010300c00302c1007444d011492120050701380c40c0c03c1801d07034059038810a29440258140d40c000b141c4200e41d03004900c502000103002030301034006400740f50b94954051420740b601518000d80602681d43c41c4501840410144040d103980416001c0d90692041e41100d41d100420054000e080c680d50f48821080000400040006a210084c1d0b803001c122070b10034550201404007042050f503030300001a8030a500201950849441020f000d40300d401221b00c2c003041034655a0441d001044102c0340d420406050105121014000d03100400c05a10100001444c01801a000c00038901c1038034021600c400c4500340c07940e5100d05481d0340718030103004c3e50130b0001303041001400d00041c0350341d5030f0a1541091204405001d0fa02c02c64260603406000c0950003d00c6800544000031908841075044c8020000684400014400b0038001c2c58161141c9469504190441d0300349910600811 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 989657095 1250 989655845 989655853
    0x71e0306050a051e120105060406061103120711120d0614030a030e0117090309041b080c07080f0a030905102304061404050c0306060a05061902010605040606020f060603 74
    0x30107203a82d104180310444000301c5100f07142020851890907540c0106000d00d40c02504496160008103044d089244103040844080140f245c94900540b030309540410031221540c02408200c1034000400d203c65086078132410074801e100e03d044042494990b03941c0c1441603070036010480300c080304120301030070010705007528680248a140c00301003980d4030b80921014081018603900c40c1c28030f90140021648100d1450310201180c81c2c0101803554a80c00b551103039005618014551020204858031004003104581e26042c0c40e4860070940b00c40380d04216020b132080c100c2000f01e13641002005004041031481a140840c0034001e80c14a1410f00700d030b252080c240715081840d460614030001403032010001c985856200341751502e04122005104240054900c54240e90500003805000250581d600804500b187c00c0796941030240042c4900030302c42c190304410306101ea9150303c0c040401000051031244000900300d641c2d54005030075210958001d0002d6002940000d100d8007041c004039520181c194020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 989658345 1250 989657095 989657099
    0xf07290903180a090e0708100905122506090201110106061215031b140f06040b07260d05100b03180705030d09051206070206070c050f06071e0306 64
    0x2075240d00c80c1c40c0c0c0ca40410220700307100702c640e503841c11020000703003094507010003001c07440714280c50b60350103540588691403142540f10600c1440ea40210030388a64050068001081c1c0481c03034000a400880c1c050a01041750000c00104200440411100c03178016000898561200e00014240358240c020041031030341807010500125822015403811008e15050014400094800032100f252440d0001000040060304103608a041e4800080a0791444840003007000d24880400103004490901c00d900701c0806d000c204130f2007104034090f140503030040d03441e81c41c154400c40e020413407081c401241204402c00032a848034022854402c06034480d0502c0c0b9500300c50360412001c4045800000c020306652141c51600b40080002441b84c00024034025040300e1901d01c0c0204090300d902268091103020707241110b60b00410020014034540112986d0f0007074a03c54855040c2100c031f40401c45403d48091069007041c00d100c44040240500c82d42065440b030f521940c581803001c6200d540c0780d84082c105801d01c001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 989659595 1250 989658345 989658361
    0x6060e0f0f2a0304050c010f0e0a030b04062d270b0705070b01061d010201291c0b0a0b01020607080604092d1103010204180c050f0729 59
    0x55030030241e2454800840080c0141c02c10001d038030b07200c5051070010301105000070482d0000d03a000240f078007602c61111408034410211580030703d18040d40e038485e58880b420004103a81090094201d4018400480c0310441e195100d000038641500c1c24003014110811140b4003190340c41900d5200a00003012031003200c8c5a40358503000c101d03d0001504002c000300c00b040b4150f000b042102c0b05035610130003140256075030385000b038039041192640c13600b140607912030f40505620620400004510102e5070103560b0b681e8048042e4a014203000c41e0b5040303103036855011800800040b610354620710441411100f442c0560600c801c0ea0400c1000d141590300202c14425650703004441e06902482c1590006410246400d2040d41c9050082c0c414000d82000d00e41c2e091050b90040e09002e506000c0d501c843d40c4c840007002410308070f108030300c0341c1340300314900e07003040144141e85400060007040c2e2071828900f000ba1a01c00e181c09a481600202c3e81c00800c0498060000c214402c82180d4580c605070340103091402c1c1038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 989660845 1250 989659595 989659621
    0x27050a0f081c02010e10051f081506010509060423030c01021009032a06361403030c2215030e0a0c090e06090a030203070201110c040906060e0f 63
    0x1000720014502d0148050a61003584030121481014003212841850080b806000704001d6521980302000380c19084100340600c0c008400300e55540c001000000b1500701e013004c001c01c0190540f810440300f0402c590041d0390b81c00141c0041e2600d48400e584d01d070340c0800510488824901000c1c0603030008014254144e8021480002c4041c11902c003152a1480e460300710f5096142c90147c030700c2c5865098072414061100d030f500f007996900c80d007410041e20b0300d61842c409404c0e000d607030001102c10500441940414034540d40e07045140c412400ca4030041a128002801c540003201d40c149661008101040036100010a00645c100c2032501203c80a090207030391044640382d14002001e154885035842d240520402070103401582025035003450369207a1000d0310284c100031040404a00c1440042182000701044509402e6499001945402044d40c019100000d050440c02100e0041e00100501070301c03140039003002c2c0c911036a03000899505058050300246005000a81400544010085c0502c407030f01d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 989662095 1250 989660845 989660863
    0x219020d03050307030b0d06050108101a0d03090f08030316090806131a181014040605070918020712080403120b0f040f0b0f09070503011527050a0f08 66
    0x494216640e80d1340341026000360001c043c4051300104426101410300c0229031016043c0d074201c00649150805210009098500103207400a4501401c14940401d241c5031414001c814442d04200c91780b60b0f640e40700d258030280c00d503010a03400d4200100300305401891340e40c685000881c5050280802c6d081082c219940c8100038110811841503080e00c2c000c0c8a480d40c0d21200065008181000f540b40c100080c10a03a998034071003584506c5400c2d15008442a50f0041860b80c070301460540740d4560720f81d260b2001034140a010b080c1803000128021820400740c0024815a560045000d0703a580c4441c50004950092035004a0401c8034000902c00002c1e880110900d2400d2448004500f8201540020b070301007503080e002541c00307842c00bc13544081846076004202d2446007112503a038818121028401402d404450074000035008000511103080240d50360030440219291603440e9010400380c0c11011a810b55004944000d910010800791401d040d01ca03001c1e0a5520840502601d45500140e40324914 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 989663345 1250 989662095 989662097
    0x2303060c090d030309020607110901091109060706140c0a1404051c1b0311040f09030c0605041106030118050a060501050403140309151e03040c0303230414010219020d03 74
    0x8082c0005243c480d0b000199002e0b0020055aa2480c0034600140301c1440d4001250040b200c940c0001004180b030301c24a503113421003030300301c601e13003001da20400805500082e0111030156541c629640b8403000360a945108000685000d9030300c44540501414950016640075150704d001c000c188040d072600144a544640b1138220b100c0300345051300e072200a1400c50000790281d5000030030008140410110705404041050b207040014100402840d07081e2038440300050041502c58403510001141940a55440780c0614401c0e440c1400000c0020a10350080c0c3c00301590304078035203a420b094400b6210705900441100d40800000f4600300001e40350307008912000c5c3c041c19200003842080801841268a001d0009107000940080c440344c12015410400109001140a01d0110842d40e89401141c0c051030f00404d200024030b246540072181c00300680c603051200d08c1c483e003e0070303140400300c405403001c0c09284410b00c8410303401c20002860250001308801034941c038030420398003685540c0c007126241609 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 989664595 1250 989663345 989663359
    0x103170a020709020c03210603060402061305040207030f030f0501030c05150c030a050c07081609020d0b03010504050601050f090408070b1003080705070e0f092a03072303060c09 78
    0x5005900b000040c1e40910a101d00000d1180b0003018003000810b0121910560880c503001442100c14032030408442c12901036200ca07002c1000341c94410060f00711424040700401849455001007000d0b6005042c08401049088079040400d0b50075016200c4580f1220804021940c59501d030142c40d0300d80d620595009444280c0d4200200340018200c1d600500c1000c1141e646424514004200d94840c5041c942c0704d00542e80081500c140208407003d80500c48c00d03c1d0381025090014100003940304017000102c80d07664034080b18868400f03014541c4154010b502a00c8158500010b21140113050040640310344550400c20000601d001c06441d21640c1001d210441a99a5075510411030025000034050780b40c08282c071010080c0010301e05007683ca0003240505071782c5629994602c0d407001914020082e821041484010414261400300d106042c02c3e20303040480d02030804071b41081d00582008040350f0702a10208402d48200c40e0040103003030103400408080c0b401040d01d40f40c0d40034601c403040c46604 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 989665845 1250 989664595 989664607
    0x2010b0901291b071401090b1e0a030906090f050610060804060b03190606080c090105010203090906041e0b4906020d05151e010c1b0305030c15010317 66
    0x101504440c1d4050080c1e0f02125501501c0341c2c2074a080a00362800c10303000400c0a00045803204486003620308000d2084400d44d00169241c20108550f04046042c104050390303034103007101283c1c43c0c3c017800305424003e004100c1c5506480c2001424500003d01c00da001b441401790421010782d001d43c030306900907045040001c0e000c1300c102c00a404c0c540c688145641410040d030010b018410554000700c12544442c0c01c40e0130f4000400300380a141402441042d0144e0424090f4400d00d0800030300b42c5070302c1000240009800c0a0100042604411491100b60300303569404483d4081d092122600010926010000407550b030030301c2c1400702102144410f440324030003016207500345007a119045a0816031082e020740d15000902c1800000304401c403a047c08456104032203845038100205508040c0301e031419005681010600103441e0300c100a00100c552058403019144e0f2440e11850100107984203e024541d2000321281051910030035501650b02d2044c1c41c4010800900c00460140d005050b45050b02d441d01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 989667095 1250 989665845 989665867
    0x1090605030907051210020c061f060e0d11030d11190c1e031e03030c14031b0705030d05100b12271e0d0305220c080d02010b090129 58
    0x800c6c0c0100b8030017428008590b03a0030b8603001042c03491040102d445910343d410100f40c003a108a6566200b28000b00b1103550301c90103241841610f640b4120b0261480c142c103900c008020900d0300c80101661000144031001403403809606001030f4140340d22054900c203070902d0301d45807207958041621484010045041c100c26000c001303d002d882c02150010000621b94189110648040030020001c0740007030300e44100d07400d209014401024494003141507890a5545100e4548446015226000300003801400081c001510400c01000f10480d21000841c0c98103004000011294854100507445101405222446070640002a510950003000000c080d0844600d02c9840c08000e0310044a81c020341d00700d000c030003003030760f00c442225400380c4d00311440f400e240350b405c03811501c0a0360480307010703100d80c0d550515001413540810300756401441c40c0d5011980d00c2415901d441c502103260310250b519608108043d01d48982603c0c010004460784c8041401e03042e400d00c5041d0400100100348210100b4008040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 989668345 1250 989667095 989667103
    0xa020714151e03011e05010f0215060d081b0d020303011a0d0f090b07120c0e040b0604051f030b011e140d090c03150e0d05070f20010906050309070512 66
    0x16a440b00080780d81e56102c500b44c6143c0c000d15007000d0480c00c03401070009220351107528041e12600850f8054400c0c1e0003100005051140064000340d401007a91400310041041e001c0104580c82841c100d076080407480e402c450307003000030a903600740944d0030038001003044050008020340b02180040d5215a141503070750311000185440d0382103030001c500e044013000170011332410080c024026030b15900195082c014601003034881c41800700b00007455105031b1800d9400c068110800010008103814180394480e40800c001d25110030110684c040380038004d500890301485004180c810038a40201804034021403100c0c0310907071400d03140800110342800303c218010082074443c080c03034000e8140702940c12401c00c1205200c00340030070340304c5002c030400400a50300e1520a06d20b05043c01005880c01c1c00141a080d1481c1e00000710a40703984401e56103040000e4103842c80381c91450220501e421102d6080400104001036a07080403090180400910450403400500c02044070300441e0030340c1095540385491820 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 989669595 1250 989668345 989668387
    0x510050a020d0c050a111f0203090a050f071a090105071e050f07060212040e01150c02100c031704081c0213030602091203040b0306060d021207050a02071415 69
    0x82c0601c3c0c190603040841d0300100600c200003199840e01c4070360000c07110170754980e040da210b19010825001680d113804075198002d598000342c09401d9812428054454a00300402102d559000d50400041030045c0c9110840c400c1000310b18505940c05c00c02020000380c0540319011014060b001000000b4a00031140482000701540c413030107860710a220440780c0790f580c00060080a0241c002c0348458070500c8031150540d82280e41c001d02c00c49d050303441d01400c40401d00c0b40f0900702c004c0010045048016803622a8020f0880f100703552070300c400442c0360a008125140101180d131f00c1c000c4a20501c4046290308041d501010401c1c40c0206a480c0b012071008005e00c03402c54590700d4941a54000414000242d0241601400c00d550217643c400212854503101e12490007401c100304024000b080c400d003060005820140c00301e98005181c98a0030f143c14682e0030302152800e00040d40010140445a4148104001030050441c814201813a880010b18420b5600008000d4030501140a003016042c0303080d0a51 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 989670845 1250 989669595 989669617
    0x11d040b030f1b010e10030b010c062301081c110f100209010206130b040609060b190501020c060a17100f090506010f0e0603040201030906020c011d0f0a0510050a02 72
    0x440304400360700b80e140c00e2020303072802280080907001c0c4095401400d250303034034040c028000e0003810300e000c009030300400d44c641d03841d8108200c203818040021028811010300e01505c8801c184441c00c0070301d03030400c900c1d8140c005080d99082881740d800d01010704894403a842981d401c1c100b400ea010031b90201d1030b124210920098602c103070360b01c40c1421001580141414038082c0d00703440c29543c0f030b545c840700c84800c200350041100b09841d0000b40414900d1f40921034041c0704080110b04410342d10b0003c0d4550014a0f582c00c04d0429050b07040001d9a0100204042d110003a1103050500b014484081e203030740701c414544407034008400f0015040005512186002d00041c1054620b8680c543c254034005000854a2501040788a04801d04030b0b40180d080c00803203000200958030b5540e0300d600460140402c030500b1142c054080c4003000d0036075428001c1c8030110140c0003501180011441d09030703280c41c403403010040044c0c0141c1040f1011440204007494842c0901c0804910f64594550081c000c1c4580e0101d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 989672095 1250 989670845 989670853
    0x902100f2316060614012316150e1005150f0f04023408090f010201110a030f0b04140c03131208010501030f05060f0d0312060b120a02040302011d040b03 67
    0x6810400f15520981c00d8484600c408039980000c0801542d69046040c003940100414074410100848904000c060111b01c80c0c1940c2034403200344c1c0e00d68225030301c0346501242d07981e00c654842c007290f41e0801408099040686082c002ea080001ea080e4400110014140c080c806845144001da12107111a50305a24050421543c543c00c0032190007000e0800c0d040615141c82d84440507096100c0920f074101c0e8280c00a00582c03601150004000b422480800300c03c4c155500c90440c02c0740080d00c9009002d102046440210300022211404011209640481403145251400c13012502a42c3c0d800d00340e000c19120021543d0f501c41107160008900384103c010600d044440040d1202c650209901d0304a4100380c80a00c1904218040103069440840302c140d001000c2e00d038002d1452819200464440d402424800099000421030106458664000602c1e103071000070b0021041911010305980143e41c80c0d411802d02e800e41c0d00080c1124020005d04e907002420140e030a54540d2a90300c000e0311140003c00b11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 989673345 1250 989672095 989672137
    0x70209010f0510020a081602120f100e07150807050c01020301030c061715060d0e0f01050103050f0613111807020a11030a0302030318030f030702010902100f23 70
    0x1100c10100d8902400d0302929401102d20f0900b40005000d01707411381d0103c0510300b454540d401500c00d1501084041c0e0b17210180508448007440103201c3c0d00e6201d04428064903400300340178544010303510400ba21080c141c0c0040703000c1001e900c110200949295143c600102d09840d0198112036a025091440c18907510010001040003030201202d02154081c0e140e80a202007031056079106480c0842e0413401c40c0d01900300143e4207280c00c1004000d1005842c40028500303404545152604c1c1100e80300c1070f0503079500c0c030041c010701c10b04101c00f00228084a000b0900303440d10f0303246c605111182c070070020f1011550100002503580c512441200c4520382c1c008003101c0345000720000303584003002039054490010660000425043c003052175507a854054004601c0d5072140401c0000c65440d0807000700060006018141c0c00002010046009021590001c00e0340801c0f0f00422591905044248041c0481c081100d218541c2110415405c08000340c1040a50440b01000390943c0c8282c0318000a10300d03000c408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 989674595 1250 989673345 989673359
    0xb10020309130c09031b030314030f2a0d050117160b090310020d1508010213030b10030203061006030507031401030f0c0803041805010b25030905030706080f0619140607020901 77
    0x606c400b128065950081118002d1001042c10711055841c0480c62017850000b5135001000508a105400700003044001c3d040300c00f640c00d0841d04140c4900140c1621503004205902c001d50484404070300c080007401640c00d020744203e072507841a00c10313802d03503920204618840c0d9130144882c1d140e110094405640e580400350780300f0004d161047d41c1d00701280610304c2c0414031903c1442510944500c44504004450450b01c03000c4582000400e104038407090860088010388080c06040e014602907071340c0c454690706010000d0143c8800034402c0c0c0401d07141803040c90069595800340c5045903080303c03c6141c1c04501c2d0030200d102480b146c11540051000081c000340307442c18050601102100c1030010072990f42c0355480f0009501c5505a0000e00c0414400d5076412106a040d5600640b0702c0380c00c2a2101c0e03555400402e040c0380080e40144041307160f51003001003130a1451182540400d0440d10000d00402c148850304400c1d02d14041c1700c2d004480600e0303031040d82d01d5100455200640060032425950381d6404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 989675845 1250 989674595 989674643
    0x1b0712030e03100615120e1207051e070e04022404090c050405060711031507050306280608180102040b09044712010b10020309130c0903 60
    0x5003a4040d105000c031110f201d00b420302c284000e032440008003060440074a801160321185050307140380c060381c2d2103032101741c02802040754a04190024070440d44030f002d98100a030800c0c5100e56001d02010040c41d0000881c1d5001c82c041b400d070340500c101c03170700c0d030785c40c0c50021036181001e201001c0c4100c2c4000460a10022120300600121403150b4005c1c40004070307400c001c40303460040c0e2040581142c41800010000303940e24000c4030000320054220340f000501c1e100c02609901007035440c1c2c0007184000091080360f04015688102e0644280c0090307040b0b0180c800c0d11021310034a0b03c07454080125403400701c1e005c6140d214844000c2001c0c58020754483d07803a980d100ca09a4054090184211f180c4595407030005003090035001840500600104d604503101d040e104145145400940c0012030524540c1c1c1c1c542d1030035140d59200c05000300004e44500403000744003d41050000840c2503600500c00d15003550780d0b05011140004400c0c8021442d00f070300e12810380e058401600000e11100f03620342049403c007070b000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 989677095 1250 989675845 989675867
    0x170c3a0216050103020a050301090e030c1903140708091201020c073512071703150301050105040614010e040b06070302101103041101050307090e0a0207060b030c01051b071203 77
    0x1955800500b607841c40150224401c406100d0041007040c8010000004e26a1128020703441440580e8903103812928001d003002524410f0b0328005100b10401000e25a004591040100d03c0050140c502107050320703002c0b201c1c041c1148661140e1001058510040029015508004003e0007219a007548415008072038903900e202c030340880400040c980c2210f03803c1050782a1030b071500d040900080514031480e201785500c0b05200f520700c0c1114401d01d0f2000e1250b00300452044224048a0105000c2082010309640069000307a10441c1044820700006000203100301c4003c0d02401d28030303641c0450344041006801014811648070358003080c00414990046190302800c43c0c480c0081043c28090b10482240d0300050b5030150084591218a001e20f5016000950304002c990800382d00d1140d0340c440010544204a804420329600421030404104080c001d18400350402c8000c1c111100b4400002040d9004080080541c0581c0030640c0502e0a0b040c40000060700003c0174040542c030f20b505024003100c1d615 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 989678345 1250 989677095 989677123
    0x1e0302040b040902010e190b12061807020303070c0f0507150f0207060206131103060c1c11160c1505130509040c140111010603050109170c3a02 63
    0x30100281ca0724207807007001c005960584620341c502440100303100301c2640030103a40407046100c100200d10082c07141c010b096080b40b00c7c01c1d0700d4403604c0c1443c28000d400000c4140300e601c030007500d41800304098004c020303203501151a2420101485550526a40503020500302822900070b500000c00c003544805d0300d08080e2499030311000c8156000500807680c8040038071903100140c0046001c1f80e2502c06901c1103106590050502e41402c10700c000001f810b01030300747c420441ca100d000508444e4086002818020049050b204000f040c48261103690b543c03182910341c183d012a050b14027802c00c400e000084d00a04000d8440c0c44003c011650701070300035405400c500401245428001910b49404228140b01e50352059060002d1890310114262600705e01c1406e40c180801e04c0040041003100b440340c00019801480081199811801c1641d103d21070007070b0196030705400308144641500001408191050300c28010b1002400c80700411840d0369010b50007040f00001751805543c2a9030000d2004011041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 989679595 1250 989678345 989678351
    0x628051e0c0408060103031b061404061506080610020715080103110a06020d030504051207150b0108040218070201290102011a101b080a05030a0605010c02091f1e030204 74
    0x5031507101810350207107114060f61640800b00510000e0f210782408660220801103c50748420b9940e50f8805403200740601c2d6960007848000c100610100e8000c0201c42c03005c41c031244e0f21f49400c01d100140b0070b407001000301d03000e040e609250088003407003000f15000802c0c8606c215140710081c50030042100e0400e21081c1c3d030210303c141400c1071520302a80a00100c0b510f54005000d41f07982e0740000c0c1c000d003200400942c2c3c24054650b0341c2c411005844000c02c10640304090703404655080860000c104c4d088005550704002200702004010303120710309060941c10004658404596643c9002c90140c1044450075058000041da24403035010074146126039101e00341c0080c03100d0031b09205401d0380ca0b0340300c0c0c003c168018402030b40c03603e6107402034030030016400c0c50794188a02c4600070b03201c1c0c094561081e50460f002075800802c022440c00b951164501500c0240b0f8200140241500003811000c8040c000c94108541106200c014a515000880041850854081c101102e150f02103105d89210b1000760b004501b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 989680845 1250 989679595 989679601
    0x13060c120f05010b0a0c061d0d09090b0d0212030c030d060801050a0507050f090303040e10030b091c0807110d05030114041107060209130609090201120c020628051e 72
    0x694001c0c2c0c0e0588410a04280c14081100d80c1150340c03400302c07a803d844c125900c1002c040005400707907041d030b01900c0e240c009116024624134002e129403002d40c001e0742520b1900200c4101e545d580c010030071480e1380440314500b040814401007402c5109119100299200020303005280b90f019401c100b0450311100003c0040da036407000ba0005a40e011511000024001c000c01d0040c90404030181c01b2001c2e024040f2410315448090581c22400c06480140d0700e00c101d40d0080007001600c0003003070351101c5200c02500c0c0c0c1064492041c1d0120780603050410a0080503c00210601e03c0f034081c0407401416403044400c4150001006801c40d403003030040c607100307518444001c501402d0900864116a03c0c182d551850801c2c0c944561000b07403c40c2804641c070062801c1d0000c1ca000c0c2c680614400f514907418001020440303880003607d012000f050034030703146041088180d81c040c1c0108070340f940002955141402003c001c16856005000c14a405840a1404090050105a08034505c0c003094240e0050300103a1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 989682095 1250 989680845 989680871
    0x90e0906060405150102210c010612020406081c050d0b06120a0605040221150a090b040c0c030c12020304082506050f0414060702100c150612030813060c12 68
    0x1201320300c01ca01584c45102003807540c401c00001415040e070038003001c500b0141100a124252050f903480078820140c0304540d5415490a4401c0c0c000401e035039401801040d800640f000003014030700010005114000c100045a1005a080221803035001031001e95140321320782190f0383c2c07484140c5010005501d0980d001c10b05040602c05c03920300801000b14041c0030301c217000100507a440c00403c19a40303141c125210b12107544404601b5005400490b20100b070f0342d1241070502c400c0f40c40c020014030030405c03840c0040000c20b42200d500501c1640091500d0103502d12100b00744d00d14400c0380d00000701407103403e0300b12814800040340f6007070000200858104881c7d0340c1c42d046559018015002c0070700301007040b0800854608404042c207490340a44040e0030b015068000441d100f5607254000302041700a1740c00c10801c02c003110384280c580810a8100300d0241018004d00c0300c0c3c4c400d107030010240705922000ca40d450014803501038506602c41c60910203030f4002c240040ca04c074480c02c0c41b0840c4d6820813001c00a46 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 989683345 1250 989682095 989682121
    0x1912020c04111204140607021b01050406090e04020d0b0c0a1b08040b0a02010608070f1503051027090c030b0f0408120402061923030f1303090e0906060405 68
    0xc00602c00d020742030240300408400001000341003260b403403100c07002c810102e05041c00218481e0b0455000b074141c501c0030344c000036040b45203c0440b03030401c501048180070140d002180c0f40e080e1141404c40c4155035640d4404078490b1003070904080c04103141c4c0d000f045461603e101c0100403104040d555203030340d1400007544452841440c1c00061900100340010701032007a044000e40180c04040c400031818559420085040ca18640c205132010400144c080c00f48944c1c019441c2a00c00c0d01e032504208516224005010343c402c14050382440c401502c40d50034225041440708050224404401c0145076030910b41182540d4083c8000c9502641c140c0000314103030b440c40c00c03441c41142c01c441080e14000c160044801c50365001002244d00c900d05001d040004030700c0c40002800c0c9030701c944a10b0000b40d00c1c41886440b001c6001d000408005041007008244802da2a0300f9402c181044c1c00c038101203845140c2034586520742d8110500004007403013004a295000152580a80c0c410b8404102549071034540c0072031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 989684595 1250 989683345 989683361
    0x40606140105160204090c03080301061d01081b030901150f03020108011a03060f060409020706060f0b04050310150518040204050f04110f060c0f0303090c240c1912020c04 75
    0x8584043d0078200250900360003c8016501c04c0c0b51030705079291246d540f88080d41080c1c02900000300814840c00e40242484146094900c003400d0446042c074100031150311000304210307114a0b4040210204100d0304007500f004491181ca40300078500c03070b9201c400d1300242e04a00e21040e80010904000041e003005100350b28619400021a1689542d613044140300380c034130441c0c3d080b030340100c1c00700b0000032005182d1000e400c0da1441010003194452901070800500b11058000c1d640c04a0100000c11582d50001102c54a40601150210b00e4017801c4401c40250030050b8403084d08098198441300c1c0044604004c01c0c4030764400c4030100220707268810b40e250002d004440080881910200c0442249805481d000c5500b4004005a02e0050950540d5003842c42c640301144166201200b44021054140408402c0410589480740244a0004415a81982c030350040346140740008a008216406011083d1484075203450034045088502e008400c20140580c00c00050040c4802103940b4a072600400c08 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 989685845 1250 989684595 989684617
    0x904050714180d0b130201080601020f03040911070519050d03060f0e1b0a090812030915040c08010207120314040804061b060c080106080a0606080103060903020a0b040606140105 78
    0x100700701c03410400101c54603030451900ea0182c40e55880380002040030b50540e20421541040d681c070800702e0b06c005400c0319006003102d4103640040e4110124094008191000c6a400a0011420003403400703d64113544103a01c8040c180d4002c43c903020044112540c8008421449002190305412100104800b00c451a0281204a00307059808008414030741e034607680c000401c1290b11a010881070400600755002c0c045080124100b14410800480b013800021030010030362442c5490f40c83e14074046a01c41c010640351f085030749280c201150070700030a4810400035188100007155a28914285100b0790000c1104210001c0d00f41170120505012020350300d4020317a13101100070b08103410b003601640c408044103924180381c03075081c60001c0864070724006c98802242c0d80c0c444448035414080024140030b4005c00310900942003260070010140e11044003411660403950020b010000d603c2c0490401c852030300060510784440e400c1c00144000e03075022804844485142c900d019803030100554040c042e0388035140e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 989687095 1250 989685845 989685847
    0x6050403080f13081b0402070803010512030c0a051f02160209060f04020706050a050601020304060906051606050f0106110106030b0a0e1606022802100f050408120904050714 76
    0x30004840c00080d003200408210881c1c00c0c015801c401610382100390307022030850b90240c05e2814010064040d10107600710305503802e42c074102013926421400d100605c1014080e690f102a58100900207005a9501101c03c009581c001d4400d410410394030700000b100a11015986102d01c608001d5a10072190300751040814100d030400d16808003e407110b402807010303400c80c00125610115030f07110b100a150300c1c2e00c505000606824000402c90449030000d1400d81954800c2205100b0150821410403c9034028a4210307654007618101e85151400d06000806403400c00052040c84074200714660f0507510712303030b848401044450f01306c9402c0e191948030160100000501054031480b0750b40284001a121800310f6000b4600e40b0720707803c00501294080d90042c1c1101ca0840164101e20300141c5840a003c1c10301c0040081640002f801c80400b40d003540c050064a04020940034060b6090310014000c44c8251400c08000d813001d00d08030b034054400e25214625140000b02000e0140903110f00341c0100b04642 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 989688345 1250 989687095 989687099
    0x206010510020d0e010318050a0b0f010807030803060118090902091b040b0310051008011712090f0d020a0f080f070f03021003060503120c010c0807080a0c030914030a18060504 77
    0x144c98200b105594a0304261b282c101d9040301500340b48603821041e2190005214806250500042d0001e01810030182040580010444043c0c0013a401c1c050702d4121001503601d0f00c030304006031852820510482c03140d04560100042c04240f9034000d6005500035a01000702d551621110040c0c0ca000c203a140c1d1a1400c1800b080c09100741c26000340d64810b0000d44100030036526900064000c000345c075154000108064014001c00582003807440b0080e8005d401004205100c04100c6001e02401c8111401207480d132286400310760b0303003c804218058001c2c060215807030700c0300941c1000c07684c540a204007501c00c46041c0506d4560029403003089951120822144900b5035003048040072800d03075010101030b00c0c3d41002c10a41d034240300e040c04022a08007510340d13482c0000041400c1d41c0001d0305500900c20f0300300401c851550130000315580000d1044001400249050058005000c4000050b0030000280c0c42000c42140010041112410350784400d00400175401300220340c004503014080016100b8841 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 989689595 1250 989688345 989688347
    0x30303180a0b0f07020708010908250b01060e01020c031b090606070605070c0c05030303040b40022b060c050f070c03030e0402120411010903050d0f0206010510020d 72
    0x40010404031030540350001c0c1c040d200e6150a05054580c0091580610309000791550104170b20802000018002d00551040742c40d640014040c1e0070040014030b01404420403001191140b551007150b0000d001401944c40d0798000303200e40e001202640c0176210301e405405503031800040c1c1c03001d028014003805035411109014080225000360155030001c00c10701c900c074002030701405000e03c42c03800c0e0364030f281a9007414102101122040e921184c0a07410400910000c58a100712250380005100c1056400607401e05111126044040e8514101100415a0417141840d101030000e264000c46d0f01a04511510841e1840f44452009550f2110038592564000136110341046060403128200700341840404045280554040d01c8110ac0c50318044030107108040d0000001c0d522124203a50850a09104681c03c000c0444080d101501000181d500a0043e03880b40e020728020b954014255000528900f402800c052201540329015004000001c18030b07060482c1259400c11701ca9009019034100540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 989690845 1250 989689595 989689621
    0x80d1e09080c040e16151e08240a030b010e0109020c3408152505090a0533090d02010e042a02071208071407090f0207120e030303 57
    0x11a4000d015814410b50724031090901d03c1e00406c0048400f0081d00880400240b54200c4042400c20034806482150203e40d07001d940c0c80d40c041040d441a01c581007585042e224200945481164408040341e0302008020842c0384e528100c500442800030680d072a0304c06a826809040d4085049601500c801600012541c69494042c10f0320010110210b049004003542400a81c0099200d5400301010031205841c0101260340000403140c85001c1050b442c0640c044000c6652010302081404112006240d9515010328000c1c20f005000241006020407007400d4001140c0000751031000541c845501e0b405181c003107403800c000080c00c14007002da95900544600a03d155005e401603541c240180003102500300043c201c840a070100000090303d154001d02c0c1c00d0044d00300921225081c04c03043d00068520060307881c095030005910724610102c000e018500240c80d8002c04040b800c01d0308449403a12250b0040c60032070f01030148400144d090030740030355461000000f9990954410400038042c865203207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 989692095 1250 989690845 989690861
    0x30a0807080d1103010b0c06070c050c0f011115010602100b090112150906020c013603050c0a0f020109050102150130140d08071d010504080d1e09080c04 67
    0x142d0014907496a00d45504440d00260011605601c00280803960324200700329459228225241200401d8519a00e02c0e403900720507003060b401445d01502d034190300d80c00b41c1002c087ca01d00003001c480032900b180d100071070840800c4c0b0403400075011b1040900d01c04102405443d500e400082c2c69200303541d20b86001c0406807120320760300780d4090070700c1c5400c21420602c0b40503101c086401000702588032005000840d0848111510340c800150500205601d8044040300c2c000c0140380c0323135000101910050409803590f1040b0701d040c00260042c03018140800c03403524400038550303000381e80381180c0c07c0e150801a0381d02d0001d05644d41c40030701a03100410001c001c0484c1e8201e01001480c003205002c0105080540040845c0000c4503001001800307030740e20020401c201d005001082c50300c1d0405003020075000e8080000e2014070f09103465000030346003886e4065801ca40041190008441c108900c1344070003000007804000004102014000b400c50480c4111844002c2d52810300150030720000301d0303042000800c000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 989693345 1250 989692095 989692117
    0xa080f0307030b030f01050411060a170603070f33020613061b05030a0b0a050117041109010305011d03030603070b070609080f03010303030608060c0909090a0219090605030a080708 79
    0x90f521110258030140104420703070000c0f000105150a241c038143e50940425058140500b5040c40307031040c41075000340e1942007030642100c3c2c0c000d903171109008a410704c05190000d1400310b0400d0702c001106d1081c0f590081c8424038220a01050300c0c010342c508041080c8141c008001030f03101c03034082a103408a0b40c41c900d4110348110400102841313245000c0342034a08055441020610100802004a00501641404070b0f004c80b0707045441420500082d00f0100300c07107006a90100c412001030300f0016071200b00644440e0081c140c003925a9686421030113000b2140704881e81d04400881d1141500000082e1b0b0301455008024044403401d1018220b031540280400b07413004d9807182e605030007240d0410003c24511061480150f80d030740c1141005001c0c0c600561120003d64040010025802c0304402610f0b0303000d00440b100041510b40703020a40c902100300001940c0410750700411990310f005e0f00d0071f03c02110440241441072541c0c5004054a601002c1c1d00a80603120410110300002c41da2030041001e801c003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 989694595 1250 989693345 989693351
    0x6060a2d090603020109143106030f110a05010504050103020c01020910170f0708010956030303072102130501030b041a010305070309051c0f020a080f030703 69
    0x312050301405080c2030344031400302659140144190b50f40b01d804103018040d6003410402100440000c10010840303220f801e41c2d4201040300d00000070b0310090303e0031a0307c070710030006100440e128100010000000d44048a41c50394100c405041e9080010005040365016101d82c1c1c1001c0c0340c100154081d50014448401030f5500300000c2400340d640801c4034000380c0303031035540907400d403180314910603560b001074903982110503e00c0401c9044d55103c20100c0c191030700030a003c2120815010300959003000d1800000e100350001b2590202c41c2c030382580e4441420698002ca0300c4010000c0d10005145801c0040340750150030030000140a240a10841550100720f1196140c12810680070b2002300d0708008120a581514645c08105642c5d140c005c4c401404c004032420012403e891207007011081100c45028181901d0398000b4212074000e42c06584000c1d000401d60b1a80a4410140108814080c822101146004042c28074461002032000e035103035440101c640c0f4001d400841c10880340c000900500c10192 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 989695845 1250 989694595 989694659
    0x90f141008100509010f06080c0310091a090a090605060f010c060e0f030c060a060b03010b092b050703050d0806010807080405190b06031011040e06062206030b0306060a 74
    0x1100e440950003003211000746c892060070640c005001000180018100c10380510603c02a0a9810040c0781142c4406400054202e02056201c40c900941c041d0158011110300070442d990900313400c0003c000380700b400f0403c20703640c0300070402446500d070300308890010b142c5d44c1007500013681503803003440b41925000c200c03400e046101d032103d0324540c85000c0c02200d6400000500130600e540780a808050076030007100c02d0541d0704000501c0350358041e81d8003030f40c840c2003040094041e80c00042c0c03100c1d11441c02480c1101c1e8002c000d00f010b0b45d176205c041c4000c80b041d00c120310341040202d00c2401928050307a0b05035140c001c26155200101d522000c080e1060b01d49001d2005c0412544809510302c00c80329118401c3c0950900d04002014200700e40d4800070240242051030703d00c14044800b0484050300c220f01500d139016110303100481c46034020030f8030300a1111001101144940500100c80b8110352095a0502149458206064480300c0507502c035034021403d91000d001480741c11000f00950510060200d042613 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 989697095 1250 989695845 989695849
    0xc1903060c050a080601020a0b0712110c010b1302090f130605090a0e060907032a0f09090203240c07061803030605010f0804110603100b0406090f1410081005 69
    0x10701c004800030042040018841c0003107422400b07aa42c0041d090016020084007034940103e1960024030350010401c40c64119a1a40b845500034958050ba82c1c0003da159008598098000c0038020f002901c2107007402d10340081c04010303008544807100042c0c0f1100401982500707005100e00c0c00310241d81c07a41c3e11140081825140da040d420301c00c80d403003900481d4aa0080201904124002e0310002503034000703110503c04240c1c281032503001c0000c0100070007078002c141d6a18600d480030a401138519110211000245021246c002d9007045000704c0c18ac8040c40701e46011410406000085e8800c82121080051201081c24024001980c01010b001c2044d901c0a0f400d400c1d8080e48040840c082551054148450f581c00b0010a01050140c200641c4604007522104203601c0b4030b140c00c0d4803a82d000000150007011404001004041c01c1089076119a100c4030040c141441c580a03a90010209100000d5030b00f014544603121600c001d002401e0340302e403100c02215a6400100828203014540c4e90000d425 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 989698345 1250 989697095 989697101
    0xf0d02030a0906050c0a1d0a080307060243020607151401080a0c050d0302030403020d150b150313141902120601210f06020412050f030c0c190306 64
    0x180e0100340c1c00040001503450407000b12000034092002818041c00480d46e6107812110411101001c10222039004200b440003032040721b01c64000540c10b000100300042007140e140c019064080066040310141d04649070905000c098050312003074004896070282c481c070940310704e20038006400507106503c0c00700a0b0b281c0240305094015410910f5030748802d01302940130207071a4540981540d030b0180001d02d000e52900284000c1602529214440e9404801c04041c02003040310015903000d40b032270050b2602418880f20b102c10610075001d00740d0820807c80c1d024940840411422400030a5040c19034454010b0083e625041450445581d10b001110140f2990200801005146e0303660004d80c0d844218414068a0003802a00c90b42a91102c0018003d54161a0070a1480380070051000141001810a1301003042c40c0c9401a02c1d41d480000c01088620000140b490010301900848038100340900000ba034030300c030743c0250700001d4100600120f400d2074403983d4078124902200c903004580b0348a849000031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 989699595 1250 989698345 989698351
    0x1a040f080312011a070215040e090d090e16120f1b09090902100f0302070f03080103020f011805061c0c0f081608071103070b180106080102130b0f0d0203 67
    0x2568808039010106502d640c61a9002d8501d41ca0350344045480361200003c54001c2000092080c04126100303207038218058103507001420901030704603040c03c041140310b4840410800c0039002546000c0701240e8003208040303250090800800074007c003d4404011691401c0d48540944c030140c0300e041c0d5500303060310303030142151008400800c10691141485d01811500c405d911500000c2e051003810000341e65a071002c025040c02c1030409200107042010114001c0c4500f401c0104403402280310a002c1c158032600301e0381664030075201144c0ca01182c0005444403120030341ca03402440b081800c140a103041c071a02401c00b4000c00d182c024000d0340b1001d414030a4802010491000820382203080d045907522140098010100c04c0c2441072a1000a10007440090000e154509201803604114018041001210b0701280c100c07003490381a0130103203400d00740c421001d0117042d265030034440c003c203884406200700c0303684150100e214840c0900d4001002420f4200d07040c0c610320400c007030000410292060008500c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 989700845 1250 989699595 989699609
    0x21f1404080319090804030b0c070f1a090604050d1b0203011d210306010804020a03080711041b0c12090b040e04021c0f0b0c0c070909050d08101a040f 66
    0x2c0c881c68941400c0034442c0300150602041820901e08070041030341607040784d0a83e0303004080031026680360f0380e00060611035100018000c0e0040d9808600380001c410a40d17008030304445920456440c1d401c010b580d5017806480180103034002d03c10702e88807680540c8413000d44982400c155180300f030964000a0840f40b072910240348001d8007019151850509221404400d2950039003456821010008804c09000062038203040c003000d0300c081011740d03030b49a04500003554005505a0340f251103143c2400c0403403981420500032401c0c4803503501e000c2104e2110f0050526150303128040480c490321207139070091405c102e00c01488808880890682e01a0b4004d00144c418000321203c01d090a1040c44030305030f5500c1d80a81604450707a4141d0008840703994101e4a550040380c11201c0e40c0320801041402d00ca1903103481843c3c455000f000528880c5070b00144003207402003094940d03c0f03c80410695004100300e82d60340300030300e18500070300c03000c46050303c00481c901004694034142521900e041c89a1240e98000302c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 989702095 1250 989700845 989700847
    0x307050a020901061e2d03020d0c1e08180703050601030c05034c14010806010501170a020904140610090609060e06121513020901021f140408 62
    0x950915002c52070043c580c07894000c03841c0c0b51802c4a041045040e030015002c02c4503610030b00c030229104500c07000d40040320254140d041c000305000500294000c10030403035020b00307000d07112070018050340c60001145c0402d8404010420b28100442c1c0ca10340041800f500c0441815501418080402110001d50300c680d000705aa541103003895401442254001c40c8294088681702e51600d44220148054819000c1100c94a0a07503003201e844139140a440704116070402150185038a81d546c0240348400d0110208014590700c8502a80c2c41d000c00b40240c40c0400d1650640003d5004610b02066000749860001800c010400c00098280c81c0c035906d90801c0c1c0140402440140d1a1407000c5403c00c2515091100c4114075004000d000d80081303104003028400e180300d903080316444600499603610001c82410b0a98540500c3c0f00d0308111003e15100d00840400d403004580070b2403442200d009901c140c0052200c02188a00b0841c0743c50400e0b400e520355a16039002c0080c00300014490740c047c6100301380d05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 989703345 1250 989702095 989702113
    0x9270807021809030904091401090809040c09030809090612060108063315070c0807081e1f0608011d2823030a020a050c041413050c03030705 62
    0x482c04030b0381900341420001200c14841044400000c8031098031050f81c0c0455049954105003d440c00b007804a41f1a95090641c28800c000c1c65800910820b8000c680c10000012145c008603051135090000a102e00b40402005400f0b2402220310b03680403500501c018001d40d02e581865007010401c0c1e010100740d904c01d200780300d500a41c1c510000102000b601014050250452100e40a03001d0808840d009018851300b004100f200c0204880a040e04040725603e11903894054130340c1c2e0200d034801c60300140100030902c80381c411081e110a0b00c4980c42c00041c0500c9070221112514242480309284400e82e0300d5100040301c51081c080c1d0030448001000b0446800808281c55061400c0030050b0040852170881014107681180d06038a100c60300b207403000000c52001c01040e840c0303c400890343c18840c8404141d4082c0d03d0390001c0c2d50070030548500146d610107d41c2c502030005450114109103244044680000c81d454500030b024070402e405801201c4102035404003103400d40e40590b84c01d9507140c11601407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 989704595 1250 989703345 989703349
    0x310030f082d0909040809060c2503150c02030403140d110f190c1d091b01120209010905090a140903120c030a140115020c0901050a0927080702 63
    0x260700320140d216080d4980396841020001c01070700c03030fa503103080c4228503c0340400c05000025040e6800c0340c00140045603109896100240d80f660140010740480140031040301e03041f46584810030450703038420a502040b0140c1c401d0580502044405001144000e10000022841d031410300d050b010a40c801506501505800c0102041c88038186d991181c0c0c00740f60901d40d500d40000740688049151102c0c030000c0500c514058460b40e00ca50b1100d2505890000451030624015130346030b001304120070171100103014400c07501d020b01d9810350720f09022418400394000f54900c1764004240101052600c518081c0e2204001203920005440d841102ca41c2d41e403c0e006c09003440722015408c80701400065040c10600713201030380e0206c4020115000c080c0048041089028260095035854002d506052400c1d03071a0340c07989003d0105644420300600c5400d11405c0d4a080c5a014141a64000b40c6401503450500c600d0b20082c00000304000301c034920a07140386d000030a60045011000e48241e01041c3c1e83c20803401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 989705845 1250 989704595 989704627
    0x90105012105070905130c020304060323040b01081b0f151e0901090e060a121514060f0d35071103011506091211100336080310030f08 59
    0x46c1011182c90180f400300d000d6000001e4504071515483c01103a00350225840314000c40140103080c0c0401d0040d010f0004001100700c1d000d05a0303503254226400745180c280d40c1542c412030b80190320741114500304100d085043c5040c000d00780c0d5249086041c50207106110300310a0b160451403001c000c250200d510700456900440c404000d0541c8a44011103040200024262031054829100800800f03058901003000d0f141c2d10420400c1d40280400c400c2c80c20104454400760b003199141d01c075040e210740d5000c035071800003210707440250032083c3c0641c1e4060007503400c81713080d2410905100d0b00002c00020307142480240020700a40703210354401d100301205001403600b5074002c0e540b0448441c1c01c6810502c8803a600c80c01c01c0003101c110780d00c0c2550065aa0504480c01440d130144941c12200e030600249910f83c0541206011510380000b031000080f400d0011a009400b0851004584900c480b12070041035214024503088120070280b05045030796941c807101c010004071800c494075500800c40b0124680e045c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 989707095 1250 989705845 989705869
    0xa150902040b0906280203071115091207080d05130e0603061f0308031509070e060a0c1704061206090204060c02010309030e04150906050f090105012105070905 70
    0x2220560800b0b050a0700c410b820b0003002200e80c043c00c4040340d0040051044280c0b400309124000d001114003000b244025140c3d4010402566501c0700340440d0780702c40c10440d8490714611212250141002002c400304121840182c0c0c1500081c80f441202088008041c000d054544200762100c543e62044413592403603051040d030224003010031260800034a51030105000c0d40c428001401c07d1550f00a000b02010542c9840e0000340c0504408003c000b051130071406a00c030300c100300300d5560040c1c2d039400381e045406050402201c0d4000303806001c0710500501650301015074603c030711103132440047d81406041040d04113500c0500050b1142403154503400e810311669000c1c01c6001004d41c07500e418488090800011203000a0405036954012010315100b181000c0041800400920002c2042c100d14000301b05c05000e020225403074902e001815240c0144c103007200140142107035510340e183c1300c010748032500741d05d480c0f43d01d0102d80d46006024081e9032080c0c5229004a44031011441c1c02c200900003019410303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 989708345 1250 989707095 989707109
    0x12030a05181002281b06020c090903090d0c09180b130512030a150f060e01170606090d0609080409240e0a020702040f02032a03040b1b030a15 62
    0xb6080c80c840c0507404107104503504070112880000c05400704c940504922450300c007402c0d90b0041c90300e56410f4100c0c4041e0074104d5407142d00719401505084d080000030402074aa040d49548208164401400c03c09664000d41c0e010755003003026140c0e01c01018050320030400070240b0700840503604504100101d16030f03070b401062019204008a005da03607003a945a058442d01e5605080100006002c0e00d000e03046154000d840c8029403c0c03060307641100300620079240c0106170104030440d4000019500c01d080d01800d0030044840002603455010602000e540102002504a11105110004140c4901850040511502090b60759520f0441407000311550fa1420440013055100c108058040c294240c030113075921f080c1410025215200410000c2c4554003000350420300304610403101000d154007951044041c8031180c50b410300c3e1070300c0600750240f140118403040c82050000c940880d50803140e150340711043c1c5101031000403c031340311002182c01c02c40d25024100d807211058450312956510040003030400f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 989709595 1250 989708345 989708359
    0xf0d09140715050d0b040903020f061f2303070e090d0c030c112404030b060f13050408090607080a140c2a0604060203042903041112030a0518 62
    0x30b202211108042c041d208200700070340031504000d12003041d40480445600244100300800c1d840c43e020351a2a801c2c0c5660185000303010010b03544882010890f1509014000380c009050700302034082508481c01a904a410800c04010740c903240c40c00c04ca070002401c2e4940c00f0134107a151101b182882c1921075410b00c420003c1403541c040000740c200b0031080c21107910088951003c0f06090110380303692024101220721610200060f0824001c074001042136034041d6801c40c150351343e61800e001503501d00e441d5090700700f8502030626004040c1c50340102e400612070075006240c440041d00240c481d400060b0103560071400040c2c40303a80301d80c10140900329000242405403c0c1201841c100341c0707541c440390000d0301c2488000e900c0e0502c001c60403100041c0240040601d84c84589400009560313401a00403820790805510b03c11508900b845201251a000d240c407a82c0346646650703a00384800741c2c00390b19641042100c50352b446900400d002906504085a90301a122070304841514a400d284400c034030701810b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 989710845 1250 989709595 989709599
    0xf0215162d0b182e0c0503040807021909020a1b020f1003060504050103080a020d031e0e0f0307030c0b09070302060a0e1c08180105180f0d0506010e0f0115120b01050f0d091407 77
    0x6000011f403544560000b0b281030716010345001080341d075100344005091251041d1004113a100c01a03020701321a91680e5208500b14403454000c4030b0608070a48003030750100e220b10134080c0e9441c0841707084d42040d240b031034007044169858022030141c0f082a0401c86400c0004145c0d110029410440b44414140e81e240030701030f0342d00b83c0914800b02d4141c02540400f044d100c00903180c200c0c0c1c00b00b000a00c4c0024001c2100e82e100f045007402810300b000c046040742c00c587d00c5008a550000002140000e89400030001854168484000e640c207284400c111904404100300481040403140c04081800d03004104541d03541e1003c80c0340b41e18071241200c0050600c40c0900c20081d9054892160880004068481c603c0b14003281e00080c880d80b0340c20400400710300c07800d800460b0164804070402d0180b50f0030611086941d88420408015440d4402c1160019a8800024207070403c20f800241a031041070501c5442c06105d0300d015065544280b44060001e83c40e0541003040090b21341c1401e11021540010305102c81c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 989712095 1250 989710845 989710847
    0x50f0f0a02030f071d13020903160303020d03051503060f0a051b0d0f021605010e0c0f0310050c04170c0a050f01050301030f0215162d0b182e0c 63
    0x104040d18070f9040008031602150b02c2018180344c400744170780041842080d891200c0300800a5488100098040d0183c04281c032044484444140d0a40e0b5041d0050840308805074070480050000501808110b040241c445050f81c5090100c18010010720b0b1401c1c40a1401040b040155072026050358000303a01502498501d801600680d0843c01d035400d00400d0702a501c2c085030002e40250301c81040502e81c02413601c0304110055000b80d886500d50006d40b8007000280082094488209115940540052f100c0b4203000100750300c001c0c1d102c11500512410191075020400b0b40311190440e0035000d070301c01003603c0c81a140002d8102c004040445000361407400da040024214001840002c0812b000b10314a6030466403030b028111540c50182c0269622016040c1c16003d010400700000e603030700c54814840800d1301c1e505006038510881075030a00301110640d60b8920035042e8008054200e4105131a6071849820020b00c02000024844a1400490070b00c0c00c800c2c00c4980010b80341607000e2450442110402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 989713345 1250 989712095 989712121
    0xe0405060f01060f0809100509031b030711040e10020309010b01030b030706091802090319020913052a03031b0d051c0941072103050706050f0f0a0203 66
    0x3541c0071785000c1d0840d4441c2c296051416034920084c00388141844100070240200002400c2001522045654012030340c1c0d03110307a141c0c03103615000b406040090130f03244520304041e0400c8130b10b900700b00c1c11a4031080c0c803003200c02c04a0300203035819034036a510707010106600e680c036005803000d5500031400340561380d14040000e44943c00c640705215052002c4441d88400b6801d0b941a10798070304002c1c0649500610802c0160740c041e00110341203101e106544080b4221a8420310f03141205507001e0010078034070035010385074404640b03019400300811028034142e502d22345061002c0d1009024403200000d84495880740f031810b10006e0707040724041200074040c0003031214441103c05403520405500081d92000c0d8246114605161f0501c1380150741106d44a140945146c0c88016894245c50781800e911001d01c0e40650f00c8028500c10031040000c14150070140d04250844180424031138140180341800e2942ca42c000e0707030000c13103212040d08010010007940460f04105c2980c800c000b460114914074250148100c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 989714595 1250 989713345 989713367
    0x60b041805090a1b080607081b03040c23061207030b0d0b01091a031e010e1605060a031b0c060f06120b0a02040b120a0e07030b130204090c0e0405060f0106 68
    0x110046003010064013035141c114420141103098151250f40c507003403502030701c01d0005840050744030080c140071000701e2450500b81d0303015582c01407094030103d01c4d00205124a0500d1003d06003c050084075901c00e0b651200003c1107101d4458001c4556860002d0001e000c4810040fa064010050300e08070800240c032075100c007030540380b59020009a03c507031029100340b11284000c0c12902742c030591211b00b6108400c60301100a640c1d400f40203114070f454074142c6a031070394540c080c001c2c004000044140554a851400b800c002d03215480d0018164840114000d903038280e40480401044a030400030041c49054001c121400c04000b005001052906400c000c0d220b948001c003800d44020040851400702d000d8048030001c2001d003121030780303455001a90725450607065490202540c9040000c0c03801c0c036004500030048913000030010304150385098542c2400c3c40300b00000c07a8002c4c0e8984095000800140203900580100000300c0c0c000d2410389001d80c0391100140c0344444010101c00100710607507102d044004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 989715845 1250 989714595 989714603
    0x4808010b010206010609270507030b03060c13210501060b0d0c180603020901120e010b0f241602090a0c0813050309011215030f021e1c0312060b041805090a 68
    0x81c1d0f02e641c7c410303001c00010150403940c2910700303003001d10844a9068001311441401101a01d40c00c3c0c480e82c1501d0100d01c5081342c000c1041c20309071410420b420351102d62950b18540e2801200321552300382d0340c403800c503034207900304000805022134a80381c0b04510744076001c031107012400c3c85010345c062014442c1030448148120810140c0004402c0c10a900c81d4500070602034030040140400601c42c003456000e042c1200020340101e82c5843c00c01d000b4900a004503004000c2c00303c40e6500741c1c08070f84c850506a448146000d0380303c12944801070058840070504c40c822030b80408000780c10380c100d12009101a002420f404101580e03e03d81c100030510100c100d801414003420412400c544a014101c0646240d0040c18400d04a8060010601840c00255030189200b260714030b071054140702420700643d440020a40d00211490015143c000d408089143e015000e4148110b4110380007101409450340790708030010007200450308100180941010246602d1010414089440c0001c1896603647c00c11038090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 989717095 1250 989715845 989715869
    0x1091d01261b13053d29070503030714090916180312020c03070e040f03030603081c060909081c060e040f120801034808010b010206010609 61
    0x41c2c015602c01d41d8581d4100c0000106003c94500031a003130500c540503540c1c0c1044040700100078010000307495804012a010840650406401d0010604082000c1250310b0f008a4003a070310b48078004a0040640301c02c81c400c80041da130f00c1c600040020600c0240c004404586282072015138419605c40e201e283d84052028407040c000c00c81048225400f00040700440b200b0b5058100100a00c00c8141c41001e40200315002c42e802c520344d24051550301c10309403249204940e00c0c4804a00090405406d140b8824003070314000c04c0043c0ca81c0c0303456031641c5c802400900300b80c05000320403902400f41d00412004004881d07007080f402d680c07500c03504820712031a004107800c40c68080c0703816030410640d88124041d10074034140014078038151030b1200024508440545190341e9088a0030070b0240b00b050620b041e2a408107054511403000c8194100030760780d01e0b885000e5010344007a05a98100d82c01c983e80c161420a001e106800340c41c01d40c4281c01c44206032600c40c11904900014130106030006080c80480b10107c03101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 989718345 1250 989717095 989717143
    0x1008010308180a170705031605030a03030209060d05250305220c091407030e0109020a12030c02030f07091b1407110a0605030a140402091501091d0126 66
    0x4856203801d8000f41c1c101d442c6134030105200a40090154182e4006404848099910800318416901d1078404c65a03d54840c01502c000244240c010b0500010060601400c00d04032035100c0301030310400c413200141c4112100c1c24008e0158003900b03000300760486080030825804c1c0040011961426040354204208006100c0f13010800f8500070720005040307403103042201800188a030940f0180a64075000000e041c1491200c4801040c86a1107450360b0040028030414a803481007540054882425400d1241c030300010409a201071010f01c000c85110400b41c03a1060500044c902101d00700d07441e2107001111046c1549203d500304450345160341501661503203503905072501d226030b0304a401d09280c100c2c016810005000d5000340140d401100d41e01001e0015441c6100c5000005c2003c84010b5448035182e00840e0880b4001410b0212501040c036001e070381d01e92240d980c4d400300426031000b8000a02000010002809001c6060284502ca41d0358940c4102a001920707940340d080518081003400d8032200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 989719595 1250 989718345 989718349
    0x30203040506071a010b0a08160302090915031002120103140f0d030203220b0402120a0c0b0a0e10050d0f0f09060c020d0e0d0b100b1305100801030818 66
    0x180c800401c0001c0110340c0e0345040d883d10203100e5a909801c05450b03c081400801c40740c141c035040d50f0850038944d54480c070503034514a10521028210714a1001d00d5420040c6148684508002c1c500ca400300c40f0224000c4011001814a00601800d4003501c2e2031040c0320000b8072b1000f003288241160b8100c0134121241c800340c1c01d001c0c1004865850540d4a10500360824240d44c2c05401031413003282604400e00d041e208a183d00e40008000004c014580c0b00608000342c0185004000855401002c0d000c840c0b41e07241a9807411544002074000c240705080100303000c07807481c0e8803035102c13048041d041d188207d0140c500e000140840c0920154802c5aa484803581c0074001125807003034410003a842014841d078503260900c8801000000081d0005004102c071042c043d03809030f440c4122100001d05210089012605d5894002802a082d41c0310700e100d030040007030055007150282100092041c0c1501c0d0640c03034041000600c00e40324820380e0a104100f40104085a19070041c0c8452001c4604c07400340c10000100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 989720845 1250 989719595 989719597
    0xd020102120304050d0807050c031b010204080d02070f0f080a06050703140c0d0f0b060703030e0a020d0c08070801050f040b060a170a060e011a12010f1d0c0910060c030203 75
    0x40344070341010000c01040107210000408100306034442d1104100c41e1a8000c0071202d900c10702c41000c9040c0e00800105095840202907403542c80b840c00d00040c00e05480c0d0030b1043c20f00c04c4c40300c1600016480010244100340603082d81000034880100e001e11130070301d004400343c0c4400c03003424041c008994800000304e203580242c010025000070800e216196161184041420742c1124102501f005d25203418585690f41c3da2040402525000346000d041c0361440d03070110044c0c241941e10a07154001e1107080c10041e101c18070312040c214402c0803080c2840d420070340341c689044030940c040d0b400c0382c1c10030301440b11b04909501015046900b0003900c9005581d8a00401c2c100328160317008101d503001e0320703602188212001c1908074000d4440c03a414042095000c1d46142a41c2056005040401c513400a6a6407441d101c0c03019085101c1c0d103800032680b0001c402e0080200c4000044130340500340e0700c401c8070000502c1880348640c94601155814418244440c0c7c41d0084174044c0a05020320440f08891001d05000700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 989722095 1250 989720845 989720863
    0x905101a09150a1107061706030d08011a0c010c050705150c09060702030a210216080c09040c080601061e0c0b060f0f120d0905030706120f0b042d0204140d020102 71
    0xc403080c0c146d481600520000030308002e0351001d002000450900d00d00403d45140780354460340c2d1100103908042a29400c0e20307000001e180d20300342c1086210030f04c80081c081c1114002d8140c4645072540c40c1401d005007071004203004007800500d0f0204001c02e0942d1007050303604c5803000759200d40d1030307401c50f2011924100c600400a031449445008140c1000780328441c0c44407090440d800d95900010030b1038891004800d500030034941e50000811309545062400201c0d6005010711701444829a4800c1200c1c01c01c030017038000400042c60310981841310138203c810210b14031010b1901c1003102d417207502d03903406c003100c05409548681448596061196100c032620b420718500203120520300d03c0f040460594408200c0701c4440400c3d0f00510015881c0b50204040301100c80545811800b01d800c0c0d0510310003003028040d28541d9a98417614550f4581b40ca00c00c2c080707641140801c05080502210074100c02015814100f038603580108014006401c0308610800062016503200c080309000d480181e0905d6800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 989723345 1250 989722095 989722127
    0x41208070218190209010c06020a091e081212060f0118230301110d0f200a0e0a060f05030c09041b080a0c09120c0905101a09150a 57
    0x140c525120520700721915020f22003d18001d41003c049045400607809004a140e0100740720300c0c0030401042d46a002030444001c28640700c0b50090303d494803480403032401c02101d80000d00b0030205000425040004811030b604c160717501800c1840700a01d070241c0725030081509014aa000001916a03409808491030b291020203049440035220a440ba050221500c840010403c50694512003400c06100354140c000d1010840b500c2d02504c981000c0c041e1110310810800d881c1e80d00d064800103400c401a262891000240040c0d0f207425164005002e03540d8403070601d00c1354104510410440350070402484002c40d1600b030844d1a40d0303461085103158001e24401580241c01c0081d546001c8220035040641c90006488810150b00c0314054023045403403120280c070100ba80c038038050091949007656103100e030303210b19294859151100b4a002c1650029541d5620000340003805001c001a500072071146480351840f618182055075000582c01800760004e501010380029031001c22034490180e2541140c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 989724595 1250 989723345 989723359
    0x30503040b0913050408220b0d020306010e01080603032b0525050301032d120305010807061404032a080d030f0b0d140114100806010e09030412080702 66
    0x524880c1d0005980851480351040c5003400c6403043e2a400d61003040c0c001c0c0c0e0029066401c1032043d070318888206809007048082844004000a02641c02d0001800907003080c1c580540ca0b0b040c040300141513090300d0b4440c1e5044c0806001005440e44001096403010a01c1c030048050010f141000c0250400c80102101c5446050204202520352a9002e01000f82e00300c0003580c0c440388910408865900003030100a101a00a00c103808150b43e0840f01d4100544000c0084030000741243c1c3c582801b11700c200c8030000800d403a48010884440c00340414802400c0600382980a074441c0603042c409481140401801488808a4030401000d0700c98104801c104c030038014440307980c981e00e81950f03030300d040b5000701f0010b8140300d14a00c04100351301038180c01402c013800107000071074140d85003810222840013100281d90380b64200d0f0380620156007100c8c00b500d003448144001e0744c1440d51007824080c0c16040480240c00c039200740700b00203c5c000115421203081c203101e0708d0340c2c1d2201d1400102c20310802e040a03501c904 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 989725845 1250 989724595 989724599
    0x1f05090c09030607020f060403031508060f040b0108120f0307260a1b0f080a150914010603090f241a0406050307080309041e0e03042d12030903050304 66
    0x4564001000a41d408804480469903a084101d03510404510a0005030b04400e0105002a000380c101280110700b1421164585031107100e100d14110341121071004110585090106024240140c240500246009811790748102d41d404c074210701c9240c1c002d8510000020004100a10921074000c84105000c1d442001d81c4043c10700399018501690081d010600d04011203101d0003414102c01c41d444c4507610b400c180722000d13000c141c0384580014039079190a9158500030b4000380804002402400900d00000396411420141d044a1201600500141460040c140300810b80903283d645060b5400312005c0e807502e15102e81c02441e8040303003500c1d480e060b040ca81c0704070104c4c102c03004403994548140c0e410000c00340e64004060b5614814480c0248640040021280904054000300c0462034844203c0d04404130156031101100d0500b0745000c160b0304007060170301202007403030b240d081144819004d60303000225840e00c15402920b02d02c992115011905034040030140500102d500868001c82640c2e02d8a03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 989727095 1250 989725845 989725861
    0x3110109050a030c0303050a0b220e030310030c080102030403140f0c03070b0a05090703200301020c0a030801030317041505070c1203050702121806130807030507091d061f0509 77
    0x212161100305c011a050200003201082c40b03204030900c960006140301c1c0e02c91000c01259110343c40420000740b0650300c5000c000e24048081000750f00030415841e0466000e895824a80c0d6480001d4001041e07590040040c000800e6000300c020f0076400f40420020340d9a101030a0020480c45400c00700e5070300780030205881c003e01400001951007160a59000d122940d100c41040d5210055800001c0200c1105410310140821610b600f58201c01d01400040c6050340d100c100720700e018007010003100007862140041c810143e02034440448a01d410012200500302561000c01801c2820651000c5030b686200080b00107205000007070b0200d42288000b0803c21021000401603d01103540b08054410154000b540007000d200b1138104400e03035a00c00080358200303410840103a001c910400760045400c1c0020076402000d124010056214900600c081d91418480d1000c0d505a0311221911907200e0060480c00d400110b0f40c644c2c0036517581650b0341d03203900f02d8130507848104442d045203801950305800c2080360 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 989728345 1250 989727095 989727107
    0x4031502070c1d0f101a040801060e040302120f0f12010e01060f0e2e020706020c0d1203050601140703080108060603070312050c1c020a021e060703110109050a03 71
    0x1090203508040c412507200d006010040030f080c0c510b0855084464006400e0078002060107403c500c1503141e0a010300d42e207015100d80041200300280c0100c0000400704940d00c02403144200514104000a807140381c180ca0203910b03001140504044040006401c01b488202c0b98101c1e0f10828054490700d0300d0710f071f0303400106070400c50901584604e0300d0f0000c00405c0302401110410000c05040d6100c4d40071180d05000c5c0172030302c000c9060f072002007040340c09088030070304442214040e10b040e20b5000700941c0e460300034000c0c5020002c0d48418004c021211840c03000c600c04860561441d113a0341000309003038035014012130f1110b40004010150ba4000b164140802d0b912520142c100c9164900b15070305502c03440c003050b46a001d244402800c032082c1648500c0712602134000380c524401d515003540c5840d0414000102039201c4440c507040141c2001003441c0444c0741c40c0c1c11007001881444000450b07000300c01c004c07030414031a061028081c0301c1400701e0208403010941021602c180d0140649100315002d00d001303082d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 989729595 1250 989728345 989728357
    0x1031416170c0613090b1c03110d0e0a06030e0717011e050114281d070c151d0a0803061f05030c0a180b0d06081605060f04031502 57
    0x90040b5070509403580b5295044c1d658074490b41300311224030b9140450060040c103104000c02d400c00c0c0910001b80054882d40d80003413207107010ba10764040c4441c654a0440c200340013400c4140c1481400450f00c1c1c402e0f150003107110152009418005100304603544586e1070540a9400941540c0103d200ca405404040d0007246200c85400d092100000c8400100b00c181c450074007036401c416a070360074001054908003c4414a0b41c01006140111043c00c20072241d4956250b0000d6000d62a0a50f80c4140e9a400052282d488032042c03034414440011580c8041d0340c08032040d0a011081d444013249000005500c4800d4440c407503103000c44940d1080c0f440c115030309800850340c41d4454545012a030b0000d549207a00c0a0100342107503140e03480c40d5a1080b610950360440200ba504124140c008516a00e416800046c00390036071048454407951000d8951083d200d0503040303a00340cad4001140c030203450103002007180f054900031560700383c640d0164009488035000d5540040d203841040d400080700f40d10264001c004d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 989730845 1250 989729595 989729639
    0x8070f08030405030a08090a0b070c14270c0d0f0621080d02071109070c02030c0d0f0227130302070905061c080408010c0513091401031416 61
    0x1225036954032039036280d01030340c42400c0d019041a1707804400a00413200030301d00d00d40002d000a14040d15460000030f990411901242c0a4040319000d02c946005042007020000b422510036004419a411004030002107140c041503c4036000042205070350744c0400e03501544070f10a002c118401580c0170a001408803441a03150641c1c1004406009003103444c1300303081c082d0704078240c545003c800314030b01ca009500401081d10040c0320040042400d66582c01c9803401091a0342c0d42003c491030310300400d411300a103d10000e00c10044a07041314001008080c0542e00144c040f194403110058110740400c0f2682c0003844aa1605d8564003001040031040e2100ca200c54002c1e130031548800d4540c1e0b1003904072042502c046521a0400094644505050410b2a01d01c0e104000c05420a0341d0f0b600c04a09440c0c0011641010460110f1004800f0044045000042c40b6040c01885042400c1e0241c143c0301606000103800600488904400c0220030007801c0003040f66081111407499540e01e04008100301981555 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 989732095 1250 989730845 989730869
    0x207060f050c1626070501020d060501050301080c120f010204030521030c0d02070f150221070509130b0a15180f06030f060b0d09170c0c090901150807 66
    0x6090710011509642c003d44032090034080380b8034a900d84079003c035a40c0c00c0304030b504032090b007079405030034402400b8012640c420000543c4682004203007106545c0c4503003101e07040040510042000f07003000030b00d0003600c1d54103507030709892180316040311420300e6855182c082d004c2d03000140c00820004000781182c0d2003c034200a8890208000103000640d100540e15000400c03c00e01a500d4802e50903030042a4040c80340c44800344940003a510040003a08041c0c0c240065940850000c1d01a80c0044420342d4040d90440319100c10b00d0141400fa00030301a503c4194026960303251480c000105960044198400042000c444142d07541c400c5104084c04010180c0010015025000a441d1541e541d40c26110b03590500000c0c0350400b80d00b1001004040e0900350b501d601d50a000403134020880c0105080d04400101240d084070605048130b4031505d20818420922040201c2100c40b6000b2030300c0c03480f0a0742280c0e11411a2108200b09024250801546058001008001413000c800258036000c4843c512100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 989733345 1250 989732095 989732101
    0x30f03090e10060e030307061b0e04020918060a030c03060204090b010203090904110315010b1809090a031803050f06040209010f03050c10091e0612050103021f09090207060f05 77
    0x1401c070740801a500301c00060100c0b18140201030059076a188a240050102c03410080151a4442036440e9544400460391854015082c880c0e80200350503d510340640f4203601e031200c03130000b1a81030028000880c0360641300c000821103955456184000940e00942824581606c80c10058003c0d4483c0c4180c1440360b207440e03071980607540003005648903210014034001d1603035190b8803001141c510b0404419850b005051070300318600b05c0218014041c1ca4141070071a2070701c03940c00801100084010846202d0420042080035041c4001a0700920036807604c1c2410040c1480319400060801a07000188180250907441460030400154280b240e4002c4802452690380c4044070001e01c2250f00001d0240e0304080e03041511824030980b078a001c15100d1600000e2250b0740c03111201e00c0c1405180f41014010007400410010b0303400b101e000c64001c5030801c100155490341d40061140d1010301c08010140e4403d000300f8000314094001c0700001d03c81a04203554231211494194000c0c00070201c2015510700e0710000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 989734595 1250 989733345 989733359
    0x7020106050a210312020a1d03030c0d03020906070804153b03030408060f040501051501050d0b0f0418141c050d091506030b0a090312020a18030f0309 66
    0x114000b220890301812030114040d06003c1c8030f5103550799094041c040703c160302601d40b100328401015000400d54804000b2801c00e1020500070341000c04081c480d41c400d001c502c5104e0360105801c41004894140140d45480020209803030340501540681800004200001e5404007240090003200503980c0c6c4c800031006981150300e1094680025100300726002218814880c01000f442041c1e40f8010201d0781803503a517000c490300e0403d00702c1c1c1c580c110415078014402008030034001e8a800400c1d21500400000c44580024a0b0340a0420480d40c3c00b41c50703558510f4251502101240e0980026100b4031101540054079400344038070040856020010403100c0b0f0400d4404a085200303544007104260b940e1101081c120703113541082e01ea010080eaa41c95a01c00050074610b010030020003103001c00706e0811300d1410710554500004000f519494240541180002d5101d0103605000308640c000580700c045600c0100e880b08450555070100380880700c004401c0c000e031106901012403082c0c1c2e68142403030715504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 989735845 1250 989734595 989734609
    0x301050a090c061805030307061d0303090a020d021807020303072003030c1c020c060411041a010815120c10140415140a12060b0c030414010918050702010605 69
    0x500034007058090030062003510710985605003c0420b401075010181d4030fa20000c2c0c11a171222030100d030b40c03036030750300345015001902b08915001152040145045280203800a511030807c101c00034031442c1d040603a501150350322880c1406d1004038852008640c0340504020359070307600941d040004617a404408a950000c0d0300d0b41d4191a814030f6005e10700b19205c43c100750020303401007406c1040070030010150f440300d0039492002d010100d003010001d0660741454204415881c0e030b001c1e242d500980c144203005002911407000701284480038a46004956919041b8840c6c0d20801c1400039400405c403201e9102c8500d0020b0380c1c0042c8072040f240307114104080c000030342d1740c500305200329983c4803001c0c041000254503541200c140d0901c0da003000180900074070701c01c0c21154003400c0d016000c03509070244122800c415109101c058420102d00d00d2070700c40c250507001c1d503038000d51007841010310f0605070414107a40b141204800800c0c084c950019602c103c000c0d040068941215507000640c40c089001505183c118 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 989737095 1250 989735845 989735861
    0x906021c120209030705060d02071110020a0b090309100c171912020f160b01090608030702060c010908041205100506061b01060512010b03060105041112190207110301050a 75
    0x20319a60030100030180210043d401c1190180d03414094684c00140c20f855240061080025100300142d44101c10b103000702c0d402500c1c4541d40d0103200090312510f1034540001d0240fa2417604801584100e0f528203441a2542c41030042e807a4001101031003000040340c00200f400d80c4d0500c51818940341c40000c0c842c00d00c503405009000020500d00d0314054102c1801040320b120765035503904015107006940030900e5056070081c000d030f1400422850000d130074000c00070051409000c10880a1000900d001201c960300e0140d02d902a1107404001811a04030000750710641c0199400b80807281c5840d82c1701c0b620589180080804d031390502404070201942e41c00d901c01c40f4401c240c02405036042c0211602c1005041520042070902076589180108259803001030303050030b4945032400803030314104c41d034141400d211041c1d01c01c50059041024410040b200102034421040d182c00a030070085d03450a8070360482000c1c42e0304c0003010520006200007401640c00300c070380c2c88070b0065000380141d07103414a000003256016 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 989738345 1250 989737095 989737097
    0x1a0a110d09061b0519060b04140a0f0e0604030f080115050717090901140102071e0b0310091113060509150306190e060306071b060b0103020f0a0906021c 67
    0x102606105140c0a1030715a07042802203101c0d101c41038141d41d02d03070303140080c01c5c1d0019a000507441026010400603024040d10584103450520046d400704003586540c00c0080d0400c0301361074030b0b2002c0040c1c0019a46c09005417400c450119101414141006401d00e0740000d81c9900154840e8004101080f4641c90b0070031b1350845035a55480d00b4107a88480300205000213045417125010041e400350b0307035103100320306000c0c004c105c0700f151403c038247e030000e49404815408010a4041210340c0d0310100e0071402d40e0400c94250859061303480d501d03c12000d5000d0007035000728032150303c1c118181c01030102c110081c1c48a8000210611323000703601d07100b09440b54003d180746503034000403110040b50f03080340a80c09590480c1010b08100d2110041348410a43d1401c1ca4101c4c0a02d4840f8004000f0fa500c1c08214040c0c00084a0904401c0d241320b01018405528650f0400341506171224a8080181d02c60750440d4211032002c0041c603161205844014000c006a1051600522801c0d422800054040c5d01000d2100c40e5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 989739595 1250 989738345 989738357
    0x18061514010309081b060117070f03082805090301060e15100318061b08061f1403040b06011d01020a06150b0403051c030204120303151a0a110d 63
    0x1a240114050810200b0455940805001c103801100c12614a425605d2141c8098501c03503042580348000c01003c0c0040d035446a011000812114480c00540303001d4036041000d0320342e101d0000c284612a154059400241e5503000c0001c103c0440e4000040c154941c2c040740240946559000c0800140c0d0003a10040030400300b0003160740f240d18100e400300454803041e0070041600140b9400002c4150340c81141904c819072560201d0590901203c05139000c08885d0500d5101d07070900e40c3c041051070b07030300c140c1d90206c08039035008200c5168050103c44000e503507200c8980d80e88c1d20780f43c07900c11041c0c481070b110603012034410380419881151090480c898500e040e40200308145a5403540c0000e480303c0c000141c40141210008505100c1040040c4084c40c0600001d048890101c2540b04445aa110030303e0304041c030500040c011a1024400c0484031909071802184070036440d41078401192a0780e001101440070030700c2c1c80042c1100003000c0e102c1c071aa10388480100c1c040e4480071648030100e0f14400000900 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 989740845 1250 989739595 989739629
    0x2070f05090a0e06070c1416060f050c16080c04061833030302060708010803120a020d150f170304210501050703090209060301290301090501180615 65
    0x1041c0c007495a01007142d01000c107101c84a110003d04101c001d90300c65000504403001541848102400070003c101008000d05086454003948001501c1501444c410041c10b803248000d09881017054a140a00320000e80d1201c80e000740150490b00003d215800c0346000e0001d01e442c3c907207424031400c0116007074452a50080b4a01e40c0382c000007440300c4051700704540040300704003c282038a5058442c0f12204800505482c0b030860401928200e001011002001144401400100c60120039a13103500d02502219209440c0c0c4850038000c4c4c014850b240f20031619242c0c030801c0c8003042c440e43d402100d81c500b01a9041e0303510707203050354408025200c00e1916940104801c21020407030b10112800c0c00c4150b040c954000d040750359400d0940d50103480f000d00103512914003109501c0c110203060f4204030214020041840714841e6110001450911600744d1501000541c4e00c5d91000e4112071034030b545c030000070094001a1142c1c4500c10a4428007038070468940099041101b509640c01010b41326440c0d0004500d007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 989742095 1250 989740845 989740849
    0x120c091206060d060f0e030d02030103050c060c0a0f0c0e0f070906030b0d02091b0d1a0f24091017060117010b03190903030504031d0a030f051608100b0102070f05 71
    0x46071017041001c031542c40c8410918410140081d02c8298410000581c1da945142416031070507034516100351140800b000400000000000c1300b4900b030398400001c07814403003035080c240081c50041d44400000c851520400c0045110041403500c0344145450308224280c41c0c1004030308494401c881281c009000b203003040058170702a0b80c4a540500c11200024920f0102842c1e0340068018002c1003051903141c120458031405011503803d000300381901e06030a19003410000900c2d8840444100034241c81c1c111102d5030b14001403080700c3e09100c000e00031241100344c0035001400c0351800c5402a12140c1144003107040d562007040034a0604c40f200c21021056420402040e4040e40302410380c0c190000390204605080641d80103002915000c0d071000116031a0906002d4220b4a040c054000340c241c0386400e10701140e88042415060b0713038200d0751049100fa41032804c540344c41c1d00c10b20304004c1041a03610006550500240340741c01c86810681c14440c0c5c0c13004034011b9075581a1400307030070000b0703104210510441c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 989743345 1250 989742095 989742101
    0x915130305030903040b0a39060515061309050f010f03031b0c0b030a0f09080f1804020c0f0d05040f0b070516230a030b04060b06120c091206060d06 65
    0x128140c50141c0786016a1035811b046980c1c000c10400000c02d9000782e41180c8220a004d81c0e20b000005004a111480080005682c03030303034400c1600a0103942e80c1c5022481c0c00f03e541a02c109502009010030b0b46d80ca4008041c151441304500c40c2d889440d0500d07000800030b0415001160484810b81441e070b118504640e01520720624a0b610400100b40000c00d46000c1101d100b0104010304203405030744c0c1c1d079007800c40042003034a15000c180b115880c1014801400280210b0450b48800715848030035490300300c5552200318070403500f5811540f09001041001f104407011840600c2c443c035040441c0d9000710881c0066425025511820390a14080000ac101d0010404010001c031449401500c000d01200b080d41049541039401941e1007038140e02d250000c0c4a01594010b0907101e0495405605600e5980c0321070fa481700003000101415150454640b5988806050307078041001008031103154980381c400e0600f240c000800381c40c070410354240c50804124010803101d02420300036010785800400ca440340400b07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 989744595 1250 989743345 989743351
    0x1030204140d03140f04060318052a09100501030501050d0809190b07050d020601080115051017090309130603030c0311070b2d0406052b090605091513030503 69
    0x20f1240700c40d134103403101c44481c00402d0541000d00340c4c01c1d00c95041003002400c84d0032101c20324550020000444011801c0001d0000c1e80b9500f01840f002e034075419072424502c203105604c5d100d41045281c818820b44110b858900416180d0a0340d0030891070303a0310001c000d54854a02c0e0090142c1030304014240c0d26040400000e010320041d50b48880e1003907991b42039400543d010241c01c0c1c566401c24441a0310603581070040d070b4010b280480091110b2415680d0040284100740700c3c80c1e114201e81000d04540764080d0405000d072499141242001c0d1804101303041c3c80f03a110360b002905c035a4804e6461b2010b0b550314401c40303003540d800d559040c0071b05030f0598050700c81200108d4207164510a141c40050070f94516030042080461070001d4442140c034940303000c100000707410321b0600b01e05020b010034403040740e1000c140e46003251203840c8002c240b04000c14800b400c04001500381040360030701d1f0101c404d00486d5001640610074440c110350140d064000403601c0c06405803810712402038800c641d0404070b0b10400c080c5030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 989745845 1250 989744595 989744597
    0x503240103060b0309010b1008011a181903060f2304050a200901091b0518030a030c0b090d050a110c0a030c050306070302090a050d060e011e060501030204140d03 71
    0x918691181903c1e40e00380c10884100d40b585e911f91401002034280f209445011544608102a040d4100f42c2c0390032840b13003100010444004080703003803d50082c90440350040e211000d8511a1540c0000381144414030160105640701c60600d41c1010040030588200c01181c11342000c0c0d44070051818010b41121000a0801c1c2d03007511440d0701000104900041e510003003800214140b0103921010188105224140c0c000000b0343d1504503900c0d00988040c60100c800d00d220301c0c1c000d907a082082102410800340c00c400503050b110701c0720140200764012000d014072034014800070303850f0790700d10070000c0d9070710420306d030b6240081c8050209844c6c883c001d89100503411018020b640000704054003141c1a00f00a030310590784404c1c0510104140e040a001c0150000e0103440d05601c0c001545001c141410b01511409000d09842407116047c03140642c0400f4003004080000d0150300a550203040382d0901c0075102801e0030340b40c030000050350b40c020b02c04c80d000c0340c4400319000c07030400703982c410000d001407800e2081d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 989747095 1250 989745845 989745851
    0x50307030b270f101104050f01020f12030a0612020a03060203060a08030d0203010608070203210612030a0f11011e0504020a030b0702011a040501050609130f090809100503240103 78
    0x802d030010704030300c42c001c40c40e0408020040603442c080814a0001c00c28891041d56140110503110307105034204890644d442a030f565500c4501800c0105d251400b1585600380b24059585030303070301c5401101e00948c02542c80d02810312910340c60310622140b0141520000b54030241080c02040010b01c00c2d005503038032a1004014120281d920b0a095085522450750b840b405c0c2d90000061120382d4102100541081d61032004505000b00700240002c07143d41e442a041081d43c909001136881d648015030b540d00446010b00b07680d264007810901612440507400c0c07020102e1218070018607041014410a6440c0f2849100800d0048030441088020140600b0907a04060900004004150800c0c801c90044126a00006001100c825514480040c084946101d00d0500c80104066039a540170345154000071940c16034a1111440180001d00c05004402000350500c5102c105210600c000391400b000182c420340e507100c61205085034148021101080a4603a2903844800242100010b0072074141c181800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 989748201 1106 989747095 989747131
    0x20907030e0a1104480912020d02090903040e010509060f010f030902030f0a02011101060b0f0a020a061404050d020a200a030c17070f050307030b 64
    0x50b08034039601a03c901180e40d5030b441040450480d400104199440701005c200000150003520810464104c0c428100e40103042c080905034103aa562100309810101c000c0e00003402c0d06802e80c0c0048d040d442d460010388881c510240a019068010340e2103d103014036012a2002c16080f0724000c050701400e001c0d4680390090000020304090800c2c0700408a055002c4005180d124000b81d818403c4000c0c840015801154144409000707985604260815004041c240c07103041c0324040c14031800b00800303054044150064580c0c0c51161054801d20711307868030303240d007610804914001d00122150074001040400c20044690004d035002805940c40d8540741e000500c1600d54a189441032814084103565445103100405107500600313200056442e1207240800c207181000840341c9120b4420040b5510421040200490714000c1c003d0200d64150b60703440200b01805002d00100c1300d03052903a = true := by decide +kernel

theorem cover : BRFrame.Cov 989568345 989748201 := by
  have h0 := BRFrame.cov_init 989568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 989568345 ≤ n) (h2 : n < 989748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
