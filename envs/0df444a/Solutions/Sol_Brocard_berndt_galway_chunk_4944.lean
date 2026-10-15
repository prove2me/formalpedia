-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4944
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:14:19.027027+00:00
-- url     : https://prove2.me/submissions/8ba798c4-5844-4430-9102-459d9788395b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 889028776 ≤ n < 889208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 889030026 1250 889028776 889028783
    0xf0703050c090303070b220201170c1b0f010c0201020a09050d0c030f08180409030e0d1406011818230a08130e06090601200f030d060609080f030306100507 68
    0x411703143c0030000c100c40c00c1400b400d8140c5040c652948221005404280c0590300280011a443c00501c042e0041d081d440750000e5245000d01c1c18060540e00c29421802c6003403002c00d441e4010398071100030450030f02c203030304070710000f0b100940c605010068003a11000e520320446000d042c90303001c40800d102d04104080c002d10b5010482078005061b9003000c45213030300a0b0307540d80350902102c0004000b51400c0d22915104590684500d0203040c00b4004005090b05070140540d030108580081c0b2201c01000d200884c0a0101c100060401c210150000c2040321011641a0940314075144410b011480b1300360501030040f00b1007005400b4079540c0407100e00f48000d1860003441c03800081403450302268803480c2d8009a60b011030960700c2a84e0381e5401c21039141001e03034016010032101c44d0000101241c8264400e05501e000007240c4042180c2000c00e40f440e4040700f940744213503544d0348061111652100d0110000c0100300c0080c4507401c0c5072840c80da100d11002e00601c0c071a0300c3c42c10040000901800540d40d45541 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 889031276 1250 889030026 889030033
    0x609211d01021b01052a070b031b071b1701060f051f140d060302010f0309170a020a0b0a061a07081c180605070201060b1e0f0c070303030c170f0703050c0903 69
    0x800071a030b1034000c1e000d0156005401407c0c0b022800041c11400ea900c104130440d02640103110030a000b410701d03803288206507032810000700307900c010f5001d42c1d1604004003500d09100050703103041e881660071141240c00c04008c00307401420810a5a984500c3e062410314400400502c84003540c00c242c91030080352450080300d07180452405110b0b050303680305104880c007c0c0c03258001c900d00401c00b101201c1540e0b100801c80403003041c58074034543c50742c03002e820580243e00427104071000c140c0781c021511404031200d48400ba26150706003c01b00e90701c40b20084140068840d6414050190390309202c9029445141450064100c0644910b005076044101102c40010121103510f4103814000d024010442d502d001560a2541c00110b099541040700c2941040700d81894094843c13000c100030540c0304400e5684091014801240d40e101c0c20300851009500c66100000d841807450b4010342038600150b801d10042c13580d0010850503102c24441c841e440801458001520340da0341100344070701c1c00307a40e212a40611 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 889032526 1250 889031276 889031317
    0xe150606161a06040f020a02030a11100f0911060a02030711030c09040f05010c0e0d080304021923030c0a0e13051606091a0a08040609211d01021b0105 66
    0x900d4166004400c01ea600340304940c045d14002c416071081c0440303440141d0040000c1c92a02c0d12507114800202e01c1c00b000d0310300f11107401118209032004101b5203000726546140490801c0480700c489014010305890a508016a07040d0194a0340070717210000e0056121840303a500b5503a018403150088440083c11b00715181803908120340b5030702c0c50120440d0a50304c0c01c5d01c11003c0d5801120b451700006801892502540201c0d070b90580a500058000c80c2c120b11201440c08660307071554100c42c007400c010740c000c0c0740b800306000c4050943c000709003003a4003e802c0b0344141111a00c41d59004001c2d0307040088036406549410300e14030b2504032500c00c060958081c900382d441c10380404000c207400b19801d03603035403104541d2180c00300c007d400134604079900555030030481c4a071a18040c0407229405401000b0001c1d00020a8880e10b1a80030b442500082c81c03010400e1742100950020204410402c501d001e40c020019980c0000c2d64a08030402c14041600d10324a1280a40c0e22403800c440d4580590380a09200700b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 889033776 1250 889032526 889032563
    0x30b0103080c0609012a120908190302040b0d0e0a060e0304050a0806104a0a0203060d061a06070b090d050708030c0a12020c060a0e15060616 62
    0x2600a0502ca2115001c2c2e0070106440740014020103c04903413952203c00551246291008001c0d000100c00043c01103080176208042403501c5a0820340c0e000c0c0d442c0300e5407802400c004600b04642d0700414818144140414001c468001c8140e07100d80031240d000248803c140794440345406224070340100218104951001c08080120103042140d90035180644403941b105800b64a9100031100ca8040f407040c2202080034061034448003001e40140701e12004201100c00000c0c806015403800300c08203441c403a80300d203c00c07150020a6031348489026011030550034040c0014089040d03a0310080c084a450340c40c03520580544160114903c44020310440e42e450f1030380381c141d000700300448a59042d409081c5100b05401d00441c00c07180c0c11703079121058500d151780da0900102503800ca103000c042007000c605d03a410900030a47c40104000c50082e0010220780c684600d4070425144403030f00451440e00305a44216a07882c818403220b4100341c00300e170b00980b10007007104c121740d440606031006130212001943c0c0c5e6104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 889035026 1250 889033776 889033793
    0xf270b060f070c15020109170306012a0506011203020a170d0612050601140a06030c0e0409050c0f060f0a0c0212011d0f010603030f110129010306050d081210030b0103 73
    0x840303c0e1401080ca400341040011303422154419000760100a44104249043c0f040314009c543c04a0b0504010101020560032060134011400d906040d050090207280b06100e802c108841c0101021658941e17138544c0d41c0e40094944071110320080036000c14868142400c030808007543d001c07040b0301800300000343e52201030030410a6512000e81d502d002c0c110022400c0f0030300180d806030488000c0c1c0940348403480c100d07003240103080c942c0e0b840040110242c1c030600c4560359806841c0180340070740010500c900300202003201118003480080d2050314100130305041302014400340d41042e5114100356825280302d00101e42e030088903429035592946040c6c040038503280321110401600071050200c074040315414010900b04c0b50300307000203008550307044003000070148a030080300305245100e030004c14850306c480660400c246240c4041081d000c41c070f080b5500035581c140304840040c2000ca075428140052030710b446a842c0300d0310a01401c518a40c60010343d19400500682004540c032028040007503a590a02c042d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 889036276 1250 889035026 889035029
    0x4030b0901020301140603090304030813140a050307090c110111031605030c030a0c0c02120c10021c0302251101120b01090603050726010f270b060f070c 67
    0xa08842010108044000501c280c90585903010203403a4031190b650300300800b0307400082400a5902c010040800094100c2e0b000d082e805003404003410400d0304140301e403440f1441404010b401141142820001c42d03038005800c500311002c1071030015035010480c5c000c8442c042041482c02441d820080714402c0b0a803520300561003850029440c0ea441115880110303450b1006035001410300d04144041156110075078068009045603080c10700d450b0f800c56021a002d15005e00d0f04242c5608004c0340d060702424030000c0b9003442d001e148060301c42c030906030b0410641005940414020140d0200d841d40c48100804242c000301e803030b0400c0c0c20202404034a40b144042100c00f4020780010082500440c00c0b030040d001d16850160144c58001c0e00d80d0600000710000c100051217802080a0a889200c200d9540c070004d180240c82d49040186030360416815804400321580100074448903070b002d40c0c14030702100c580c060078914010b0002c04c641400c00300080300da0007044116a4101c0c0300140d0001004440b201120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 889037526 1250 889036276 889036283
    0x30804150806030a050d03050c0d1503021f020a1106070803010f0f050a080604150b0a03080c1e070b03091c0815030d05161a0403020a050c0301091a0a0b150403 70
    0x1c1e015915241031503214151410000d01c20750002031011400c5d80a50445903110101c0c100c1305060515154541d8141c48200e03100e03000300c90000d102402982410080701681c0c910a5421454917000000000d5540000000c0a8010045426198419079854040303c68451700409002d40701c1d48c445809424001c124480c94541d058400c0780020300d070030300000c0c0b4011a1800c60240199581d2901c034903c1221404004641039640c65120b813105a0315070f00500042c60140710302d07580307036070400915a181200790f1007110180c001d440d1062461380e50004231a0140c400d1503440544940b6040421468200040444552144003903000c0800540c0100745610918050110348249000d9005058441070890000800070b4000c1220b103080000c6d150088142d41d118000600140400a80c80031003450165412001a00147d048006029080011104003103007100208802c58103559501c0d1280100c003420011700c0e0011000a0410b00640d00505d0880e6001d0071500c400c1d000d041c904070072544140006c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 889038776 1250 889037526 889037537
    0x929190306061b03110c151201050a1a1e031521100207141204050111030f0403060e210a0f11060105010e06040815180d0c11040603080415 61
    0x400b2440b03218071451829200b0440e980c11110303034600f00e60190341011041d500340700b05c1c0c4500000b0386451101c5040034441660303440e1680e01c000000007420340c043e40000e100e900200c2c030500400610001c030706000c2d5201c003401580d418030403e01342c1e44c4000b680d28074a0b00860200410040d03a20111050131050300484a01a00c281c540102c07280e84070f40309a44041e107502840c8203400c00400ea500800301c850140e01c071200c405202c40c000c149003444002c548041d10002040c1042039507000010800d51064041c003035800c0c0211911401c92070b0141c9e20000e0013044d2107a5500c00401814403841c6580300313600c0c00c803c1012013a00404540eaa01c4403100d180020444a06c0040d090320410445440d10a2803024280300d910740401101c0b030b03030307041e100b6039070300401c1000300240040c810017004c80d6036044910039000a2500d1003a1644200d503140e60300445800c910208a0007590249800e0035040d444401d29051048000115005240c1a04000c164480010700460b001c042a60320342584112544d40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 889040026 1250 889038776 889038779
    0x22031b140103090b0a0c020a051c030e0706020a030f090308191d15070501062d0e0114010c05010e031204060e01091e0302011b050909090d0929190306 66
    0x110304580403c1e40c003910604104000c00e04070410381d080024680340b5441118032003805ea4403454100b520344144420146242010080e11580600800c4406408c85028160b0207180180103500c072074004200500b0404a1821004a01d018801903400785410200c556203a100440b03540c0b03a00130f514072641c004114044171071104803084003a040346110001e0704c91840b951a0307078080e10b20341d001301e28200c91654840c400407401c164130711030950303004500f04017130a081c80c0f44070f100c1d240307000380303071b000072440d485100e0041c4514403107041c500a070b9084c2884c220100040740c0c14414010800000068107034000080d2003a940c0c114030490b0f80c01507010361820060710306e070000c0950888000240080c1100074110503401c450b0710b41180e000032139009000200f01c071203400102d441d081196007240700226801141050382810445207450340301c0700d800000c0108503841a80948101c074a48100513442c12001010724201c0b00c94003040d0413180000403500c0c1c4840711401ca90300101000100c110010380f80690 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 889041276 1250 889040026 889040029
    0x1c0305120f060d03111014070e010201060b03010501080a14070c02010905030c0a060f11060f0a0516020613060906021305180705030402090618090303100806040822031b14 75
    0x26103001d60801409550f50015a5400781c800300103192080105000d9101c1a258183c00ca0061075485080c10307800b48074514054001420a054100043c0c3c1168034050041c05000101000c490641c1e0b801d00b0300c0c48644c1d40c3c805119014101d80031080001c3c1150100f4031200c51740119140c01514401d885200c0342c15190000c0c503540700d4012441c1070f444501d00504000242c0031318085110181545441400c0c0c0741404000c41c0707040401d840e00c0400c0c0240c01c3c200a440042031051503045861030414001e4440c040100a6480d01d026002a80c1e940290140404020b1580c3c0a4100140e000d0010340d29002d0660700c0f11000e00651007458040c7d0382d007400c60802121010b541500c149171544401d03003140c0752074092040301d0000a201540114207080728407118034114030400d108104181c0103555918140c0e00c07000040440d540030404c01e47c414024007001803011402e40e0120b41c0425070704c80c81c0c9000d0706003103020004c0e56840500224114400d80a02b28045425041034805480d413407400c0c9400b640 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 889042526 1250 889041276 889041301
    0x501021c110d110c0a05100b0405060a030201270e040c0803040f0e04020a08030c010b040c0e011403040602091012050f011409060111030d06031b030c141c030512 71
    0x2941c40c25028410003206148006580c00490100300c2481c80c141003040901c40c0320f1601d28008004d8826034001e1014600310040342c0200b103404070041d1011710407070500001040703c20702c0b1808000d05110301261700c3c902540d00c00d21101070701040440c00f410180c3c0e48441c03c03810000c00355019104a0f140c204089416040041141c003110305d608401103031310b07240c00314240b100c04002e04101c1c0c1c0030000440004140c802000030b07050101410000240e0b210504040000301c0b000401c8540600c00040c8000180741e800407a50400c0d01034088045540c2d60361071404c1002446050b241d60761003410504e0722043e8990144006000c0310039000204595254102d083d220b0010910481c0441d00070142040b11a08041c1d5001e50040010b04000c0c406c2c210350300e03009040da000443c146038000d944490400501c00c00007681c40e481494942c04805e002d040d900c4200d41002c0b01e0080c01c1c0c01e2034017807481306183d4803000c031100c1c040c0201c15231079242d221031490000e216512440702d1020701509100401c000072450b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 889043776 1250 889042526 889042541
    0x1e0f0602030d0203060103090b04030e0a0503060c090103020309010902030a0b041518080901120515040506040e03091009032f09061c1e0f0201230301170307020a030501021c 76
    0x390000c60420141001d0b80002e907100500c418101074885030f0400c000f850041000340594840d40760500310300c200e80c09006987c0082d074045403183d0b000717909102c100c60801d411641c007041e00f86000350faa0350340d8401c5140035040c650002034251181028034418007421002c880d00907845003000004200c03000f400b610590740000341566462250303285600000e45010010b10903140c043c18600c65100001c001c0c4000c90384100d4010002c41e031a1100c95034540391500c80c09520a00450f410058071404c08a86903990180104082c0150103080e02d050b451401030b02d1080056900494040d41d60985400300500c0c410070313030304d2088464508040300040c1c2c50580c02d0a4842e960140c10451030904820020f0480000200c0c1a01c9009001c40d4005130782c1607508036400c1090103010041c2c1c025115100040c1740c411005054254511031f0104010141c0e031600c02ca904480c0d907140c05005152940790124110b100e0720900a6020010f20300c004100f00044d0050400154400c20000340400040c0c118000d0300c192 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 889045026 1250 889043776 889043789
    0x2d0301050d060b1c17030907060f17101502070e0402010c08070b0a0b0405010602240a060b030c13061b0809180406061e0b0706020d061511120708120601181e0f 70
    0x603423010300046205842d055110b400914081004c0c4200401c4039489440a50b0414076070a4400b1003841803411039504401c20b030005200030580c00307181a0f00c5030940031001c0c0009040104200c40303c0140001c920641c1d40712030700880c81540500f0010300d02e000900c0d07541191400b0344e0805000180490010a40d000c40d01d8a01c400c0307203000b10303c612041c000c0d408028150f01c08070303a403407001003604410500914440e03209041440c0d030b01c10080300f1404001081c4e501900412030780070185108008100e4900e075103a5404041075899000500c00907050040d4483c0c442c0c0c2ca00c411800300000c1c010180c1010045a040d4002e081c0d10421080c1c21142e0300d5040d0042e0b00010200300601c0000a071b013a03001f802115040c0a000654940360710040e05075090581880c0c000070402400704031010410700c8000001d03015507218915200480e651100c2a002d080510303640c1c1103441d0005460359010b1049107900a501140d4800925200d9240c81c080b0344a145205040320a10840450020741c4008070009a841 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 889046276 1250 889045026 889045033
    0x31f0b2505030c1006061202091e011812020406090605010203070303020f2502090705310806180c0607120c0302120c011508300903030d022d0301050d060b1c170309 72
    0x40b5084d45020294280c056810018089000301ccc3c40c41c0c4d1464540003070443d44820042c4501c3d07900401099580c26084801d180e0301c2c03d0010849603030000111040309926040140c3c685d13403098080400c1c0c1c020412484000315103640a00c0300c0c01e41ca0092411650300c215500c41441c1c0b20500d00726454001c03810940c4c104106500d0031640382030f0941c480116503c0b10304000740d02c25240c424103414200b040c4e4410401c0f10f0681001496407800340902c054104c420388407d81480e1160312075240c03104414a0180a00c441044210103043c824050b1440d20498441c05503038805400030554000c28072a150b0000600d00381d02c010500d260041080c2c0300700c5e4075400042d054000c1000c1300880c1c081e10b120f10540048010042e450b5207840500190502a82c013640040c0c985e0500140e0b125880c440005507000c103407009190300d520883c0c04069a0545501382c0750032403800480d00d451002400d1442c0d2040d4420100018a15801d180e1101000240d20900d03150ba40417143c0c6500b00c1c00e60209440301d246903003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 889047526 1250 889046276 889046299
    0x41805071e1b020d1205071a040b04020405251119170c1c050417060412030c0905030a0b0a06050901030b01060e01050f031f0b2505030c100606120209 66
    0x2001103500e22600050040c603d015465460100107840710f102d543c08524040f6842003031121040102c6551008e100c1d0712a06450603540d0703450303c008000c0000340708903034031804510109a001008080910400200b01d074082034031078050281c03a94100c50700d0240c81803002c4010410040c4c0c0b80802042c0e841040b03031545050514000d6002d03005000740d000d451060b9003403481d440c080c8500d07540e002d5003030351641c9580d9410f0241e00d00e400c0084296440d503e030f0010042c0710024250003404608241c15140004402c04000d60403515a2065031041d42e1602c00c6c070310b04105004030f0090381c40c020803001d40c0422119542d00c0034800902024800904080c0c800c4004010090261940c50720303162051412a04e00300203041d0b80e010b43d40007070f41c6119000f82c0700c60800005008440011002c1c02c20b03070741c105003030050900d08028003150307198070140400d40451104d01080000c00035183c0074042202600e10031425180294014803840c0706100005056a1513039a07800300910842d000c1200203001c000111 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 889048776 1250 889047526 889047557
    0x100305060a1107140c060a0806100c050c01180f030503031906150e130f050402030106170c15070f1202060601030b090a091b0b041e060f080705041805071e 68
    0x501040801c080207018004005c4c0c1566039520080c100c20390643c0b910390301c44c00d080007800140d910b02c56414060003e4204100007085001072182020340c000d00e42004010382280f0799100307540302940a0044403001000200810001001030351240e03030841c0c100074004682540800c20303100d02d4801d12500040003044480420710440b6180d91411001c3c089091074031003607140b001201d01540f42c42920a03529001c0c40f04600e8280508802459030f1a41c035060154017141032078868504403812072217002c22905000d10700802400740e4544607013052603050003c040781001d1500e8142c002e02680117000d07070b0000880390740c02407244080410000e81213119590742c610308240101a6858141c9140148600d40300c454801401d28101411102e0710541d00c440c5003041c02c41d421044840c40c1c03100724025400510603280d211031300c0c40ea9040c1da4502912183c4980c0c000303840314031a0740c010140701c155800e4280c400d41700b40d030491030180349255207541c00040007903001c0300300f03025400411001400b000329a0408 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 889050026 1250 889048776 889048793
    0x140606120703021c060602010e010b0915030a141c0219171603031b0806300109030f0f050703021b13020c0c0109081501030209070c0b100305060a1107 66
    0xc0740700d06005151240c8400d408826075400c1031403102440c2ca5100920803d42e0a00841c0e9000f41070030000e00c0800d038114000707100360500600da030b03540d041d180c0706404e89641c0130000056040d0b040880c43d40142000d04003961598030000e1803c408d070660f50444218a840001d41c0602d034000b540082c403400f00503517610401d0005240784c0480f00c40c000e0104000c1280c003a44c00040303a074825180011106110041c2000803291100401d05005011017041050788506c00c20b120782e000070000d2910207040d811007000922807030301d520156642ca802c01030000c064220503000400c00454852848107091072030201d42620400c48000c0060700041c1e003442541005220780c060490004043c803a00340411105c0700c040746c012140e0010700e54040d1030b41700000c5d6080001c00024001440c0500702c40c945004000c001c450041c030000340544009000914020312407540e07180313043d42c006510101810889001c080c100da82c3c4c0000e6509000d40e802040030408903200b06e00f90081180c00380381c18200c041d00c603c0803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 889051276 1250 889050026 889050031
    0x11070b0402180f0a090f081b0f0d0c1506170f010612030c0b060a120605060a05100503130c0504020c0604030e0604060c021314090d120902060d0f0b12030d14060612 72
    0x1d5410031b42c042c680002e084c400c050007190011f075440f6000700605180301d43c40c200c1d580440380141d030840c03e078814080b584030041d8506190801801c010302800128500001c1480d40d010540580c8440c0e01110048004120b250056541c44001d021640d2a0341605648071682440100401c40c00400c4400040c501e048007903008a0081019610a5407085500e4054000c00d4045511642d03032010801c080c6051040e04010340425191903d5808016502421034030003d00076100e03641b030110055042003010521a40500740c050010b54813010358000a5a44442c02d48045010aa00041207219800e00c141500e003210520350722079141403c1c0341c0a1150402000035412440c6445c0c000b040b1200da25001c00c40e000b461b17024010310f80c183e010302c8000c103d400768400c002c2da15402d01e44c1510141c2e80b0041580d40440b040e1a00040c3c0c00e0560860000901d0103403c12a00b15040041c02d0603003000103c0a00000408480c00740140d00e040040c104101104480c200ea010303800380304030211215552000755 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 889052526 1250 889051276 889051283
    0x7051c06051308190215070f081302180108010c1d010e010509040c020d14030903040e1909051e070b04140604030606030c031518021311070b0402180f0a09 68
    0x4000e6450710b031403c899218100c500480350b44001c01e800240c3d41040a4060389400c864103000300d06007068010310240c10701648804200f607080200b03d040c03680d84035040d511540280000f94000c000c4401c1600b1034001d2246500e1544bc100050300110300400345014581c40760482444440c04440064444211074690300f4100503007401f00c0210fa8071503100d1002000d209030010310ac2c80c64460750003421601101910a4076180501c00c0c0070301d03018008292826908e42c0184c0d030419a955030440c0c0c60405948038802a054140010201800307004501e00c80715000301c00583c28603205074001d0580d0b0710311612403040145001c11042203400c3c0000b40800c040038004001a02d020f40c7c80c1c035404103650704c90700b0943d0403107283c074420000c2203041c01c407aa0114410445c05d001a440c101c01c1214501c1c0c1441d4041d000d05440001c01d060310890780e11001d0070250620407107845035114201181000c1c0122022405655030900101c0c03800e2001c8006445521230b010703030010700da0368a0000e02c003800c0080402c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 889053776 1250 889052526 889052551
    0x903030b0f012c0a080115051503010e150607110901050a23060c100b030c0f01170406110c10060602030f030a0e0703081207020c0a0f09020c0c040509070807051c0605 73
    0x19450f0782d0b51800d0282c000c1c504400045805420741c680040c0c040095030101d44184000036400000c11403c030103982c1103647d80644445255a10b070550580a0442c0d0314456202200140440800030300d40f081c5035480030140c6203103545a8984040c0b100d80605401641140040d80150450743c1000d00d003940d0890340c000e8881c0d8180f0b80c0121031946030108103542078004584a0000c84094201001840c1020304211001d03509803082c84000b800002003a8031610141e00c182001a080c02850340018591204040c42c4a0f0b90706d001085840d1a4800c1d000300044150402d000050040d00c0041564207200d49066214555110254100001c1443c41054092805200400804614440c000e0030b903000411140341d003280b0f0040130080c01c1c000c9402105100d40d00e020f00a01c503800354012000f003602d40112005a032800100016850020785103101c582c441c2c2040104042c2c4000861000304507980481120300040d19001040200e641c41118803542800c06101940440d0b001e4110740d41182840b800d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 889055026 1250 889053776 889053857
    0xa1e0803040609151713060e1c0206010801061d090c0402030f0f0a1103010902070c150905011d03030f070602070c0e1014060708071707060903030b0f01 67
    0x4241103400a42c400000318550000400c0541c1e0640380c0e03481160460328190b10206500301e051424454007904010003808130082d07007401c1101030303801031034940c000401301d410038150704159254000d0f40110040050090100009102c803050089500362080100207030400512035003244540031004084200620488209600c1610b952004502600f0460352203101ca10f000e0000300d1499a010341054041c51404600d0060b1180c28020f490540711174140159940b00141010442c4003880d03080000d54203180018400815001400b0b40125082a220142c0d9900118039503015401102101034241d08200120384290350070b40010b007032562040000600700892621007611b0380d20242c0141e07401c10001020701182c1484003200b01300a00358100355441e219074003000f0039200d00419a0003001240046400c00400075a60550361042400520182e261140e605101c0043e08101c03605402003480d07d0952200e50511010750385c0c40f201d06854203001c200e51840142400d00e40144414880c2081c01003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 889056276 1250 889055026 889055039
    0x40e0415090602090406050102160308031b0301080c1c030813020d08120901150602030f03040203030412050d120e032b1509180209161b030804120e0a1e 67
    0x2501d00080d02607a00107071141500c400b440b003203504941146049d03510010300c0d24400300e40d88041c94183c9070320a50164882e00c440000c0300021880c7c481d01d4010718400700000c10290400541d016090900b11144010f12592564030744030b50380394030380150008172034400068840c10304c01c1000340c00c5803025254611a0001e601c41203486d4121600c0106102003010902c01d10789001d029503000d4044010a800c01146055006903a0744200309112003403001c007000103000e650703081c010744004112251030a56009081e16115488541c02c1d556003000c5624109032165080c074a10541d44400c007100c004524114106002e1842d040c48904484c000303c0d00e505003681da104407400340072010880c009140c251a030a1030400d030140d41500c3c10080d0318089840c040700260b82d031500159003119101c4091843c6c44a00d03101154414060707507410780c083c80c0549070b040c00c041d448003002d8810b80c000e4404225080c2c0820044440301c0d0741da421250f2084c0800410b115855545000644105020405040c46030b502e40c07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 889057526 1250 889056276 889056281
    0x70602030705091f080109060b04180207050102130915141e10050d1d071502070302030a0c050f011103190c021305100801090203030711030c04050c0a09080f03040e0415 74
    0x40e04c00ba2490031884845815003100d803450140030080000d010181c1030403211042402503210f022141c1e25540c005180c0b258070340d41100c4417990400001c2d03607a00418800800c0f100d41922458007824584400302103944c480001d01ca0940b80500850301080900c10104a0f0390b4400107a01000d1400b0340142903130030354074040006810307095038680c29114000502c0f1281200e903203211085007014201140040c40d480460010241e50010242030f014034080101249842ea83d034000a42611a83c000300c01802107901040b400c540e011030705c0081412040c0c0044801c0c2510401c1e01c90260f0042c0800e040005410482100c1d02802e0700e09501d0700403450700019010580c900790041d62030b69a5090128034400c03240000080c0c01820020300050f141c41e4040780d602c1c0b00784200540040541c1d40e10003050f950621001c416207400510074040b03410b00b055a0600d5a0003043d2120201e800010700080c00e0801091100d2640c0c2c100300614109441d2007900440180000e00403581a21004c040c40c40e0140d051 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 889058776 1250 889057526 889057549
    0x92b081e07080106020d08040b071b0b0c13050f011d030c0303030a050a0c0c0f151407121b1b020103060317070c1a310b0706061a07060203070509 64
    0x3030360b68140340e501d003940c00785c185013100e0300b04020000b0324004c01000c035150482c800c1d00050107140501d401d128203c4004601c01c881a801410682c640090188440d2480b000c1d0807109071210906c6142903590040200030040b1041c0640032604d9400804801e82c0e80d0f141441040300040d050b41c0f42c200c0e040000904543c4121130703c6002d640c4ea4000d110f040c00880c0f00d1000309040714280800012401d865240c0e040b485182d000b480109010005a884242500701d18003111250b014160079040c0518050049240c14121000807840d280307070400007181100300340300c119065407106d0110646407007003403007451300160044c0d042c15200e51001000074400c0505000e0460000c008588501c4c0600e17100495010340d1307104580f21703608002a00444544041201c4040800035003051448040d80c011042e201c00454040a800310040400280da002001c01400d02a200702002c106098403804180c0099003c131018981c01d9105001410004807164002d54200340c0c0707030422600303100c903140000b81640b090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 889060026 1250 889058776 889058791
    0x90a05190b04151d060d03050717040906031218120809060712120b150a11121c050604060b0922110406020f0c0102062a040905092b081e 60
    0x18407130b44c01941d46420682d03d40280c401c546100c8458003d8500030490301500c1005409206e111441d80c040c81a40401c540c001c001002c810702c54141d132402c001c65945540100580864105808070001030300000301d00003600e00d0040f126030030012176207844100c2d8004c214550b030040e0080001c90089580448030156001c41d139a0f038144440b4070500c0e014241d03044680420b004410031256200c8005088007075a9654220b85450450419444201c03854225540e402400010700001c608803100001d0400060780706034a1010301c66030f200c0c5002d02c4221103440c414114216000c0c45514118900400040a045003036011a0700e145036500f8403108642d004074120400d20760000d402c00403103406000c2e02c80c08400203006440780b0064500040d40b030b001c009000a402c1d03c0d544c40c00c45420341c80a40c4000d180d00030340c4001030b00c0310384400e03e40c001440282c50103d094420b080c03107048c0403916020b00307544805209004030784100c4102415200450701422010341010b0503c000c0f4622040c031468544110f90 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 889061276 1250 889060026 889060049
    0x3080c160c15021506030d03050a02120103061b0c050a12050c1c090b16060b010c060f0212010f080a031805270709081906020705060a0605090a05190b0415 68
    0x51000b010740703400150a885001e10461800700b240650f030201d031441b03808605040c00f0a040c1d0f61241c0c020300921852001c0820503590400100611106900c43d17600f00c1d0001c0c40c2c0342c00d480b000e0603040c0c03104c01d03040f600101a43d10412051000500b82e00310381c00ca4802c1030400034100b406c0c500101c0d081c610b00c81d0070391400450303410840d483c90b0303407048584004001c2e01c01f40600e001d01c00391507507110b08a10000503010a441e8924407180364400c4020040050704000200b00500e138418142c1d010394003e0040c14070a400070b400105d50003c00d003440c1d4040310418001858410381950782a10100d50541c0c0800c0341816002002a881c0c84d10b01800d4020510440d81609000d0a51036100f1400b42c0604048100107540c0b100b8032a41c88000f41001c0d0042c40b84441030388041d40c41c90324401034412544000c10a000741d0b01403000f81c14043c1c001006070f8004880340e994a98030b0851320021641c1c01c9804000c008847c0554217503034022035200700c22590740500f001c12148c1c1410403d8810054641c032002a041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 889062526 1250 889061276 889061309
    0x3070209071701150c1b1517090c0102060a05070e06040603020d1109101101020412051f020a0504050906010915050d060f03030c1b09050f0702100903080c160c 70
    0x2c0002da00e5016001c28000116a42c899510007403000a40c070000074485d030200d036100c40c812a03400844034014402415810711102e00340070001c088419400c04048940410b00129400b01c602091000303120354107900401142e520f64a1420160030013a01c0d10060140d001111039660321000024400340500d52005070b540d0301c40f625650100c076140c1c8451691207c05100000341035468110401010030903262080040710805ca04a0080c4910b902440b00340380044414010400c0128002a024090707a00f054050103401c075102d0142d10948000c00b0009400300001d10152500c0200750b80c110b681803401000107074a8140100c1c03106401d19211010910103e03803118085c41074080c0c1009000080384412041d0715556010304400c659903001843c410032060f00c5011500006620740040c0300d50802030025013040a01c00381c4645082c1c0b0400014055181700c0746101c2d60074090b4442495042c1c0d40d042041e6189040f520142c0c1041680300000c192021690002c02c085484880180451920058040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 889063776 1250 889062526 889062557
    0x60603190e10270201050906070c12030f020f2b1e09050f010908070314160b07030e0f0904060203060d0503040e090601150e040b12240603030705030403060b030307020907 75
    0x503c1c1480e2086414554201d410010703640001951f041c00e009a81e171640320300d114903050003d18030715000010b020755001032203414140d0000f5041100c21070b03a000c4e61403c440700d9034000d40f80c505400c0b940400d5804502c98070007204400190441d204842d107440318880742c004680e140100319040e481c41c00200702d60781c14880342c074007000c0404402c0000d0031700c0c440c2c0324074001c8a5a190040e0741f00152480302000140404d02009005005d2181a15598607140031b45940700420b05400c04042a4001a2604c4404a16003030405e014200781c10300030407000c0c040e50f66a843c40c0107036000501c2e268000c3d00060101c00024010409040038002c03840d00030041d80741c100740803480c0c07100592101c40798058805440b0b0b03415401101008510354184e85c04076024440f907000c2078010488031012005d80c440c0001c04219a00c402c000400d07440d0080184810343d440b031a0402d607486c054a00c020b84039410030882000054407680c442c550300200541030340d0900c2d58130b07000189100811203540e8041004044070300b854 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 889065026 1250 889063776 889063811
    0x5010512010c1b03030b0d0311060a060803070b190e0307060b0904120e010e12010212070f0215100e040302031206040203130b131e030215060603190e10 67
    0xa00020001c00c51107103040d000820b00c0d440041d5140943d42040a40d40501d44607800890440f0800f4005d04498080762400030120108a0702040039801010b0100309008054084c0303004031a0424011414814151600990790b80042e085000820001010b03032005030160080c1100c0c90040400b45440d00c100f03007800c006943c00c003c240c03841003135040c3c100000150340d020003000710480c6103000c41e1104582c6c001640c070600d200020a601225144800c01002c0b01500140580c100100340c0400c0fa0b01d501c681654240c0b100701c0e414001d40c001c015030a8684c551344000d242c0c80340284001c004002c1e0740c1e8007600d40c491029a82600160800108290100813400300540c101c001600c0071803652515081752081003169000c0181400c0c24a030100b288040d409040c01c002a4006004118a8456a2008000550350782044001d8011100c8520303d681ca50301d074503885100e0140c5070038a50350341c03145440307604180303d62215a05035a4540c081c44200c0b0400c0324405140107800c0010b0300d5068210070118 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 889066276 1250 889065026 889065049
    0x3090112050618040c180204150e13020c03130e240a06030207020d15330b1e0406020610080f071e05030109050a0b0c0f031b0903060406050105 63
    0x100030341044207100710354461072414104440c15240605290303c0e2482d00b030a411425034040b83c1c0f0190074a50b480e98503a91540140102d410701481e10032a54030110041d1030340c00d001d142c80d5074005012048082c06980d2600100345100800c8140e0785059040400f1a61250300e075041070340001c0d280c004104104811042c0344c041721b6019100c501e203a180340b000180c11406c50780501020103030081030000441d00c07918012000039038070030b011101c004d210809100062800c80c4501c100740c9a44180c5030922040d40d9001345254900400b009660b03820201d4445d182da0044000c450b001080c2a0610304581d4544060406000907502905090500070f140744441703140b80d0861105900941040d4520a100261071001c0710740e4840107844d6003044a200801c090034030b500c00c030740550828100f20300300300002c2a9078200b648100c07d07061054480d221906054003d001c1c000e440c00d4020400302c0c0c030f8520010700e00d05030f0341d8401141c145002801000300e801c000c02a102160b6854852005000070701c0c14904444 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 889067526 1250 889066276 889066307
    0x1e0d09050f0f0a030c170d0b01023703180e0105010207050f060702130209060d050604110705060f040219120201120b2803020604180f050f04141e030901 67
    0x9403940c0580107982c483e020403000070b082c0094084584100150221020391610340c0c0641d043c1c40d035042d602c414014004080c20240140110442e2900c0401092508000c03285213041d0180660742c1c444041411002d40700056003400113082011840c4889207800e00c0c0644500305500d0752552400001900c1c28000d40c0040388075010b66020424561950070591701c0c842e070126038030a11500c800c8030002c001d200d0240300c6900800001001024407025030489402404240d4003041008001145281503000707501c0028625040724010a4403039900d400d15540040c0000c01151800d203448400c404215610f80c071202e00580d42903a148103560f000010041070b1204641c050184281c4503000070000f4500e80110313010318103240480241c000000c200302c4055540942881d13941c5403503811030341081d6000741005081d9800c1055076058512940100c501803000c2116444080d15107075a20102c0030300ca10313031451040c4141007410801c01c004402c0c0301d00c00c040c40c1001d0340d611030440b800185020316102c0c42d072 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 889068776 1250 889067526 889067533
    0x1317030706050c030c0f031807060f171b250f02010e040903051c0207080408070e0c1c2a090911120105040b0a08030703050301140108060310021e0d09050f 68
    0x1c01c005d0f03075000481e903040300c1803904c0c0b5980e0340d40e20780f041081400a859046061041200110b11160046100da01c54803260b107440c6e00800084051102d191400c8036081214203200400740300540c2840d016088151003007002d43e103156034006030240707041160042034880d00c51844142e410740d40c01c1207800202d0401620207201818060328003034442d01c00c40c0c1040c0c107103031210b0711003400c94051030703041e1000b10341e1003005250b8642e501d081c1d071542d400850188000e14000c2c2000304604090040484807800c0e54248000103480ba100d00e444000d0203c0e5607414981d290080000382e8003105150174035000b00c807d85031110454207004608085440003c010170300010108005030070342c060003015604440084030b005c1400c0d0b4980c0080b60a10302c190340308501600c404070341c1c0c2c4101a0403502030341c10f82c0e1004100246505222004642d43d0405403070454145d00403028088880e84103400815282000701c0d02c0080c418603019540ca21940410076a54032140e0300ca844100700700d420b110b40032150300400000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 889070026 1250 889068776 889068781
    0x60206040b0609060303160b01170a0c180f0504030305040308071805060f0f0406030e2404020f040e0f010207110901180e1218041103100b1317030706050c03 69
    0x80c03075000c01c00908002c0c4070f14055000140380c0d0364200211000d400d503003c0e00f02c04001e401d10f0a031400032800e000301050300403d0b1103049400000026202e010940005580091610704000c40c05100742011841d0728158498200fa10040342a0045a01840c030950380050700d482c05040051200c40064001c4040041100d040145000554000402d0b2002110041e681d004240d000307207810b21491101c1e01c000400410300182c115007680c00110400c100078182d54510540d0031031064408907825030743e001f0845c214007080150070a201e84808101020b030000480c42800407246140a451a000075443c0c0c0d0001444020008030425080000c4030035100d036903140d4180404441061406002c800c0c8559031038500e1f10000208019008507032452403640340e99401d00500c2c03a081031405280c058025820204510405614081100c0c41049900c1032200068208100c040d1194030410f081c2800801050000c2001440004024142c41c02080107580d542c215140001c00da07400282542d0792007100340304 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 889071276 1250 889070026 889070033
    0x2823030901121407020706020c06041a070c050a18060506070c03020907020109230d140a031a090a150e010305192306090c040b0a0302090c04030602070c03020a06020604 74
    0x1a10303a120002d0070400700058002203202c0c01042a6061140a0a1907800b401140c40d008111081a201c1c55400d403800c3ca5880000d0000c648518400d40c000b040004241c40000030000c00076040e0f86200b40074019800f5a04c500160803d038003604084004500b0a03c40402e00110340700b401c005020a0303407140e05140440d2038102c0000950f12000c0e02940e803800004400c10f00c01c4d070207051021380c007596039022190303c805240205044860004224805d240e14001c20900802868100703107080600c182c50407408103021005850710b0040c042c005940100d00d1001a0344521480e88200351170600000c8003002c00300300c68002c2105901885802405000501c08100041450a0703104980c42800b609100303145080c2003040503940301c140072501546200358040001040c42c600440325002181d40c181c500404100807121084a260382c03001128800300018204110b00c9580b0070482e000c01810309070b807511103609076031141c0000c07980c006074401d0038421850844801d6001d41643c0c801400107140599 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 889072526 1250 889071276 889071283
    0xf03020c03250824040c030b070203030f090f0616030608030d05061f0921121e020106050d0b04031103041d0106080106120e0705060a03020706110a02060106030b01022823 75
    0x101c04d61390b551002c40042e040c03080000c2c04200a55100407203c22a103400c600c000e40380d81040c4c400304c0040103e8004900650710000c0d245804200c0321011b404541c0b030704100c02211014040c18030040c503403540300001e20084188090820041d0741000452246004810444008000e5002030008aa41c00c0300040c500e07032249a4102340c655402e08516480c1703103c0c406014200c9800c3c4000c0001443c00504500140c3c00303940092090003203a905020801c0e442c000782e01340c0d440c50090310b800850702d140c0d400101d01180001d80d0400d0003410310202009039050002c2c01c40e032264001c0c2c00141c051341000c0468046100989005060034500b0b400c86505100000b4054000b0702c0312510602d40300c4c281c081440b0310074004600200300040210755104000040034010b90000d030400d8600924140c0407040e0151130300116400c8039940c5c0e020b071455a080c5017098000708800700c2a94118803039400d01901c01510303404070b1032401e1280c1040b424a01d000b03241200c2c191b084103590546031815035a26002d07001001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 889073776 1250 889072526 889072573
    0xe0f01022a030f03150301090c06030c0809030f0a0c020a03020d0503070318120219181505040e062229090109020a0b0c0c0d11100e0303070f03020c032508 68
    0x205088442038400c000007d000d04003901015011103d0100c0006500b9096448003481c0b0065480380b11040e9512050162280540400b44007202c104001c0d0300c48451146070042c010b01d1000b0801d06071249c4030f801044402440c041c00b140d05038400503050041c50f030448080d0201c404040004aa51820003102032813070510904002c1c040c00c0400f400a4460f00c0309442c42020f0140709081c0381c0c1c0d2003200d03100c48000c4c014004e101403c00d014001d020445040501880350701e000618000e1800351500b0200711010102228094a5220350540c204005409044038010705880b11103181000c84241c2081c221820024001103038680c5028445030040c0c40b4280710400311040d400f085521802c0150a2a05180c0c600008944c80760b06880010104a032103914481f8007181a6103252120314125825100c2e801108107441c0d06900c180142c0000a118403a40d625481c0f20f071054841080b1003002085c0b91442ca8243e549114070681d031404035804850500074001c0124000511700240c10507c100c105141c1ca = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 889075026 1250 889073776 889073791
    0x10e0c130302090720010507031512030e1f03090c06020606010c0308070905030604061a1005070807030e040504030806011409130203071b03180f03020f040e0f01022a030f03 76
    0x780000d160207000c0c0703642070b40c5c00d56890a480c61122160840c14001c2600b1100000401d15000086e45015801041441039405d9400a82528a1030380c0702038460481045907668010324120103400103000300e0040782e1213001c140d1004600840f00b40380000c11415160001411540000108a030b0f0303a03030214103000010741504044000b034440074021200d07035104d43c00268141c0f01d41070910007001070540c41050024548030341040744030840c0081140c054500b40481000400620149011404a0b801407204034440e0a00313114441e022008a0169041101c059000c6010350007001741c503580240d958080c030901e48507100e207403401d1200007a40b032040c00062100e210f41e0110008007914003c0103441d143e42c0f1a405202c8415282d842c008144140d06c544d01c481101c0360706800100070350405000c809030303a4010a903d40c590b100800b400010300914041c60075034450a540300b80c4030710082c0b000b4403914520500a6118035030b4200e001048000c051600300301030b4001c0100c200e10129840503039400002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 889076276 1250 889075026 889075039
    0x807030c05100c09080d020c060a1215030f05100204182016030f1d06030a0b0402040821030609040f050f03132d090c0315060503010e0c130302 63
    0x24603003055442c007141645020155440c0c000c103e0881c54020500380215080f00b0200e903072030341445404036242d09071030050310b801c600d080c4142c03800940070710848008000501d03000100d80d00708440c44a401765007507009940d610070034207030030303060107000c0c40034010b09001002d0941c6814602512001c00315070b9030700c081e12116510400a41031300c44603001c860200003134010342511401d900780d82207400703070304c5100c1180855052409290100c0c000c4109401c589040803101811a13144014040300d41c1c0000c1080705065079032a81161541da551000d0000350542000404460850b002d002c1e51080300b08900307415a10701801000050f58854030815480f43c2c0c009101d0481d0100b9190031850941d00b0380043c03010b4000800c84000f41245a4200811201001c0621590391222034000c651409001188191604440700a11444003550820300c1c0d00c007014600018104200320407051081c0b200d40021000800000040040103044100c240d04032140760201e9180000740c4a0040421141d840024000e58 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 889077526 1250 889076276 889076297
    0x19111f0c031b0912050f07030503030f13030801030321061401110325050319050918040b0708100308040e010e0c1801080601031b0206040c0609030b0a09110d060506090a09080703 78
    0x1b070010f80c6000e10b161044421346c64485c9005500c9400c102c2d82280d6aa80940020f4403545c102c5110006658140c1c490380d5a0742d007035880454030f81c9000c0b84400e4030240380c02002d010800f028030a000081034080107213021904400001840010001180e401c50b40c4280700c040c00004060400c8404681c050a00d2540d41c9843c0c50f006043d800781d11144404c5000c03e83c082d60351182c02c4002483c80c5c000031524004a80780719001c0c2908941c043d18041e03d0107268000241e8070360700401840d50030824910b1a1030740340d543c03666240300c140d000f0340082ea01c1444400040201218800c02c0356001103044d0340c203d0424011030a002c00c1503407800240c1d0304100144001c14026400307544001c0074480350700801d0008000c5600082d6503000d040d10704950069440d00300007080d82c41240241d0503294050020b45150320384440050140c11820f4003a03d81310f000f020300c0311071a0f848001d2250540e1003078601145a103450010000c43c04030080c0320396242800c012071000040c220404030b402036a4903080c01c5040c0c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 889078776 1250 889077526 889077533
    0x360b0a0b0c0c0a0b04031a0717060102070b0a030e06091c03150f081b0306130f020609030a050706020105090c0607060c030b09011d0c19111f0c031b0912 67
    0x41040081e0b0f00100c20f448041100da030b02e07000500680e401080300d0514812002c0720456941c004a0f80c2d00300084c5220803002c02c20030440d402c203401c0041441101e580c0354440381a519203a0211440744080782d901c85041d07a00c1174041c00019448038a0740c000d0035511640103980c4003511050000314003059900c2141030070a85903d09007601401803030009440813610f030000d2503502c00002100d0098250000b054881c1481c000480781c1c40780401d15074030300c03440316955210300d80e6a0702070b03808aa0100c42442003000c0d940303007040904480c40c0920300410142d4507040e03000e421600041c0101c01c0b20340007040400d070561280c40440d91a140d0244000484040071003081300240406641c00c0c1d4403140c0a000003505030215455800c0f01c0118240021094070344102509852140a5806a01911107441000a580100b58002c051740e010301c21343d008005148452000307042ca01c101d00c0b244a90f201071403503060b0ba01d4403a006000484131440500703000c04038405402d090b00d45c403c45010703180d46103078007040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 889080026 1250 889078776 889078783
    0x16122103020d36030e06070503070206190908030702010f0807032003090114010e0105042703021c030e06010e070207090e210a12020f04360b0a0b0c 65
    0x140c029400302000f100c100b1a006003201491400328080d090910403e03104080302900307a90402d180e00d03440341a66031403e40180030440d0400001914075020034440348015840b80401828000d406014655050801c0a00502824095044419640d0007407282200507600518600c202c21894180748010b5a82c645d0118040c00554400d0302807298040d0203243c2d010003442c0514041c0803020000d004120021808114940d024031500c01d884001da0010000c50400360f01210103080c60796a10b43e21801141c3c0340744000e16402c0411001a0b000d070380903d040300c1d1904211a1940c209140501000803142c0b0002d03614601809048120101000441c44c46802045440010815888244800035031354000e9030b103038100e804154150003000d105400c0d948640c48105c4d00500314035101c075000c1e20903a02009001390400e502844104200300700109511f400400503628803862400d1784113030f2560304c140c0c0c41000401d05002c4244d141c01c10008403010760707580b290542554185845141c449034100c40580c42d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 889081276 1250 889080026 889080037
    0x1050a080712060906060b0c0f1c0e04050705070206030903030103020913080702090c13080717151605130b0703030b2b0f06050705070311070303081914091612210302 73
    0x21804000230300150311318000b040100040c000710081e01d4084a10700c449100c8000710329105000501a120441d03800d26042d80026003195140c034020741041050340c003107a19540151045a4150300100042027140f50035a4819401144403021401c10004e030340c0c40051a0041c01002881807a83c01d001030701101050080d00e1701103000b481c0d0f500d404d0342e644441e42c3d12103a490142210381c001c080a0084889000180a91040542000c800140d40c41c001142c00410140000c2010403030104505401440e040300750901804907006000c0d42c038585d916002d400c94809048442c029001658290f840481e407484000c03040707890741900f030b148200038079203480c02851040c0018082032500052040351903010016154544c07103501c410035000d807025401076a0300300e03511008000440c0c0d54001880c4603840001c24400b00c0c0c000d080481c0110340300400401c3c03004111001c2c401e0358004414404040c030900c202c00000c1903021100400302c1425268100c80e4450300252410310822010725100f6a4820341c1105c1e03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 889082526 1250 889081276 889081289
    0x6040c0c291003021e0901031205041806060e010315050f0d05030c0705030708060405030a030c02030d0e01020921030f03132a140a0302041e0f0501050a08071206090606 74
    0x1605072904160103080c0b068503020a9020b4540c0340c05680b02d29000d640c1c00200204000c1015480b6032079559079159180f900e1040304200482071000044210341c04009902e03116416001107001400c00d000209284140c80d940b6040500b00352411510441070b007020810b840e81036600e6150324011501040c01c94980ca00020000d100010b40c0107223440c004100b40c002e49104800390340c503141c1e0b100519a940d0000399070280a50f0820003418004030b001e03071302c0044544401c1c01600d007422400040401107034107031480c0191070394001401e00d85619055640c0d01030011280d40c042c0300c428400703041658a01038844116000c3c88008082544100414603003500c80da0701c08801d0200c05c0311005400c00d9201940c100b160614035002010903001c12b124a40c1c0844a80039142c001f5051035a006c000151480c180c04031b40141d0b00c1b05050342c07824034078000d00e0700d5048040300114455151174140b02c0880060b0348030044a4106400900442e0314420018201035040940030500e8411400c6c00c800038401c5074480c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 889083776 1250 889082526 889082603
    0xe0c090a0515040f03141903020c04090c050301020d05010513020f16140607030e010f060305061302041b051305040509033103030206180f100e030c07060c0b06040c0c 73
    0x4000b00c446c2004d22000c02e00080c1e0711007100081200e40c4109030505c0080241e048011800302c141400d622035503100f400b513240043d07641c0d61500800c1c2241d200e006640d16030341e01c0308010701c514181a640e441d61085407410840c901840d0b82c40e03900705401220f0314100c00340f9000100200388007a0940c03041c100307a44401070ba0410300309484081d000740301400b4800e04550a100d13440c003418400d031155508a90300080500540d40d40c01c080c030881c1c00141d1808991080d03640084540e007501008016a80e0301560315910303601d402d03441010b640b000c01c0380c3c0050f216608040800c4020800402076038840c0d942c1c2c0c007640c00e011104215020f562502c1c0e40750132040d20798400c0000103165000418500a8004030002240742d42814811500c0360001a1090300c240e0102a1104541416030b0040d040c3c00c0d0408162810300c05005040c9082180a44c8003070002900f41001005000701c07100900e1304104111010010711100721000381040b07509500290001c5152842416109034440c4003548200100c887c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 889085026 1250 889083776 889083779
    0xe19170309060a1710050a060309240608152a0708030a050640291003180305070516030311151e090703080703090e0c090a0515040f 58
    0x20182d9004d540031800340c16400000c07420709104004100141c0700060b205d0805141449415009450000c41c200e41104003041c56503810740704601035045490b00d801000c0741e21480d06030b0329480c0c61401030603859070310000f40c1404016422001070a400851040d01110440c0008401121500030040c001c1d0010600100700070840e0b03c05d81c0b045108407400c0702c08551600385081c0b0701c40b003100601040510900080d02410100b10811807142030200070300000b1803d80c05a61800c001ca401503c2c40c7c4da90f54540d942e002c070592501034559070b40011285000c0118010720f08040d481c600404e000a010310000054400500405016140588840c54644150241d803840d00406c01000003181410702d00070008101031250b60525094003601e0303540489030a05d41c20700040c1d8103a07a00039001420314440c0700e01c0003000801e0540503009a82c020b0319181d0740c040ca0506005040d25004000803141d0b54100600891940c0c1c401c80b010035604195042100c2004003211401d00c5d11958110300001c0214580 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 889086276 1250 889085026 889085047
    0x261602030c0102180405010b1c05060a03020d05011d030313080714011506021c0203181f030b03010f0b090a0e070b070c05102303060a03020915010e1917030906 70
    0x307840003105085e24104031a82e80c0d9112507042e4001c030070361111031150080b481c400006032600b1494222800a04944007140e42e40d0004007a020088400c54080e51102c1c281da00102401c45484908452003000c0e40ca145410808e106c0b0203c04001c001f48410004030f41c0308180034940085007000301401000f0411281003c84409600030030b8428480184218a103440f0401c02c00d0f0100c220707a407401d800940c2440100080a207544610179a100e401050180c81c007070f0f0800100482e0380703e41c0c50302d440002d0420500f40c103160035180c041400110142c1020503901441d240e0300d42c05580310b185d0400c005514842d0081e0307607040a016500642880001041d107000388018050010200e13131048405200f00300d041d18060750f0030507000042c50044500360092103c0035000800555104800604a07a00c4c151070b60b00041c4005015111200d043c1020a182d95503035801c0382d401d440800080b15030001001e0f510f5410210015680503403180360030200000c0ca00d8110810a580308620020251174403541c2072038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 889087526 1250 889086276 889086307
    0x30a030c1524060f020304060302091203030c1c0c1e03090b091501090e12070302011b09050315010806070e0117070c1b0810090201050d061401261602030c0102 70
    0x1500250110001e00c800143d15014820a9880790020740213075080a02d090b03000d400a4000c94003003500040350003110300c4048030034030095100c0e140e0f4180c1c85032240d420035a46607840c880d00c4100c0d14800c3c40c00d403a1070702da1031700000010501c214020740c41041c0385095104034040d0500d088020500308148051004010300410100c501101c00889428240e80c1e80c41268103440e4440845200c03508460b064480c0403440c41c00910089029000100340004000c0007108000f9103030020a000480208050045290a1000400b02000024080b10b1075040c0340003180c54174405428132086c4600c000c6000c030b00c3d900070380002c032068880038511490351074076220141802441e44c0040310b0741203042d801120710501c001201c9080d030f400d45005150300281152884000c010441007607040c84024028284448000d0240c240580508440c00743c01c8100743c0000b500b19500c01c0d1005035010001c0c801420100c0c045440d290744620340c007038141c030807483c803200503425807046108440d029400000c5a801d00d00d00e88 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 889088776 1250 889087526 889087571
    0xc180602060117011a0906060f040f050f010e0f011218060207050c010f0e130e01090614090309012705061602091b1207021608010609110405030a030c15 67
    0x1d22400420f0310030101c03503038222150344244803e03155503202456000e041191030264030a901401e903624029900380903a016400c03070340c40450740380e01c018010301160901007098035880d1400c0c241401c2c0711135503030300040103e200072511504119030280b00091501498200e090711500807401541045000d0400001035880b211054995111f02d0031400781a512a01d400d6030844803a0755040d60014004041108940d804800d41881d142c650a603208407203420303c2401d241c1d6200d040002002d4a04c852504c0303030b0600041c00c00382141c0091050400a07604801400c0d07122415034808001d40d403510000c0312504882c0d410983c0c0003900420203907080100c8440701541e8a00031122041301c2c0d540c0010713007010b0381d0301d5100e0b00080344000d01125158a21001c1803a80185041c0113803010b034901204402e00c840d84586c01113030a41c1d1180340030851400c1d984039000811203801c24076840c2504010201e60f40710041d9400804206a05203041c0030710490710707040300c4650b0701c100c02132010240c0a0350202d06000d01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 889090026 1250 889088776 889088789
    0x110102071d191518060e0c300906040c08010c0f0c0206130e0f060f1c05070312091a03130209150415060f0c120e030307020405010305010204060f0e01050d0c1806020601 74
    0x1048400710380c141140c030145103c0d41021f00741d14a410341c1200c44540407080134500440ba18800e40304024011441200103215a40c244014512071616040085a0301a00e510030010750b454031000e001032540c003031203044114505003401d1419280300d201040091080001d00504507801c80000324000c01c403012220701801a040c03880186807228810013080c0b5510300442c99100c1411071b180d4601424000b202401207006001340c69600d40e50340c480c400074003420408000012841d4406006411480b00e05c40c440307001c03c09000c0e04514127101654034810b100100a0305c101d0706880050f800040c003503400e43c20b60002078800c0c0603020350700100c0041098580501c501090516030301e8400c46110b000301110068000d100400d58920b00e2801707a0300280c14518050705030108110810158542d400768600a40c880c1000590343e502e4410020140380d0385c001d0030410021a0140010640e9201058403080300e4044030002d000181d420040d03410701ca2210320703519121589440040e08507000310340d00d4101c814 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 889091276 1250 889090026 889090031
    0x3040201020d09050a05010e18090d0207080f0604080f0d090318050913080d0603060510051008070504030b06010c05010e010b040f020c030f07031b110102071d191518 73
    0x1d60740540f010080c83c040d0796040a100300c0108025846041458820340700500305183c10050380d155440207907012100741348240c1c44002ea80d03841d02da0400401004202d2500030342440007105032801e448203405800a070110001054507100c1212394011284e00340c800202c200800303121860041d00e480c0708000c1e040101001c00305c0000341c90030500c50702c0340704002e91240300007a24015510500c05410203010b424103d41c0d602404000101700c0d03c138a9020750041408008590702d020204030f42061558040c5003003140e541c084c0403370690484280c03825a83c2c4040d0542032580c0e02c02c0100e0b078000f1601000b9009600f07110b20100c41030410b41c005180e000040d2010f001d01d402c6101c4660a80c8109035601e00564030802000c25540d81c001c001d055000c0c46880e04043c8103803544240398a4100421081c3d8012240f0107101c030540d030701044107a00030081880ca0400040f041c40549482d034030010b103044083c2000100c41400c010895104d4200d0025201d903107102607454141c9444445128080c0c14003851 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 889092526 1250 889091276 889091293
    0x30a1a1e0a0f0b0d1104120b01090b0301090302150702010b100c050d0201020c0a021509060415170708063f0c0d0b04120903060204142701060c15110304020102 70
    0x10541c2c40e818142e81e81286120f02d00400b0000d46402044d40341e1654900403c00c1c03002050800340f01c0e514955082c0109104095035041403180021501510365442c03090385400d4480d000242c022464101001070420884265038800704140e015111486545901519000707003500c40940040d10859007130300942c210340c2ca0080814050b07080384513140481c28150300141d070710001840c18071290b42c8800d01104d04141841b10b00d60104a045d013094120b00d00303501c600d1110b44181da5000380310044a507802c850340c4100307081caa040034080b400c003c1e0a50f401000803a24004061241c0345e40100000d040c0f603500b1000e5405400f140d80e0940307108554848074015400702c0f4800e407a03c030380402c0c00e107174014444403110f445985e40c0400030341c0c00d504843c0501903c0c05000021610704d00c094001090041504007c861202c01040591807500c0c2103403481d00c20514540c9980315840e51102d040d05c41505009110200c0c90070310b0324640f4100c50b200309400d800c0558200315569170102442c0968801e808072035212 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 889093776 1250 889092526 889092539
    0x1502041805070c15020703030f0c020319090302090a0908160c05030f0609060a05100f080109061d07350d0801050d03081308071b060e0a0b030a1a1e0a 66
    0x18900f80016051100744400081c94058030350050010350300c80d040009000c0030800500050704c025401880150f00081107100503007603807548038480401e0318903162418904550000310501401707000c910f4015924010071080140c0841122900303180d0750b0082200140525058501c8110740c0605070007030103007094803281c0d400c2c00038103940101024030140519a0b41c43c6c12001c001c202c010082c152040102e4000180c0880102400001d441c0c12800801c4541040c14100c0655600d50784030000d0f0541840003200c0b0b0030012559005440380408000e01001d40d034101e46507442480309001e01101000d8118914030302e00001c0c0c881140c0910303112507009a0b603c0003000041d210400c00940421104400124891b101c42460050039108190490511189403203045002e10300c0c0240d81c034281c540c00c00912009400c6401c41020820454000080a0500e50040001c1c0000342c080080d15071100c0e50f2018000031100e0742e220903500a000e4080d0085044103e50060035000c1500340126206580030a01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 889095026 1250 889093776 889093787
    0xe0102040605030c0307021608030408010b0f1804020301020d1409010606030c0221070f0b0f01050a0605041202060922180b04020904060609020d06050307120f0807150204180507 78
    0x8644140c0c0b141411550307a030001c500c0d2a4002040d02d8118051403c0e945001145403c200000d072401000940d00ea50615038800d08544040380c01903c24502994034801a40c2d460034a241c145904265158103070b00c4510100e40680a0034080f00c100310301705142440100d6904c0d07101841100c0082c0248180c80d904c03c010350407030f61071007101d0340141c10090031341030031503903a41d20356581406480c42207180c0034494075541400380c094801141c160205c80c1c1481002009140c01c503001d043c0c102c1d400030b00e40740303840c801800501c141c2c8242c1105084002e00c0d20190747e40d18042e0b03000e804000d0b00c40d22010420118200c0d40c80b403020500d0040500e000c40044000d90113022030b4118981c02104c0b0385032519650200940e00400900840d602c503110940480c0140242c009494441403009021075040d00700360030182049282d030001004109030f0208030021981c52200c2080254101308030070741e180428102a0801d04215000700b28403400098002805008441d244404086008080180380c4030090304564 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 889096276 1250 889095026 889095029
    0x2010f140421050c030a0e120606061c0e030c0c03120903150421111509100c140301080a0c150e040b0d050105041a0c2b091a04060e010204 61
    0x20404241c9074a01e0070301c1c40380302c04144220007800c0c201c1c102080007a000d899a0310108140c400a8500c400100050400c0f2a80c0d501416890001c0d1030340b850030300081070f8103008035000c0e01301020b65102c10610300321155100c0790b114440002565616203146159aa0317400c22000701d107000744544140c000700900b019054400c045c00040c05001350313200c485a00c0415150140040c2d0b852440100000e2090f4a400110151611140c40d031122050054010703509042c418142130356a040400100060902c012130014001003041c8000106000114002c0321107680345400d07500a500c00100201e1000c80000707941683c070b0301c1801d10500550f02c0302c0b40081c10740c6040000d00041180e0b401000c2d458030f05034000700120840501201104089600e5081c2901c00a407826103a100d1040701c40d42521452013205540410341d492054a00b40074005070600e204112001181c82d0344240843c420600c08a80091001c1a0050304256078205d4600198104581c113580440f569490440050420041802a00c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 889097526 1250 889096276 889096283
    0x620040b0a180e1e060103140f150d14010c030b0609101103120a3b03040e0a1a1207030204110405060301120b0708040213090c090c02010f1404 63
    0x1070400165000544145441c0e0080c001e08081d0b04001180e09003000c0d0005104160b0035582c0315400d491034001e100e4442c4081c0c040d038101401c0c0143c403d5005072003440d4a8010401007058003d40c0d440852a4240440c0d0150f02e0303610081080800301404011400211854034002c0200084c440b101c405034125641280e20940014040c48100c43ca49041c800741c8642c000641009040400594070603410355004285c1e01d40f070700001c0000d020410441d0310541140003541c600e8007100c2d2110f000d00c20b00340358004128600c12480401b500d44844030510640e001049100c41801c1030342040420800940b5850510b1241d420740b5200d20041441c00e8050254142c52010140c0305881c25502030101408031a034041c2103d0500300300000d01a2076140046000700012000812130a066140443c40b40320081d08000801c1000f42c188000750341c0709440b030f02010114a40c0003c130310006142c41030040310a680f02041441c6860589505c3c69019040000f89841007402085900c5034010f10719050365050790042e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 889098776 1250 889097526 889097549
    0x5120307020609070f030605070c0606060f18261c030509061e18120d02040f081204060302160b01060e01121401050d050a06050a0f0b041a01051b0604062004 69
    0x3c20100e0a81d902c2300c0c2d007100044c81d00300c00c46107450b1036080503103034558003000000d054000310081155004103002803042c100300d0300c0c0d1242c0e490101d420b103020021500d244200f030aa030303442c0c01c95200d007041910341c9015983c141e00c03d01d240200000c0d00038a0110f88441c540d00904002403036151101c010811120303c40d05120140d600d0b15101c0c526400c10741c100261580c0300b42e4031540000c1d00100041d101440340d440f00941e54506084a0000e210000c0d0b01c40c290307a80c001101c5d001000c500000341ca050340d01c545801a20360b40701c3c8039904d100c1845001c01400b035082040010030704961001c0034540180c803e8071268501c0046103e401c0c201c820402045031403406460050001e482e0000440d00c01038021310823100c00c2e00503903c0b07800885900b90f50040101d5910090500024100e0003005100c8100711010441504250600c807070b400d80c2c5600c1c00781040745c00101c3e042d00c001009200b03842c903150842160020300d428500140140000840450032103580c4c0204040181c007401141c055407003003400d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 889100026 1250 889098776 889098779
    0x30307020d060509120d0b01020c0604030b130f0b0a0c0e030c090103080307020111030906151008070c26071b050310020706020d050c1801091208090d05120307020609070f 75
    0x10880100f81c0644454914015400030010010658000c0c0036002aa024000b80310740300c0e5000603103032103004100385010f004140030070004603400300d40326a400082c0311035650000da103030710705150118001c40005040c11900300c140007048016a00143d2021416107541480c0c3d101c0b002056a030f1003200d2340440e0b1040544c2c3c018000140144051a0000100d00002c20010071420329a58140c104403026030039a4003a03420080c80306c20780901e620268000351201070109810900017000740000800910520010615210400c405003500c00461504210040c00d02d003c90104500280e000749815510341330425000c1050200d8550208100d940050040100c0b40301c00c005140a50480c0c603041c1d0340b2550900403e440240e881c0189881003220300c0b48a91b0369882c3d801d60310007081c00c0300f41540c100840b86009000d604500000c0001d41604090156240c603880390006410318222400207040d4000c03400210b0110750f411020314002c1215030250b030950b50b0f800718840c0e6110300d14821100032616800c0c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 889101276 1250 889100026 889100033
    0x6161407060b04090b04050d08160905120c0a1203030e0c030303061302070b010308040305160e0a090c08011814011109010804020d0c0e0712060f05010513090e0105040b0105030307020d 81
    0x21a06100d02c0251011401540b40e0b1070300701e043c001c100c5060343d03190070101200f405c035644a40f981d98460f00c030300407200256030100701c0203003241c2c000d000300b41c000c19080c66506045401000fa01040342c034002d20b10540d85031075100900914605420441c00700c2c0c10005a02c090720710210f0039501801001e401142940c0d40d81c003c0011242e43d0f006500802982084404081201596410301030340c09090030f50b40d2641f0b0b500c1c00501d08074484407103d4280c000032030240b114000b4400440d400a00420f4081484c0e02d681c10400c0200c901d60340008030030740c82c0800030400480c503055206030b45ca02500f42c1074000d5200b00300c0182603501104c400071b902401040340911b0366000380099074000d4005001e0f0000540e00c5d5603118082001ca80001110700642401c100185922266110898228040c28800b0070f2800c00a060400f130076009150600c44081845501410b02d410708100412350b072141445550040b1182900800054a040c1c1c1c0c156507100010950b428004100e408265000c0d043c1d4145104548 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 889102526 1250 889101276 889101281
    0xf0105071a04150f090b372405010921061805010e01050901150303081b130b0a0f050a1e0516050c0906010c0b16021204080616140706 59
    0x42c01290481106030344508481018070404425070781400380050380f0220b50604103c42400102801c10041640030b130350340e4484900d241d000c5042000b40300303903108a050141c0c000103480c05440b1141c070080510081d146000600c08102c0456200381c0f541c40303115403984c00c1e22246240000c2c502400d84404445d0400148055220215030010350504411020083c1c0d102400e44028400841c45a0b4543d002d01000010a1083c8000c0181d1084082441495540c001e410381c0c07030040914580a21040c1c070b58404800100850380b031010f07204201004c0b1074482280d0105038000070306841c0002e80c8550f554070f68902480480f00442450f03140c144007151072002c06c5140e4985443c41d2001c00c44140102c501d0340e070003c1c00c01c003692803048015000c0f80000100707000080000502450402c8103184c4840c01107140003001640054003020680d80e0740b18405003d030b01e0705100e00c85444c0c07a04e80005001940310408108103010707965020310420070840d020800c481041a066141480720010041040000c0e06503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 889103776 1250 889102526 889102531
    0x90d06140a1b121d060f1005030d0e12060403050c0106060201060b030a1e0c091404020f0f250b040302060601020a080421170306130e0d0c110312090f0105071a 70
    0x804076084070004031320115142e1021526070341c1c0c1d110350240111407154101c1690305c0220340d501602840e20f0300002076502c022030b003070150034020885c40001030350329599070580002c410750003141c9442c1081e00d001040c9038001680450b0a51030180089025481030040b2422905082c0c0250b0031034681ca660710703004100740c201041003140b010440d150385d15168003840c1c06140c5a521144910b0b4030b03040c94100000c505001c0303a071049204200c0000311903480300984140142c0050f2054450310100c00174000c20701c001f03004e50100c0054174452020031414a80052050b446a42551220f45030325005907503a4041c0c401c02000300702d05101c2404071a12186c3c6e901002528421030512001071904c43c0e042c3c07400600407007a4003103000020440e09044c00c0d2118441404100003c101800c80d9243c810b8545407030b5040032081204c800614014424102c004642415004095500a0702074051003440d561202c64200c0c0140102c04c040800c641c0507100380d5451542042400a0355150b1444594095400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 889105026 1250 889103776 889103807
    0x4050c0f041509060510180b0318030705060a0608340506040902300402130b040203130c060f021c3501050409020d110105090d06140a1b 60
    0x2244010720001d82c14a50b003000621488000103096800e1034240300c00403945c55009014001c001c58030254840101c01c40c0c0007210701c0d200c0e180b926902d42410020000020314003500703031844042042c00a100021614030301030441410200911552110096100d100e041d02203e4010440c03860401d1600580040d01c01c0c00324400207060310541c81c0c000045098015400c0060200c0e4085004c0940e5081600c4005486507480d013031090034110b441003a10b2151008200a0080d60420070302c0c0c08082d016008111f1741840140299102e103071602180400403924041662404070b04c3c2d500098130b5014074031f182400038003980540400000c09090315400b4070020fa991007040301148081e540d40240300b160b0402a01888240c0100d4508192b8040c0d0002c01a002244110718085020006030344404e403007280c9690010f03e1102030707498400107075030310300900a0781c070340102503803d42c070b010000603611100345561000c05584c06601c5a0001000311800b0508038a2035410390b03140100402d01540f4448140900c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 889106276 1250 889105026 889105031
    0x6021213050d27030c033c030e15091318060203100305031201090c051c0b0a030c08100e0d05030402011d0a09020c1b01020303010b222c04050c0f04 65
    0x3400e440e481e80003000c5074130545403800c10780014001c0000c8003e040344003104410960802038014881600d119411510f0b0b441c1900c0c0c1c80b080c0d1420103008181c84030b04d04100400d00c24142030214410002680318101d102e2103101c0320001c00540114a202e829120f800f1404501011012070303903400d0082d032002d8807022100140300000000504200001d040c00401d0b000c9072400340d4502039803d001e581d440b00200003444010321102111a8540c80100c1040450010100d501c0d203e040204000001941000c2d00e000b104020201e034403640021028a16440004100b0090142c80b050507254a405940035000130b10400104e8050341c0300726900f1559540c1254001e0318121440700050402d40d96034420710040750041000c140da26003e11003180719401185100348c500c0b0031100000d480f0711050080103d09000031a5214159001a00900c0d80842c0e114425410030b450b41040c00345410102c1860f0005c0480d415503034140100740d14080d0080342d211005044410840c010400c07103c0c03445106c1d6800c2036 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 889107526 1250 889106276 889106327
    0x1050d090f111f2f0609011505040207150c020f0307120912051f02040b040815181c0311030a0e0d031112100e0406021213050d 56
    0x641940c45004076900c40c2c521401c18281c03040520001c03c00c2e6106041400ca1070000580a080d0040c144240d5104016040c4106100785042800801c0c01d070041011075100b18400c01c55800815408440070070701440c100c0040301d5544003040240d01c0340d10001003034507501c406084001c283c43d400c0f01409001c0c0b0300540b0b2112000d90016440c2d41c005850542d03014004400310f603e130940210081000d0308110030010384c044802e840e8183c0d580000e0504150700f0754601c1c62061a82d055034185c40150085101c6550740351754600d405a90344805280074568407044002190200000c0060320044001c020040c081c1079a61070103030301d0001d100310110014103407030342c51a04108002500851040441410010380755030010303c503501d00740102e50000700785494000d000d411041e55001361140e1220010340980c86903a116010f80100c12560300428a968401c0240010000b81e5005068100900d10690f412640d5003000607841c2c1601120252058000008911142e84500b04200380b44403021960b082d0007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 889108776 1250 889107526 889107533
    0x102070504020a021f2301080a0b060f1009031505060d060e03130b0307140c0a020d0f02030303180d03060311060d060f0f03030e030309100c060608030a1d09090c01050d09 75
    0x407180ba1700c0c003606a514403040560044048580207610f003400031a0500f50705000043e640d80d024204040d216842c0c440015800d030752282004c081580010307003d20204c001d841c034080c00c211490700044800301c000814050805110f80b04071442800700818404981050352031711002842813540511706d80c0010461a210a07036500ba58400811241c280c00365a0301d84110000c0076890052042203049804029000041500045a1012a4044034100c40020552400d001d440c020704d05c00a4050001000b0450b507500490341c8415076002d11019a951660303504000c60403180320f070100403d020311010080d00c1c1801d0980c0908002c00050000088194450701000c034070030500c2c0d00440d42070195280c188100b5902403000e405c40803050340118106251a00003a8940300c10201d03550411450785030500c2480200c5d0400801000c03140140c941d82d80c003010303000b070440386456540d00000351070040805d86810500400c2d03105004803c0500341e0406444c0c01140c26030701c092880031401e0f48441014010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 889110026 1250 889108776 889108813
    0x40308040303140c0901080f010b041707081006061412180a05100c020c04150306050702030f0c240f01092f040306140c030103020f130e07051306050102070504020a02 73
    0x62002d41c001103844107036080005041000c01011800030440c231100410102107c5c90550341503030f82607846800c0c182c6600804514003402e039409420a1310440705490201d86183d07000405486041e40c1e9141d04a11441180141d885549030280700d00c3d40c8280000e00241c0c0426103031040e50161800d4038a40314107a01d6292410201d04030ba030078003070751f100f202c2a00079804210b400d6017400162010701c080050a070642c4032150b00c901c80584503d89442c001000144248216003980d840009003d4846120842043e03942b041c240700740381e070041d0710117003005600c2c0e000008500c1180c1c7c040300d042c4107a08241c800c4010348078141c42c204060408002c2c090081c03903441503d600031264903041c81d445910390308000064810300211101003015140500200083d503004881c1940d405031030f190001401100441d41001a107014049460f140940b41d030f1280c0c1e400308801046800885607941200e1203e1090000c4035a14801c1c00d001d030f842003800304000c2c2019006009503245d2401660086426031240586 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 889111276 1250 889110026 889110031
    0x60c070618050714041a0d050114090c010e0402120604090309260601050409050613020609040504060b040c05032e0812040807151407170406031a09070804030804030314 74
    0x20b068010070018480b0520007404240881800c507410b020700000e405142400c0c0c5180448180038403010112141444000d4103d030001641c0061124154600140d01a440d99820a9500c2c0091200c901e0701411303190074021341301044001c4652008540702c42080000800305d070081101032000c5500000b0f1910040c005045090300702800460b84030103140308540c10003070160010792081c2d01c3e10303001802040000901c3e55000b54160781a52662000d0300000b0080d0107004c01c05540a814941080204520307a040a13416402c103440030f0111201d050801e88640c001103480e00c030070b032000070f240c81c54491180040b0170302c01403a9020b604e5080d44518000d0309114520790038045140d4006410005400100302590042481b02054031013030318251001001d002130359551030216100030655005205002904800041082110f01d03521641e4032070280107070030b100f403894041c144011118000c0c3e0910040180c0700e1200ca0341c441c9500e0f41e565806444400000d0002c1d8105690b8010040740b00889010307950 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 889112526 1250 889111276 889111283
    0x504020f040203090a050f0a08192109050c151e0c16030b10030809010509010215010f05040e1908071a01120c06050a0e22060b040305010b030d02060c070618 69
    0x104181c40350400b14071f05400500c6000c8558081918a40070400c0f000c190760210000300c0503564410030b41d5408403407846440740712220401c24a1402045031f0690780c00301e01024031400540304508020380820020303410210b1a4014070340c0c10807d4441c007180c00c0b0002d0b07182c02c3c00310074840c4c1441100c1401c0d902d440e040414446c0300140c4244280280060007002c02d5200c110702480c00100d032b0840c0d54041d600e000c1e0030300d414180000861a41c8050b0b00901140066548003055900251707940c22205513201d80300c2c403a00703005510303112281d4070250001c00d800020562044a0018490141d550785240798801e000588041401da41d402500c40c0f6502100d03402000c1e00399801d0f0350000281042600500700d94009400d00c402007121020050b04114203c18450045480c0c0d449107210302c106008680c3c498003803100180c9440404104180e205e030280041d2806500200b00c400d09000900d9514444046a180564491400900406003420062003107921a01d00070941c2090f04415001e031466500088 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 889113776 1250 889112526 889112533
    0xa080d091403070302151005220f06060c080a0302090a06090305120306010f0e1516050106090204051c020609100302120702120a0c050c0306040f1e0b0105040504020f04020309 77
    0x1810301c81031084080078420000701440c0740c0000c60343e004c1e548241250405041708881d00010300c02c0c04690020350b004102c00751101317410401884600300804100b0307034820003543c0741c088419a41a83d81c4191416203101d610f0310364070001c031900c1e800256000480b2041c2056002c01000e01103450b4040e40c800200107a0708d820303080170308519200f404c0c030240070343c41c3c60b0440f000c1c410400345a90120b00601115014100541ca94400d48042200040c90300868101c0801c001442c030001c18054000a400e0b9000782d0003080410f407a0051003060380300302d00c45d942d4007601840040104003100d001d0700441520091140d4900200840883c008000a400300d0b000700740d000c192602050310850606501c41e0661019002420080c00500098000c1091030010420030600520400604105003e000c0c64020308231031161801d40b9100301040204001120700c1c88103c1c68416240f04415001591190f021801010503824031051000400000304282d80c0089840031544c1103481c5e0344000d50080c000790014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 889115026 1250 889113776 889113791
    0x21303050a1407060509090604020a0c0501060f0e0c0403030e22140105010e0a050109090207030e0316170309010c170d1a0f060f0a08100e0108031903200c0a080d 71
    0x302c60410107150700010520504000d4105a50380e251107146c2d000c0011070b001600c403025480c0803600441e100d0700003055036103440e002280305001e141c2c5042c11910300b0380c0200a00c0d568408002c0d035a0003940700007004908483c0003e5643e15080030200b414015920a030310047c1c140c9101c0100741c0720f030a00071b010700164600c014403855034000300590114200340c030050541480d02000928011241c0706d0f00c510160301041890406220b42400180d01c01e00034100c5112410780d105060342e08500d48a18108510070400c40c152803600881903826901050712024544141600c0f809104403d500c6c81c17402d00700e400c20110003109503d100e940300300d485032204002081c0d82d400511100000e1070300e0b49031183c54241f00c0e200b911114107048a00000c01c51414981a44400110000200440d040000c190841c14000f18841000001401c02c42c5101c1c54002449110800150121610003000e800c010740f0006800600a203070300000c0104448080c1101d207099065214120107030484144d1031001c0d611041c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 889116276 1250 889115026 889115063
    0x50d08120c073c0c1a04030f14010b0d05070302060319020d2408030d020d060b221203020607031e0e070513021314010c0b070f030627021303050a 64
    0x42d6035003d40315040343c00d229250961540d01c03518003284604c0000700540205404d00d204000e00390340081d41d20810802d0581034030301d0301d503084a4111038a89a15864030380000c0c00c07450001084042d903500a009006014299000c0c0002a0300090034410340411015901e03440c401644001c00c00b4440320200002c280008881e0040582c002803200e10314501c10400503c1510030105c00c44545009880d401a90341c001d010342000500700c2039014080002010482540314220058440c101006040014184945a003001c4101d110450000742c01a41b0000025840754060f90180904050f06a0005900c0010145040035100c3e21403514070700f038120040801072401e010740a070140d803040c1401503050018005c007006451046100300c00315100728140101c16030b4090000c022010b078100c502c41000703152513a03000c2c0c0000713803032015600003915016002031840c001c240307000100c0c501e144009046110712441c83c800394200c1071340e2000384800081c0000000b0010003400d1315040c0b140c1a0038001110700c60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 889117526 1250 889116276 889116353
    0x909010905070e07051c1404121707200f060705070302060a02190c0311010c170f041212150603140a110406120207021201060807050d08120c07 63
    0x5014100c18a10f08060140042d004000e540e1200b554495031200c000680c403141000e4004204002556200c0106100500000850b12248a420303501c034801010840d092a9080303400480ba1a40003405101c620702d100c00341d4495052400e445441120051100440c10740d042a1080e02c0c03040210710f00150341c104050701400569408175500e0011410300940c641c1150030403080000940420110100318420180a40002c000c800280c200800c480030300d100000c1c090700246440048a0489200080c002261403200e06225551000c1c04511074400c50314260740c26003034070310300c00561a120491200b040c00907104032002800250380125105054094010165202a082103800303401c1c01055806103a500e070445048a0f590b14000329101c0405a12074003d005e645002940b21f8405a4900223320054014030155407510b42130310310940c1c0e10000c119a5003164603009219040c140140c03a05141101d801541c8890120005803034000c1d42e036100c4034580c2404641000d40384940105642040300340c2c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 889118776 1250 889117526 889117529
    0xe070309050d0f120b0d080901090918200a061404080105041203061d0606071401020c0a1106090108041b030b090703120e010512060f120102300a0207050c090901090507 74
    0x140f0b82041010b0421740456003240800401625101000441903003e901c40c11a0000414400408014240001c0c0d0b103120b201c14001400d8450300e2110710301040820002800254100c4000c090142c2d1500e00441525900d40c4201c1910b00c1c88024440014020002e00880388144c0c031844168041c1c0c3d10104005c3c0c01c07603e2070f0704200700141c1c01040601200c443c0d503629540001d8107d400ea911405145891462220b144003101ca0b40d50000c151000ba8106c0082c1c440040c5104550420181981c4070070311a040c000c0c03001c4240010a110b0104022404180300b4100108a680c03420112940329143c1c840c4640098032102b18035403060a08009001d2440c2d8500d08120380da280c003005241e2042c000910a010390040c160496a96501048403561007805a44500300d000d4581003481c4031540b1100c1c004e42200c0c24501c80c00300401048403031640c1f00d4180f4512004030754581241516142c0ca440000c0d00080412200e91140c03a42c100b509540d4020280d1242481c2c0d000400c00c80240d1620314100000c9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 889120026 1250 889118776 889118807
    0x303040b032e03140316050c03060906070e01111501030b04110a0308030a0b0118090603050f0f1515040513062a18030f03051b0f0303010e070309050d0f 67
    0x1200b40062400d2100b0b1000c1e048a0700402c5650401c1c00841c0d241d4214891140b03a02000c8288200c038004118000c42c40030360040c8210181e5034940c2d1418040c64440c070080340e03290001442803101001d13540c02503540303058100c9044200d444451011040800c00103081e0001e4a2500d02036042008120500302c0e40740899000762014031031140746036694031030343c04081c00480e5820f07203a09a01e0707240d0344100182c0c5009108000041c4041d82c0c0c84055100030191800b00f03581d00e015070905013803a9800000c0a42c0d00c501404010041034000d2641c41e0070114003c0c001d08110191848442820b940d180122030107a440110840c680c00150310b40403007103880200722300b240a411054030b00d48a80340040344404010780f500b4030860035419006600411f00380e42c2c000030601c1000a210105056101001e08104144810000380b44c242d204100c60b500c0207803e07041c960640c4100014803902010529064124135181400719410b03c0c155a11801d05070845600f80004040043c0e84a125600c01c850103d003105 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 889121276 1250 889120026 889120081
    0x1060915090914061c0506010b1b010f1d010e0303040b280b01081f150309020d0c0f051f05130503031909060e0d0f020612101d280b0303040b03 63
    0x3043d505c46d40c94060502c140c128a060214910311021940c440f00714400c070f50796000704186405001c558000341040d8040f2104401050f5883c900e85005201c0c008400078403030000c5003140d4540d0789141c40c040e0000c150000c080c0740ca848229141c407420314241d4801c40c000d0f0002c10880080400102006030041c01402c4009030190340c03c2803903001c9a8020f06440707204946000080350040c2c2580907102c0850300940021115171001c00b030213a040030903419105955110b240d03842d5500d04101c1c50803003d2403501410540710001501040c0550300508401030b00402c4016516510000603045402141f400540e40080c02d20405a03d80c4c0701c8441c2016000324208164840280c10204002d400b441e40c0080001e62100f01a400f59602d1a064031010348e0003e41c441c142e40703080307034403a034001c800707403051600340c3d100c684941040740356414001344110240c5500700700e141d260b11090700080340000c01100d58155280840b00c00c03518140000c0002d002140b0103190360b800d0030500209050002d03009a240501c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 889122526 1250 889121276 889121329
    0x30412110103272a0909050f0105062d0603010e09120f0d050c121315050402100c11060c0d110c01020723130509060901050106091509091406 62
    0x1c420a480000c03068002c030501550b03080c4c0c1c04110040c1c41d01d41300804182d108590000424556039000326104038440c1c000c0d5102c0f690040c9100703082e02d1041d41c0d5107901210b2014844070052a104404041141c141c06c41204440c05c00c0204441e0792007030f00b140c096400c0703c40c204122410200149000c101070044050720303082c01c010a80c0c1c1c440c001d0384000e040190302c5202040c040417075002510480202ca061030360403030a2503070702c0040441c50003508031103403805514046041489032242902c00c0c0e03009088045d0b00704400404442c41000d0400480f008130114001300000c0d210078015120b49802c400081c480102c0002c00601509450303402001c3da5408000404c1a60f64040b0310103040750403481d20310840540055405c041c14901c0d00205400516642145180b40025000360703016261403400c1c2e4030582c45412220342a1042401010007040030882c0401c445101914103021200492610760f14140c2c585d50340e04181c030042080100c404a83c41d003071000510b4400c0e0075444c070301d00703480080d805030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 889123776 1250 889122526 889122581
    0xa1410140111030d0c030e12070c05210604200913030810150503010609050d3503040b090f06040c0e06011209031805060a0903080705030412110103 65
    0x400c01064100080100d44030050b1000f0029603542006003201070080d0314a0f030305c000b00104507101c4504424400da98620306461001e4088807081604801001c450b42c1c109000e1010166000759640541c000b0740f00e080c2041007061103000c1c0118400c60001c809c0d40c500d40d041410305a8021400ba100b44400b200380310780e4690080c001103209606080458565903420382c1a80340310090b5025682d03005262100b10a580c7c1e00500541c180c070300c180c031030402c2142c0301e1040c00580c80080d0001030900d41801c83d01c0402250070000b06c0412480b0202d01c000c10444a60101540d4209440c1160000603020074000e280d80184003282d120070043e4028100d034501a110b0541689e0325102d2403075440e1040021030000c1c0d100300c1c0408058100070340280170390000361070002c05030600f00c3c50110b004256607502044918060741122500d6041e543c43c2002d46003591a0040158000202191a4801000700207820380384541c0c1114038038010321070000181d0440703001405444218254110340d418088010064 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 889125026 1250 889123776 889123799
    0x30c01080a050403020a0f0501060f0e06061c1e0f1d0a06090503040b04080d0206150121021908010e090d0f08040501110301080109170703021e010f050a1410 69
    0x407088200d40861107803200d0034180c0c14006030443c05480000b10f40c40000034007405420600c00ca030440414861505d03544c12091052050076107045910510404c681f042500c184418003110740f0302004002000d5a2176146441203091400c6802e01d0240c40d0682a800403a5030312404880c0c0a001030314540300b5090f03142e20b40d1140300c8100000c18550fa030700d000c1003d104041060714080d1940764021036a403034481902d140c0d18001c1c231084038011712a40d00040c003e0268a1040b105030101a1200300d240d004400450104051059110115650a001042408180170980e825075881610340079041c0d41071103000401118005d1a410a90744a84060415154052031111882041d45040603482d111480c03d1405400440341c082441d04000c000444d00c0a41940800103243c4502d200041003041001140301c9401210000340243c1c20440c1c0c00d540d0001400c1e601c4e0704c0200340380000101c03032180702c070b19400307c0e9410796621288c6a44c07580d80609040e40700030420340000c42038160386056440c214280d00c0c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 889126276 1250 889125026 889125031
    0x90708190b191803051240050a1103120c1005041401091202070603090b070f2003070b0609061e01180b0712051e090f0301020a120605030c0108 63
    0x3075801c0c074021500143c1c07201c50322070126840310610200d00d040080c001e800c0104861840e40d01c00011506042c03403241c1511440c0501e03a0a036a48880944040c01d042c013521b044040d8001c15050070303000050050128094040c45500c0f0b01488810b450b06046ca01000500380c034005140421009492500c0001c1c00040c41c0d0b40b01201103000d039a1131070401c8003928042c04d07000c1700b9800c0100d01c00412840c4a103400310900c0a600315041c00790b48280450a48100c207402030700315118040458141c0d48540e00c86412803003681003050405000e2001a10404d9410b000f6010300c0c5c0001c5007103030030848026034480e0050380461720800c490a041001441042510070312030102c0d00003508801141e40200d410b1a084a0110601822559524901e1640307501030b401c1140c48812186003114418042d0381070740c0c6082004640d0b1100a428454501210303488819069070064036603500b5805a41d00340020b117800c40c0715a864945072044180c90b0740590b8002d4004a10940128480c91511b9a1108103540e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 889127526 1250 889126276 889126291
    0x2408070f0f1a07020d06020d061a09010e0f030a1203050a0b0406060f1817070e0708130f1704091b0905030a02042a050a0801150801030305031005040203090708190b 72
    0x9a443c3c16920000d0750305140032400400060020445c4403030355116500a1045400300c4015900606500d502c046c1544183c17040240411000031501c8224101040040d004603001b500b12140600e5503140c94454003020351100000949076010804100c1042c003e581c0c0851050380e05114090610001a064054040b000402c121190758020795140701c00a021000f010900045045a40c1e000302868481d84a4058070008040d21000300346007502c5405900c0c4944080349015080e085076948200703c0407400e01003514082d824081d1400048440784c01040100707800d0400103110072115184a41e45c00c0200d0842c000d100e06044100015100030490f00c00a950488000500e44550303861103a80300d01c4400701d91f0012680302001ca08154106008040003030080d00c070710318503a0340c034148200100c1c0001e00c100001130f1840c00420010303000e6006541c100c02650040740d41c542d140c034007117800c070b130002c84451001d03a02a001c10414a4410300500c00d0400340c4200001402c1d2083e115151002d50251986 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 889128776 1250 889127526 889127579
    0x40b0a03021305100c030311040305030403240f090b0601030504051c1205040507170102131a070f1104060603020f041a04090f0902120c0f01032408070f0f 68
    0x94080144601100014103401081d134406840307111001002c806608404401291601e000d001549450b4400e440c01c4a5101005600e014216580c61056001132030003801800c0d0041c0114a00c9841c40c0156008035108510008081ca064285a4a80078016210a040c07510345018000440c901140b4428544100501040307a491000801c03a880c0d8264000455914507007800c1c4410804082455011500800f40780641c0340340c100803050803440b9101121110300d4041c0d20800c10203403044007602071182c54448460604660346c8a02e00652400c0358102c4440e40804c6064405103014456200a803040d07250443c1450307290701040c412441a0b0080c0c4c0340c080da441d40041840034014007120080c0804110031701c601d0714900040000313000100003c03442850341d056031990b04880041c800c500c106000f0060121403d02c00019401030800c5a0404480b030300084620a0300a50405050b000704600802020801e14000124010701e810f50084480c0c40c4030030404002540b0701c240c1a10390400c1c0304040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 889130026 1250 889128776 889128787
    0x71b03030c0908061f0b0c0606040b060903060f060102300706090c090902030c0402030f06040f0e0703050c180f07080a060e041103010b0f010c060e030d0e07090b06040b0a0302 77
    0x35180b05486078000d120511480040254042113024480c516248040aa1070015250f801904481c01a050341300300581c0080000f60303181ca0560440000503201401c054076004604011a06262003142d5052b0510034881c00d002d081d583c1040042c2402c0c2404058040d8000045101d2070107080a11802d00c2c4000c000c070301c0c50700f0300c4410303803101e0342140d88a0341c40a8015034a45048000d85001802a4403074021081a02c540307040c80e0007201e11441140c1d002000da41c2e201400c0000901c5100030316211540d541d080200391410421141010354002d4005001c2c903e040010880c091858403200b85840c0546001d2180791990881c00981144280c04c00d814127903a140e41d00c2006114944c0710301810b04250040c4024004208000c01154030b059009000c540c039000c080c42214016018041c2c00030340c030004d0b0400032032855800402c80c1600003003500e140c208008103907000e880d1a9640740c070181c1c00c400020400c0e140548280f441c882d2068038450b0401c3d03c3d00c103610003035016405540c0103040c0c0000320b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 889131276 1250 889130026 889130051
    0x20103050a141014090124021e07030c080102181002010905150a050a0c0219050c13020322080d090f021207170102040810020a090902030c070b071b0303 67
    0x11041d02209070400c0d030b054624000d0280c1020040a2040440c1c10110781c040c0245030800050b9141680c015050203c1150b0321100d940c40ca141c28080c565085025504403805055102c03004000351144d900003c208135421824035064400c032680c0204226031041101000c00b403045d0a40d00c40010003101c210021046000e002e07400350041100081160082c0312602900c6105801740c1c60196845880402c0a682c9405030302e0304541c108580c0742c000d130740000c1040f40803400342c078050080684103009a90390807150b8004944404140007102e01080d03008020041c0b00711511122030942c0f240340383c200042c8060307512049058499201c41803115500d80203140c003800705210746e040f962540540381601120140e8540360b1140d4550050800b4003088110400540005000b07a5069943c1c0c00b000e400540e4070b03a9900d000030343c825090760090154070080042c9a440300d101940c800c51510707a1640da101e0003440c20220081d40205035030148040001901c1000000903942c0340300681c507080020340c0700c0d00f541 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 889132526 1250 889131276 889131281
    0x3040c0b040e0103060b030d0806060d2307032003190e0a05100e0c0a0510092105010c1412070203041206090b010b07030f050f090607030c020a050901080a020103050a 73
    0x4101080c400e400040000b4448108103096040300d0140300b0800842840b401016192014403c44800203001040482c41324944040105402c43c103007000060102e200800b01c0038000e403112440c1007601e0b104020801d074990940140310142d001508491030680300400c2c000d1481c00050507894495503010040008003065138080e100c1513100408442901750545030040d6070fa031143d070007516a07074189221040001e03000203164148400c010684800c03a8103150500c01200184000301c130400c500500300040b981d0100d86903a0100450b81c00510292006003481420f40309940891000c20040824000d203401561059905003040e8405004154851a00032031450143e074000ca040c0c0c480b400e07000810014940e0101503114892240e60410b40c1c0d0f079855a401c1c0c1d01440d80c018010072001000304490b01e12440051404c40c041100c01d904001c2c0c0d034030101304690403070101207000c50b640f554680c0070751905188000c02014125442282981400010f98540640000082c103254451000c40c03811051b0b40c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 889133776 1250 889132526 889132529
    0x20919360b22060f1e0e0d080c041208032508010339081b010e0105030a0e06010b0a020f070605190509060354030c070602030a030609140402040203040c 67
    0x21001340b00481208001d080240100d920400f81c0b50040451078907104000d000310030020741840081e000c40240030400f41d03070420340100013012100f410000843d00302c580303003045e2040a024603081d82e12441c02e1038080c2e20301000e8503243c1c0300501c84500c50720310b01544200203e055a80c80720a0b41c207032120301c240c46598603480343c2400315010741412043e40b640344503014040c00c9402503400c0711110015030328000c3c1c0484000c11014001906e14604009550041004503005280b0180000f51444c1c2c0e26021403c010080c1c1110720002c0e8009400300c0d40d42e80c104518880084024080c00e0307607030325151004d0010310400040d020302c1d0403080092814140540180e9080300b07800340943da030703e14040c250a40942a04005082c907040080341c400c80450b01403100007140e246e42280741890b41d50714800d40d030408102c10200c0341588800c00c437414290000b0700210380200700300c1c0c00454944014050107010b55859401000070240b81c00caa0040e855144940142c115806440050307030307070720749080c0314a104255 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 889135026 1250 889133776 889133783
    0x32203020a0b010b0c010c08040206040b0c031b06061e0d031110060306241d280c091703030a1a0a0806010501080a0b060304020919360b22 61
    0xc0b0000000c0c020703070901c000c0c40b525403c20000c04c8504c501103410781b006141500d010f5040f460070b010034410040804000c14110402000f1242004001a503203c81150202103610142d0440828080706d030034117452003032809a00743e45007103040c40c4010100f01007403020140601001403440c178040e005101031100014411000c80140103064907420000082c089016a080c101160b100b0000425107030075080e40705a4066030320b00801083c0d118502e0f025440c1c00303801b00e080c000500c1c560801e44c0031142102071031a844802c5c0030410b07101e9000c0162803d0642c2c0e0010550024840c1404c1400740b02104803036002c52034800015001c100c01c040c0b084008924507015030014589640460281703000181d0394100c46003645d03a00056030360003010005039181c050000d0f8211074240040b800501d0070100c82503100900c465003840120020741640c0540f48034240307040114035804804001c582203080c500c0c134200c1c0e038400c1c45076040ba91580c4540c0c28140061050300600c28107610030350719041d010003601d0100e40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 889136276 1250 889135026 889135043
    0x601032c031e040e0705090402040e0a05180303131e05070807150e06040302010c06090204240e0c0a08090f0a08091e060d18021009030512032203020a 66
    0x195184200e6903540021540b03800e070050150030804500a40049805403103c00807444004d84031000140c441d60013101509500507024080410300108481105100e181c0031400841c003410000700201c1e080301a40d100c050341d50010801c000f40e4a40c400c07030028105500c000c007510403c04800e550f00034440c0083c8002c1c85d80c0906040007520443c0068010291410540324003807841e600c15058481c0040703400034030f0f00402e06000c2003000d0760142480c842e243d4001e83e404034240089500241c200c840403195140d079022410303c007400c60321525440350080c1501000280c200e0900840205240c02207403101c000304003070100000c00c560001c4c0410560b448400c0c007101c0301c45005103003501042c0c000340d9000c0c0c028021481c54003c40020a0004100b03c4005004c0501c0d11420f01c101c0000341c9280420f01ca040304483c7c1d032190060300c5010a03040e060f40c0c650365041c070039030561600c9400d00415102e031031700d424414418001c1e04e4425007105103240d00f000821291785000c1d0b00d0280d09001c039010002d0510030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 889137526 1250 889136276 889136351
    0x4030f03080609070f0807141911151504094d1806030f030c0303100608010308030c0a0e1e0909070807090504020a17030a0909050708060103 62
    0x1074010380c01e6401050111a00c0403e95200b65080f00c0d01c103440b20031a0b0001e00c0034004980340c0b9000d51000400e01c10041d0080c1d1a0039166203480e085800400000c200145042e4240c7c5000b140a000d80031160300da601c0c0b005101d041014100010b1100b42000a00c9a40d54060341000c004240751220b070707500407100b000b403000302c12103d00000c0d43d101c080c56078254900c01410040c2c048400710a51807040360003001c800308d00c1440c120040c010480104601d40520511150004c030301c008101404028000360700031035403894032a855003000981030f0f000c1410b0065a070700501c0010b103a0810349074014500803006482b007403c0e410860b094048004200c0c0c0201484445104030000c0060280b803a64090707800001640b644081a569440075104071281608070750028458007465410468000b40020030071103c0680354215a5201f0030403114214860740005101c0c54800c0e040f0003c000104001d10302000b0b6454000360142000c103004090b28100341e41c03580c0b1042c1860481180c041e10b1081003044820130f070b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 889138776 1250 889137526 889137533
    0x70306060e0601030c02060f061207030f060f020c070605090f060c06070e09092121010905010518071808031803100513081b010510230f130204030f 65
    0x5110398080d2040124a100016100e540240200048404243c0c01030100341d585681c80d02d85128060002640710f405004c5400043d181040306030003941c0a0703900b56030b41034080d24200003211100540d41c0000c5d401400309214542000c520700040b0356242c10031540c0d90301041c001640da0442e00f00c005504c003102043e4034103040d80000341c2d103100310000e07111010098102400c00c00c543e00708903524003443c2e100c0a000d40858000c881d030050304002c07909802d82891519041a401100a05103840b07005100031b004001400c40f40c040c2314010f0074180c2c0c100400c005d81520b000d0042000421480c1402003221440002d40c00303c128240090240c3c0b01a81c0d200e2000b0048400c0a4055803102440707071049100d1410204039501c030765030003140421700c425503800705541c4110443e0003c5100c8210100c142860319072400c0203004d598812100288840122800c1010030100300100c40115031400d00791070038060b2183c8848003054000d100460b03001e814015643c03da00d01900c5075800040090ba180c8038450100b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 889140026 1250 889138776 889138781
    0xf090a09020c010c020703150e0a140606030d0903030f08060102030d0f0606140f300109050106110d08190b040905060a0b091509061201051504230411060903070306 72
    0x42d125180000d10414130340d0302080760303a0041400068003104c2a050320030080c1ca8154440100411170b801950650b084503110441c1c15045130185030b51581016080000c4c42c5011720090851004030704006460505503103005159285e001d072131805012200020400c1c80e8020010358600c0096400c0c01d211038401c024043c0060400c62141c02c012400701c071000010724051005a0300c41803a03c40a0505100c9503264941d1980e404448441601000d60350b00c000c5498101c4816029240c019804900c5525108006242c0400e2601031116a0015000465059440342103d07403c403031000c508060400b040100030300209240b00007240e0191800314100c04100300401c089104590310399042212080910078000d14140c11103a41e01f1000803408100340750f160401c2259084a000303041582d0103004d07022403908640d420740d801100c0034000302d410360307107468240281e103a103080c2d121103102a500360314140d03106c100380030344000c003448840d00101e401625a4020f03a0403104001b000c07100c001d175490a00c00c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 889141276 1250 889140026 889140037
    0x110d110f0d150e061302031005100e0c13090b0108061014130528060309060209090403030b0906040e070b09060d11041e03020d030c0c030212011a03010606080105060f090a0902 77
    0x40c04d00480d400079048446056420034895005405040400c0d98481400004c0400900504c00c904148402150f0980e2030f0000910400070703d00070560b501c0c14000304888407084c07684541c6d0003a05080c0302c0031060b6805503c01da0400f8090303850b44480c05503c0700503a070300c0384e480c1d50708000b0000208526501e20b4000c4e120f5421100c00b5110860210080d07040e0b1f40303d080f2460070508a800c000d65040007020702c02e84c1715008040c0200d40050501d01da100014181040c01c0c1c4040c1e0000380c82d001035915a280c40c40d00140c01c901d04890404c036070850381d0301003a02d07a1018898000c41c8000030542500588a0108582003880c1c0320b0820840104040804005504030f4001c0c204803603801e090045003610380150b40404e980e0010300d000310008032680c04580d6042c984800321201d0012001c0000140c50301c1e2401c5000360304510000c1014083c075101c1648015000202d02e101c0d130305209003004010341122020b4151481518041c1d1760340801010070300c01784130f1206915080b45c030960002807503084942c05000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 889142526 1250 889141276 889141301
    0xd060905090705030715020c031009110906090711010f140f0f04150b04020d0c0503061206060a0e040f0c1409090115090c120f0504110d110f0d15 64
    0x85039854401c501035036036805025150b00b45e8491042407200e50000508110303003080341c1c4101e40c1c4400450b40400d041101511641500a480b4500c000030421400015600040c0989010003145003100005801000c041c10107030600038038449520f1041f01c00c2d0041402e0508440080c012004000052000741800301c48000c00c680752000480c9100d900c0481c207034060340d0464551007181000205150040c03003024984c07a44140d0030049410000382500aa0340003460310348070103450b031074110140700f01b52940502c4168075410500c10401c5655510f803803001504c4c000c002410301035980e07250020003400c44410242000380b010000080005400f26a41800002078425083e5625841003c40c01e0359030046885826240e103031018071030b501855105c51700d2b00089107020801400d40c0c86000d4210f0f210031100310f504a0b02c5008110900810b0910420103400544812803d80310381e8894442480c81c82d02c106220382c40030324a482c2140d40364505903543d07a0f04580c2861300da00c10580740d103004011031003040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 889143776 1250 889142526 889142531
    0x1401080a03021203090c04051909030807090b040810051003020603090708010b01082502010f020f220f0605090303040b03090a0309080d1b05030d0213060233090f01020d0609 76
    0x110f451104060f64010b032212001403203183e00c0101000041e003402091141202c541d884681a00306290241c4002603010b80c640c0b4400d414120300c001c181c01c0c2c69412005118008020402401800007000810782ca1034070701c0014207444c0c2d41411401030660b0b80c40a90f2120f000300500206c1c510120700203007121030890003081540080c1c40103580818088514507032202d20240c884151030070345052000c41c0381603440002030000c07242c0540c0b8100c0e040510145146080807400c0014000040719001d40449a545030100700741c1b8014040c989a03000d4042c072410410301040030921601c0810903140501006100c0580f01d1620070780d040d9660240c1002540080e040c403800081080c80418981950340c1190703122134070a00303064046500400c410074100d5032880208180413002a25102400100410000c43c2e16403900d0110001e15100701040e1042180030300d001450301c0a21003080104000c03c46140c1c400055884282c01814501020280fa00c40d5000040e911041e1740300b60712000c10b0b501106000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 889145026 1250 889143776 889143793
    0xc031b1506010305040b040204241409090f19080f07030305150f060d0c0c0606060c051005090c12011803081605030f04020d0212070816060f0c08090102011401080a0302 74
    0x11415180c4c16540030303200b140440c005c01c000d824150080800c07409540c01014a011888a03807580111281d031000510103943d10780c4581e01d10b00504d501d034226865800811150303260380c1c001034441000c600802c0c42c040c0307100281010050000305680d840041c2d030084a446801c6412f001d4068501222031840140d0640b244082500c1c14100d400c0c0b203003001501107400c14000d18100c0c0c00030101c40b003180302031245a004110004482d40500300c0a8161a90349000e018102d00d0528544851034081048660070f2004000e2200c20011704407000308001c60380900f4401a81c2c0f00c140c01006011141d0840341d903a264070340c0506401c07550b098042c078000c00c01602c4400c0181001c94075800306507010f00030501a00049001b40c5021403004c09020300040c178040c1d20080203222680350001a500820310b80c0c004441c0c250080b00c40100d00300083c129424004041610072078000c0c0008441c0d10014042d020101b40c95456034801d5005000d40d1480ea80d81d50341c0d550b103405c0e0700366580c09403500490043c4580b524 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 889146276 1250 889145026 889145029
    0xa0b0c1804150302010e01171e07050c0a0813031a040c1e1e240e01030902061209010e1f05060a0e0f22060b01110606060d020c031b1506 60
    0x250750301d0202021000702c802d8155401114a80a01e000d400d0404c400d04e01d64601c19407810305140d015100c6000d041c01d000034048180180c02c000180a44280b00c0d05001d100d44490010404404440c0e020f1355aa54590702e00c000c105d600041500080c00a900c14025000c1d440402c01280703001c3ca001d001c2d56000140e84590401107900c601101c03401c008030003102044816110003941c42076880024201e41c4950f1648415081031b000e00102c2c08010b4101c208141d08660000c003202d200350001e1806100703200310350f0045a100e114001360400c02c084002e0003d19046402e500000400212009030340001a4801b420b0400d40895144488802c6c500004108149007481000040714071200415010344c3da0041d40b0400710740b0007828156505804c40c551031807020b240701009540d91096500044841c2444001045011a001b0f00d908550056003400300c0f950300c5800f690382c0d0102001016035036217280f60707074030303086018640d00510000e408015040054001081d40001c1e8249452138454641e900700 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 889147526 1250 889146276 889146281
    0x30d0b04023c13120c0b070b100e010501140304030c120f02100e070506070609050102070b0103140d0516030903052b0306050d120215100f08010209061b0a0b0c1804 72
    0x1101c40311000241c0b8020403420300d40d01c0b00750b00914045c150034090903a4503d02014568405c08046480c00c403100200610440a081008003800c2c4605402900c0c1d0f0400c80083c008400014403e50200d40100010f01014440e0039561070059101c604640c0c0d4500700b00c00a8800300c1042466009401622200b5400008910034100c011a030b1a00900c2e0300e5141c1014010158042c0710152791580d1511400d9020440c00d000901000303119003141c401c15071460518854400c04141d400010f500480398540540c0e50260503120300b60b50102e0501002251362078191104a035507400207110b400741341401d07000d00030442400302108108540052104141c20402c508a640314041c541d40910300d03140c103001003402c0d0100c0f07010380c117403a004860b16440c1000c10380f000d85000703c0e048038012684c45400d000e045d080360003050080c4030210081d41011848000100b0034020282c00404542842210011304141000410701c000c2d00204c2114650401d04140c0b80b481e070018894000021130140e01c51b00904261 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 889148776 1250 889147526 889147537
    0x50c090d150b04090b0f10080f03090a0527090f07122306071214040f051011040e101d1501080105030d030e030f0a0e1c05030d0b04023c 60
    0x43c40001aa54404102c02c01b402c0c1c0142014250145540700030819143c208500c40095491000554440c40604100309503000690480390090001040084585411407500507141c800022140304681d102c2c41d2007454501e2224501e00580700e4010006081700e41018102c504c180a00400c0d070381ca0f0602440c41e502504c5030401603415511103000039641d0703031003610001e6014045400116400c50509124410a0025141a030b0b41e12000011101040000c00c41d024180540740024045602c3c10100030800340100d1180d4908411031200003158900b08121107070141040310000360100340d0901c003461010b03b040300d4000c080d6038a600d20503036a41c01101e005040300e80050003403029111900707007200600303800701e4607507142d00c0144019200c1207211f4016020311201c0e503803075501d00c03031154080107010b1801d80c100000700041c0d1000480411400300449061800c0a04046a00e181900c086002032107040380c18180804003849650420114000c8a000051029494110031244800600091050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 889150026 1250 889148776 889148783
    0x23130201080420040509030a03050702010e030d231f0f1802091206011502070e0709030201110a02062106040b010e010c0503040b030108030909070207060f03050c090d150b0409 77
    0x14400100050400000e0300f00007440441c48500c02c00e4a10040790540c2d50543d41848550008208020055414030503540c0c0260725200a11040181c0c40c00d07585c9034400d42220040d40c5842e5010041e00f46035072408185100c03030b407044e04003140c1780420b5401408000f01e280a80f002403005030000d1112840e180c8801905c0b03134210201403101843c69420300941c00400615005454074102c0d110a131000d00040c2d008220300d105040f0300c0369048100a00b03060b400e410205503964803006000c0310310351261804042d40d5080c20f11080d0940386050941ca80215604002c0d4000300000b1004007581050808040b12b650500f00501c464075441d081000b039510480780240001c0c02e0354403201842d031040d00b40f040005e000b41c081d6407905481d22000290755100742c0002d045c6600c001103400890420034825076100e1030b00c1c8080e000715410080002c180c0409204103608164640000c100700c24070504c2100d4010000502c40011071000e468040e40d089254440341501c1c030310f0b110041d0f0103400c1600441c0340d0180d2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 889151276 1250 889150026 889150037
    0x7031203020f040909020d02040911030106061707050a230d0c03090f0209190905010606260708071413080705123004030b010e1819080d23130201 64
    0x801c4c2007100242103a003003d9911040441401026272500e1041035045401010b203100c044c0015010b00d8207407105039112404008211008801d541480c021080c1c07c440d46240c000c0e0380c0e910fa0034044802204510708003030f140c0001e0300d6032041c1c0c854100c0200000f0900e41c10502441003800c0b410f0302251151900903011050f4050311000500d0507421560740000304228880c056040c822403003080760b06141007120aa0754401c0e090104603003010350218a0840da102038180c00d4028010b40c008000c02400400901180701d02080c07803a4010b9030f400b01d001d040040303140d8444800c0c4006d1250303003002c3e00c0b800019000d6090041803a0522041080e0510228001010400700c83c500d100020088028204410004821912010000b0100910040d07004600d1054503505201c2d008070801c001030900c204480360001001c00401000c51005541c5440801c0c0d00d56042d00d60800e00540c2c403501c034480c00101d190408000074003010003819141648184900300f5203607501803800000148000010b4007055 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 889152526 1250 889151276 889151279
    0x203060c1c0e030c030a0306090f06150804020d020d030c0308010503010e0a0308040c03020d0b04060b0636042c0c011e14030133080c0903031b07031203020f04 70
    0xa0550b080000b1640c0740d041144d2a00200804071030440e08500203040c0082e445482c01c005080c0c00f07020b000d400c808001c004002d082e142044c0741880c81d444d8600c10090048400000d015540c0b01102181622703000381c044803101c9003130f1a00030902182040101c02040340b8500201c0c55041c1442500d5a07990b84000800c081040c680f400d441042d0000c1c01156460318051003c8010f840f0240f0241009201d01e00da52400c3c01e1524090040d5610480214000c1500340480e004410320800d0b2480ea05e0070382500d440c1c00c0c5208a0303c00d918004240c00e11138000b1b01b041c545000ea22034250031440710903d60286006040c4140d11410788500810f4401800112043c07144071151018840020581ca164140003480070010408031000d86c201342d204456031311110080700c0303907180340c0341d084001e158152940130b5003c80b0310400500000e5010b41025407180e0046006010b40d00c00b042110850615600d950f240c0580a40d412552182c0c2030000f20740084810307000c0001c050181c003d4400c1e442c600c165950406 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 889153776 1250 889152526 889152577
    0x9070807050d150512070602071a122508070311120a050907080a030201060e01060512190209060c010b030d050a0f0f030908120f06121921020a0203060c 67
    0xf48012100f04203140c1580100040135680c13160200e4600c0c010f2400f80a4203454528040e05104c3c85600054800c21244005000e0800c4070301103c120b903c0300d0544143e03a80b41d2081415440703864100d49041413004854514007680c0000d891445120f85982c1071042885a40303a03034819000d40303001d1800c000b0038800401c40641c2c05400c8a03500c14810011510441c2e520231165240c03000d000810303000350350354072418400b51802c80703a81c0c0c1c05440c1030f0510902e0500c3c0020401540c8070000c0c1030011242140310a0030780040c60380c04a5041d66002058603880306842d019090088c408441c003144644242074000596600480a4440c2848542c403010154100c0a40644080cac9482003c0420076a50b84500400113040301e0250490758021081a1013a1401c182d44030000d250141c21140b140c2e00710001c113105114001280f8010380541600c030f40e004056854031484036600360020030210f40300c07405101c0d251680000c00c061418000c90480e042034403202415080340c8541008481e82d00102030300c80211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 889155026 1250 889153776 889153781
    0x106091a030a0e0a0f0611040302030a0b0604150332061609030204061e050f030a0f0213020705100b060a080115140f040801140609062b06020909070807050d 69
    0x20041c2d007100840c040301001686410041608422a9000aa0b000b00420710400d8400c0c3c0a0405c071010030b06207010304503000a6031b44c41c3c800704000d00d0701e845030300018507507151a0000c05100c2070303052148904945a1034028602500e40404280e12a81841d40c14500b90419a4115420600c01e01820007a01d0313801c018640c0c0341042503c90300b0308c07444070000030041c0c43d00e204440090944803c1414800310446101254001a62100c2c1c400c212002e14040190340124070208016400144800d02001502c0854900b103a803400c0c55490a01c00720320b01c0c050000c041150703c00c52240100400030b010240c002c001c0117005128194001a55102c0140b105e4903c044450507180c40f103081c0f0865001d40d24640c000141c1c005103215010b010085020003103d0024010710b1303840c01c05064050100d1400e03101244d6a1b100c01059031f4459601c41c400c13402c005919421185560060320360200e03841602d800c10001940c09146594001c3c2c4440001070340d16071044541e107004400582d02d49282c5100513066a01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 889156276 1250 889155026 889155031
    0xb031b1c032c030d08091e0c0301020d0608070b1e030a090606060915080c090603130b010608011a07021305150a08070f06020d050726070f02090106091a03 68
    0x90010074510307440c04030401800d02c0c03003021040d03881c050540d0340c15052604003803048107940144034588080c01601400420224014250210071040c0502d20350300301490803000800d11601948000341c4101450680d401610035529202d044070301d0207644001032a41c5100305a1405803e03513000c00c0001c102003003d401907400ca85203a901080061442d01c507041201c6c030b540d00c80760110300030300340c00c22010614a0820004000c40c1c14803407180c0c034200c006100140b01c0d44c41c2452044100100054543c81c480d4041c0e11150b0301b00c03620f90003560b1034200203031000c078013805000c80c0f6004828219400c5030303108080b5851a6406021031103103e02c0d04452402400c005081030491011401042d0150740350380138000010b00d1420010014140b0340f12100b03440e8820b46d0400b02c00c54100103880c101c0a034002044454140c0e0201d143c81242407a6820b000700822000700340121048000790a0b000c1c41a4031103690341050007103912442690341c5020a5610642c07d03c034051307050009503205441d44500c0d40241d50b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 889157526 1250 889156276 889156283
    0x5240304020609180a290f0d0537030c0303090809060703030f0c050910080613060602010911060901021005091501060f0e030a0f02040e0f07090b031b1c 67
    0xd00b002c50000000344200c0d0004c90000c0a0141c2104000382c4402034068080c044944021380e500c41d44a404883d90011002106680119580c84415185031540603868102c950040c0c00e80341c80d042c030201d0034403041850782403008008002000800035400c0c1c00305151803050f85030f12400682c40f111784d8103038040e110220051340c0d5903400744650a01500c40c00d0090520f41d10a540c00107400d1452100d440445103004102030406c501445400c0c055140c042c04980500c0840c1001006079850200180300d40040e402074401080c105980092440d40540100c09084e20400c4c02c03082c000c02d494241702c518090303003540c18016400b48034511201e51a41c0e12654200341c0e01e40c10b4685c070703482c604184285a5001ea000c040051800340000c180c0a61040840711200400c0300542179080c0903840d03880d806019180f02078442c035500e400100480e0003c00c0b0b0010181d0740a410f840711541d4440040d00200420f42110b4028019400c03002076281001510b242e200a0040032249020740c190030115401c0d0a0007002c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 889158776 1250 889157526 889157539
    0x5100e09070b040e06012d08100302100c050a08070b09061303080a0c02100509030a080a0c0c030e040e010c050c0721060b180c0301051c0203100c1404080d090524030402 74
    0x68280c5941d2148507e00d0742050481d4a61002c29500e005205c0e8800402c0e5030700c462000e00301440141d4401a0001441c1e42c00d00e843e448201a0782482d90400c1841d581c0200b180d000003440c0c400704071101d03020500c910302d4042921a40d540384c0c2030800101c411000001c2c000380c8003000146408029034880390810405104950340038441c06461070440e80241e0b08518240e02c0480c2000106a01445607507010322000b806100845e01807001910081413500024103110110301c1114080d151a800220704601c1340c4000d0014640c084005000e40e0711801c1c8800701d0f4001d4180114603001b034800301c80c1e41405900d14442120f9225180d0800900749403080a07480010600742218518003e0a610300402110070250b940703524100405c41171380004249110540f146280480261741c0200f603c4101a080c510049506078a40604492104480080113907500000c5804902d40c2000030714112511140d803100000c00b030b180c0c81008002c240d991040888158dd0b8140050b80310f00031000745810601c040c000303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 889160026 1250 889158776 889158797
    0x31e050904020d1406150405060307030f0f0605120a050c092a13050a0308030a090602090607081801110604142d1b010c0b091005100e09070b040e0601 66
    0x3000c0e680103c101240322074840da60020410340c4100e20742c1d0819001c80c0c04000c600c1030101c0032041d50141d44501c910a10b00800019203070b5010350040c402e14242d42c24108240c600f40c41398800241280d0040900440c548034840c0c0b00d02c00c0002d0700ca840703c0d41180003000340c0305100c000c009040301c4c01080319610170b07091030200140c140308089049600f0384242845403144184c20300245000000c2d48028401c405c00102000810307194800c5a81022021601003503603e4182040000707845211034a5400100001d0354405100380d25014115040340b1448280c40c4003419401151040280200c5041c65004000441d00103803028402c010400c1a4805483c0b038091010340090030143c04c10031100030b140c90310021481b00d4070144010807540c054000902039032074a0000003042615482801003a007d9001c003c45d190303080400103203440741c1d120314092140c0e00d0044400c043d620306501c54102d50628075004940c4461022a100040c2c40b0418074007400c007851301101d100d6128010388498140a0390921 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 889161276 1250 889160026 889160029
    0x151302090405040c210308060909070b19080108071412160e180706091503060b1303050d0e0303030c0d091416080105130b0c040f09050105011407031e0509 68
    0x6552246000c0c43d4212a09445d24018a07098801c03003d20f42c031100d994100460002c0e80120610360000c000360345240380c554801da40743e4603240054111700048000450031110005407000480182c040079a100e40c40e030390343c5040720782e601c1e50580159a0104104a00c200c2142412603400c44100203023001c44031440d41000316180a28a1900968401c001d1038042100240b00c1100511a00361200000d210842c60881e00501120041c05803510020841d00203013012032090b0040c1d406081a003500c159114204410340200301070f14442103540e800b50f00901c0007864000ca80111583d003024001e1895036035140c94001c2e9592105460b242c40c1c1d5685c81c600008503800f001d17061020303102d90000301001c008800100050900f10380c81201c590b0f041a0402c240500340c0c0d05048105603100704c0107161030f21160712400244c0126001840203034400440011200c2840c1c005030b04070b40080c0caa0010f09009900ba0140031311a060000c0c1c0032404d0b6841012001001c0008007525a8040c1b501c40e082207140c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 889162526 1250 889161276 889161281
    0x902090a09060f0945080f0703090e040b010b1308030a020a051b01020c04051e0c120f07050315040e0f0c030d09051f050d111801081513020904 63
    0x402020b0f00940e8481c040c040486640f06082d0f5180d00c809404c1d510517461048550a440201c454000d542d0f0702500c1140901420304540c10b80e00d92003290705072503442c851100d01190f0010b00307041c0d0000c1e820f100c0c0002d180f0308614800d801190040303401190760b030804c0c102d8040d550200741c00c64098106224001a07600342030001d40865411607000c0d00306c1c20b0320360a103540703064184603040d2100345204400344100d80c0c00148852385100c2c20313070307020406548100c894140c0d01d00b8540800c2c1c4005d54081005008142c080080894024045985125485072441800c0c940380496808012031010004200115042900000c214000420200b07140c50b4400156040002130841030515900032800300c1a51714003407090341c0481440380ba05400e59850680010300c01c1c099401040c1655080c030000c074041c0e62162040b50b250941c00f0f2030900070703600d140401045943c031507600d140101041004400301c43d0310aa004601910401e820202c110340702004106003401030101e00b02c0160b900f0404016280c6850 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 889163776 1250 889162526 889162529
    0x20a06030519020a20010c200c01120b033003190914010c120608150705031b03040b150405010609050112061d0105030d03050405190201020a02030a0c05011d0a0902090a0906 76
    0x1710b001180e024a112009802842d01140304020640c1d40c8007000300c0c0c4c0740c000a90405404007481c0122621210002d41c10040c00040c03589501402410651801d25141d80b10282c40134030748948880ea07207503000e00d03d60441d0000740c506600032903019038400341c00c44903a0461180c5030b004440908140b130411000301d0844801c0042c000c08601030228801503190388e4130980c001400b004000e444a51004c0c00c801020074001003107407061000110102d402560020001c03000303111184007250b0303207040a09003400b4030982118a00f001d0308500c4117410321800c2501806040f01c84507100c040800e410a0700640740e454814a000801658070100021390201010492844820300708801000b94101030a042c01d0038515a5a00145401d003401c0c0300c0054400602c8140c44050b42076100c40e80003591004132b05022500070007950620440d0302c80c60a1002c3c01042130100c5001340c0303c094150030001900340101d1f0250b02317442d50028641c0c004000340840341d0024106100003c10000120340c40d5070b64003007152042e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 889165026 1250 889163776 889163837
    0x30414010c110c09010e1803070609050303160c0b0408030c0c071202010e09010324020705010e16120b040611091801030c0506040e07140d0f09020a06030519020a 71
    0x20002e40e101c180c02d010303403500c3c1d080503961480b0303940c1400084560f0030b00242c020b00360108901c0002500000c00e00030b491001c0c0c0d01075014031160380c4604105641c0d800982e441c01036280140c021156240c028200002c0c1968840f022030311a03a1507864000c51500000e202e8402c64108100c0c20200060a20005001d0aa0322a0501b15200f85000050032003220a120902070064440180302084c07040040d14000c2c6501100c482c03c40c1083e80c0a80d01a01881000615942c01d040c01481c08842c040b600d91480140c501800503102d1b0b6443d8814a8000e60050241c000381440002c50003003812608404416205442e03203510f029101004280f00c402a603010040380f40003200140700300035100b401c00c00180000c8515a042c5400c2411007400c04002402400900020103154680460b05400b511034440004508105078140004058060407500c1c404a215224080000c10414041c1c80703043e0003820705801c10f085c00804801e40c00700a610400d0008280704142585000c1d24101c0d40c3c17807034100c100b07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 889166276 1250 889165026 889165037
    0x301060e0a0e01021201030611090901090209040f020f07030302130e0c04080d09031703040c0905010f08120c07210c090c02010e07050105030619120b070f090e0408030414010c 77
    0x408091a030202d50354900011050390040011010244003080e003c1c0c152600f0007070008041130300c1034650721a4032031446c00a4000e81307480300001c0c0c00c1c040356000c1c3c07a14020580c2c003800b40103191403001d01248900c8804502102c403e00c0100e010034402d60182001c0f5201940c1702010325110301039903204000882c1c10314140f00380050248003100083c8400c008814560070001111420360741c6107008504491141a034030840800000d041c0000c0e100404020018030800700b05658441e60300324151011801000810b00c00c0501009042e00b000341100e48130000100904503032402c0800d2194909040c440030260f42c41a00202400b04109241c0c400080201c220006034002c00200003a02303440b2450440c120b190040c6c4001c1003944d030048126640700070220f8000b0004881c2d51450b4100c26400e8000300e21383d441481c2b504003004141d00009000c0c80300ca48402021280590b4104c03540b52060003600d030500190b80215000510b040060740e0050700c2a11070500e4041080401421680e8294083d40002c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 889167526 1250 889166276 889166281
    0x309060b0a0915080c0a0603050c120108010f060803030f0c03191a0a151211131202091807030f020d060c08060109081501170319090509100305060a0504020f0301060e 73
    0x1091007048001060024081c0980174008400113004003018440e800516845100248500c103c0c0390841e089000c80354110000d03542c4610780f5034001c10003c0d0b8031180c1d251901e6008a44400000180d030b00c1520103020340c41032641c440c0007812a41d0001352250350700b05c840c0607010200705c3d201d00070317507a200241881a01443c0d2603001000503000315035102030b0b80d600034102d1500d000369020342c203c03181c81c10045003c01c03800d42c1010055601e100d00c032266141d0a50400303010074902d111420884c1541d000b1110148035840d010301c400050a995203003110298009582000001c40c01198a490340f800240b00804c3d420300c83d00c3e400144c41c24182d0600c00030381a1010407140e581c01001481c080c000f800000d0040c5507060a00580005042c041c1103c40b40042890040c03400742000ac4549401040c000503020a001c80e001902100d000d010710383c415003440d000a1842c0550491500c00c40b42c010f4003c5c0001e44410b00c80c3c030020b01010b4002e030b0308081003070f92140342502c0900412004246000e208895803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 889168776 1250 889167526 889167551
    0x90a020904061203020a121407060e2521060e0a030201050708090a03110c06070c060e1e010e0d14100b03010203090c1923011106010509070309060b0a09 67
    0x1590b80381c20249640c0c502030500320100c1d80c006110001039900000703011842d00002026540595180300e07100703d0b25000030b951004c0021705e401100c01d0164031011100706062041c02c504412800700b542007602c0041c2d0b0b43c104900d080250300b03440b011141140109102c151521a14203440e8610944941c0745d0203200c041c8101a070910540f40e0000ca00d241240403400c0c0108a180c40d01e140f0304014003002040005200301d9401401100c44d004c0b0010440c5907590703410b2500d0454024548140c001013845004424a80d0511341483c0140d00d14864410741121003010041da82c041360018250303045101600c4034000185001e40c807101d800303a21002403c803400f40d0b0b0b01030030036542239004450099005209221298100040304102a40704503010b11204a00b100801d51890032540859613034060300c01060aa509214645050100700ba80d0f05500104003010b138a6661a0a2150b186c01c48003282c0000c4480e4030a0b0721006446210382c1000c210390701c80c040002c11240c0c580e0441d2480d01c0e565034111880 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 889170026 1250 889168776 889168781
    0x3030c0e040c09051012090501090209181e0a0212010605190803040504020a020a1a1801140601030209010e1302121e010b0310082b110c0d060902090a020904 69
    0x841045078180580c03a280d1600502d9007400344100c0d4000d10180385441646030048010484480d5001030400411055042090182200310000c1c0c1c0202060400300d0341070000c252501c0c08038080e01c0c00409080c01d5541a2a108007525140e124039030146c00100e90043e644c483e04009103410b4040081040da003400f0800a445420700721030b0307010003a540c0d010860744e4804029101240d000b2180161140d50010041c0c1c2048400c0340c00400700000b0000388541d044420305424081c904824261001281c240c21040c00c82d440025184030340b0203810000f64642d80b10780c0043c0389a42044c9490350790f40c136400010031340f07101c00416126111600426038400c1c07658164441d56028800424049082c1c00f800c06422540303c042c024906001c500200051884e888044841c0081060400305c460000c12900380c01e22a08010305091025003103500788070122486855007880180307216015040b40c20542c4100804d000b0083c904584132916850604090380e0340d10b4586100700360400002da620720600c0d0400c0b04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 889171276 1250 889170026 889170047
    0x30e070807051302070204110d090507060f050315190e0906070201020f0304120507020a0605090102331f0e0a06060207030b010620060a0c0315030803070f050f0703030c 74
    0x5598481c1500300219a030344444030b10701003101c220050f030b642014000308000d42001c1c020507001030300004d60f000c01d007603140c0c0c004904140154180d4681c2620f448088030300d8050740d4512000100c00f0b0010408610310b241c0c0c001070711b40b00100043d0a00180c0c0d0350004201d5104e510461280c2030709400c0141c0c4803000c1c440594050540d100071868240002e6080029000240015124907043c000303000525010301d04030b410f01a001403a450f85240e86450040036540a500c242d0300501400c1c0501e40002004800a12026403002002c020481c10311051400e03508014400c00004e18068003048461a60220f0714019042061074100c49181c40714003a400e840c44e03640b002c1e046602006040000c55912111039040d00c00c94502800ca9049078981070300e110050150a4940c0d0242c0024880319103034039408620f1407040e03600d05101c11f0002446d07c0055100354270001c0c0803486c0400014214920581c40e0f031046440c9030420a00b801c101d503845445a0b00714880403804039584154220015800c00b50449 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 889172526 1250 889171276 889171289
    0x90726060f0c030118110d09060b01031e02070204090b13030207080706050a1115070503100807080c100c050619240317070506240108150d02010c12030e07 68
    0x81e4a0030701070072568041c4014441c0c1c178a20b03d111986515102d00907017080380c19401c00c590b141d0302d030101c4e80380300b0005100c2c102c01240c2d901d18184d0304420039400ba0195406201006980c9003c4950b0701c20090069800340720101e0784540e40b4194100020032034403895000d504043c2c0c1c0d2000f42c1c9950300c0d0203407820095070044070329135001140030041258032204a64541d200ca01d801e150941c18001890301c0e00000604c2c0e00c0c00074031088104900940e01401039840f45030a0700d1a90a100e507140340c50368072006140280055074000c40d140d50224180720605101c103410358070b4885020401601c03501d080503000d4035024414000300c5100d00d4410350300d006141d249030402420006040c00840e20104107555444010001001c8803100700042c1000c50681d5078440e00141618480d04d00018000310b9407107210035414411268a045000e01d504c6a90340a1080b0442408841001440b01c100f00b40220360000c2207040002c107050f00000104c01c40101030304005507484c0458000ea540c42054203200440d040798 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 889173776 1250 889172526 889172551
    0x305090307210509041a10050a090b07020d02130917040608060d02031e0c21030304080f16080c1c090302240301061d060f030c0309072606 61
    0x3032001c59a5951011a0001c64540e6202c24125101c1c1c20b481d18001c4198841d40145001d0788049880d015620041074401c049400d10008200e004080d00c95002d96414070000910a90007880111072040c01414001c0c00203211516102c100e6001903000e090241d46042215140d150701002c03c10b11903860087e000001b811581802d051040003401c2c0c2a008004a2217280341c000390405541b010301c440c06080301c0240e543c11040700950070f4035a07141d20240c5418000c12100305002d2203d00e040303c18450440141d006549107444549a845040e00107000e02c0301c0a103010070183c40d0840d904226201424840c05280307440e00a0000c4050500030890743c58603c10342c402d84000042944500080700380d0380d0481c0c07030756007032820701c0404a001d032020022034075000c000000205025401542c041210701d001c4200c04521001c0d0410f101c3c0340d02070440f0000409000b480465008090200550b5100f000d0408886415130307995a04902c1c4200c0d110100c00d003070250030f610740780040c048c0b020907404044007401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 889175026 1250 889173776 889173787
    0xb0f0d0905120a080106051c09021f021e120f0c010219090e0a060e0a020a02010213030f0506011e03061d0106030b0a0e010204081b013005130f03030c180e0703050903 73
    0x1d03820b03c800c2c00502c11a103540c8014100440d622f051010400145a07070b420006040070080183d501c420920100040c0160703070070106001d044c0000d451030506244541c0c070f802c007521110369002c5030708802c8800d0895502444610740e1400d028100f400e407110580d0b05c000c001e6182040b07466502401401c1390000030b00b046018086400b2404119401c020000401031781c0c2d070440d1000702c1c02070154207440c13450107071a03010003c14098408185200c141c081c00030740d01c2c66680c40c500c011600c2c00071031005403860720680040001c21407540c0311801203041c06250035034003482c0f1a111400c42c2c09a401c00c803038a185602c248043d00200b4402c054910080c1c0b8002c614240c20842c04541e1444001040341e03804049072096052a40b18248140215814020814030301403026030139030f4040004084420303000e00e000005181d18130740d031480d40c06070b5400154001088078a038900310090710610104000748030401d040780e06002c00742d00d03201e0010002c2030081e13030803820143d100030296040981a0703a00781c1e106120 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 889176276 1250 889175026 889175047
    0x303010e0a092a0905040819080123011101020c0105100f08031e04080303160e01030605180c0f0c0a060507081e060301090f1217010b0f0d0905120a08010605 69
    0x3258490012500418140c102699240410888076088130741e080d402d0030180810000103102400401903900390b0010ba20111510460f1103260911030071020544c05102142500075003280c5110904043c98051204414600c009003aa4019a80308115a41d14800c00c440c800309024036101a00c66141103611303283c500100382d1394a0003649800940000941d0f061801e0300c010a0484004140d40026251203203024501d03a2908940c400341000401d07150b0208005641c40ba01ca514150f4000500311145003040e90301846840e00010301b100300100080243d0340034420500060185050804001e0101540500c1e01c00d00b40c80c03000c0e00b88414001500305126503070030641c1d2400060042031010132041d03a40c1400103405000a600c0c040c2880356404aa1002e0006c045400d0b09102c0040c0c65480380714a07016964a0100307024401c0d038a1505040c40710105040400c00100b00344007078400003107134a0700e2649070703182000c0d101102c41c80c032a00005441483c294100d100c80d0300400e010f040c29805c150300043c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 889177526 1250 889176276 889176293
    0x1103061014040e01021e0304150203060d0f030c050f0d02240402060f0405040525021b010c060b060d0c0906020a02030a030f020a1505060f0f0609040506130e0303010e0a09 75
    0x11000307120b6503c440c26082c00b09000d6064a0040380b000c5109070325480c07010f410000c0d9a000303071800e0381c25820141400950b00058001c982c01070002801001c01c0e004072340c41d102e011419000c402ca0421415128040c0480c200b00300d00c2c0515481c00c4d0142c0126205044060325241d80c1b00c0d4040c10011701807800d0391013000c04403540d60740030f90155203040d0b0310b80800441c21018442e580001d540f251509052046004881904c0f402519039038408074611010500705a0b60b52803203082460f540c0c212140100c145521488040000750f2141c40c0100b0045020300008000ba002121200200c5940d98180d5000719882400d400044c003c03400a804160310396000300340c07100780c01d100180c140100030544880c0188204581c041c11600300071081c0c10b02d040092030341d0141500f81c608038454070104034014440e1500c132000208011300144081d2428030080244405003000034a0940d0011016190031100885070140b00144080d030805140d80350b050520000304001c014050300c01242c42c180302c82d00088c1030310 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 889178776 1250 889177526 889177559
    0x203060610050408070801020301180e0c010e040603380103080f0304170a09060801091415030f100507200d030b0406050a030b040c0b130306020f0f040311030610 71
    0xe4072011804402000300b541c0034821540010303054490480001a20701c0194082c5068030000c416483c20188081321103000d568000301c00d18815005040240e10303940c000c0314001c0080304050000706400d0340e282c8412440c4140c0401064500f41da4500c819402e1071000310b121900c2c0c3c5030326100074071075055841d40ea40e035005d44002c0e11040e080c000082814808081c0801c0700c0031040c00a059075a00c14080020110045445200d0110b10300c0c1e80045010b80e153b014400000c4c0f503426106205541c2c1c1d4440307040d2101d140081640500541d28a80100d850900c14843c07032055107880410141050b03800240440c031000d1303204a40310000c42c582e400d10140440c3c400001c0109290100700c041e40303000040c00811a550200707911450500740001040b038400c200500c90b90041c1b610101c0507941343c40d0402d661041c1c03050030740d0f00c04044400340300049065000c0e180065a0320640303420301490900401541d0300c0b5420a8600065590002c03040381303401c02856900c5000856402c2400d0320302201a008a11013 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 889180026 1250 889178776 889178779
    0x50a151706010201090209090c090a02030106020c01140403051e0d02030f0f0318071d150102030405102c03010e39031501081207020105030402101b0503090117010302030606 76
    0x344400328803160301c01d41104203a5034001f08402d1240c00c162011603038929440107141e014170304034000141d07001d246100b500e048a10740d40282c00703042c3d00c00004440c0104030340100c9165520a02000c80401c00400c9988000420107040f201c00816083d541854000c114802000319441000095500c412083c1554807500c0c070042c3e850b403a51a040305801d4040086140c0303001a20842c000003d50301101c0081c8a14981010f18540060b2138038802e1014103408011164050b900401c010016814010110800d800710b920b0704c1034101d00f94000c24070720501e40071100001100f55059048d040d150a106e50305d0503080c003030020440d0303041944840700b0136056603441201030110003c0768040341008012110b140d18006082e205044140e0445018140c02030040525a00c161072200c400e41081004580105070141c50741070466840317a003084041d00425401c2400c02c00c900503940c038900c1c090300755002d0151080d0003640e100c19001000600b44098030002080c2c594841c8010005a1804210b1070b0304900c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 889181276 1250 889180026 889180067
    0x2702011b050c09041217011d18030c03090906042901051608030403030c020613230f060601020c0d11090915070801030b06100f080a0609020a0504050a15 67
    0x40c24101103003404044062140c1110311403041100300100e01910001c103200c1030312038244180300765441c0c0f203c08009000c0d00701c0d03d0803645840070001c6010315000354020350014071041c50040300d21200d41141c214203071000e101d901c04200d1400d18584405561b030700035000d990402c001e12030803603e04041c1d00c101c01940c118400301886028a40d00c1b40b42224034031280b11081c40561080c40c039041955601c1190300380d00180c540900e06040c544007241d101c0c007915840c40c0c40c59680f0a50b441d8041c001500001e9002e020454101c1d2000c0c0c0001408025581e0400c130001e0b280074a88400068203160b00c03121401c0c440d1106020300800540041465003820a0a641c900030342d550300c282451400e81000e020000f640c01410800852591000405d41624414070814200e500c0c7c02040c0001c1440c140d4490700400c1c18100000400b074490901d465002003440000700c0c96590380c406603805c0f60b10402441c07001800000d014000303410280c0f031403402056204498145280c80031402403910380200c402181440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 889182526 1250 889181276 889181327
    0x112090203010e01090c050a0b0901020a111807050304111002071403120f0309010608030f04051903020a06090503160f061d0307090c0e0f1e0a031203270201 69
    0x440940c00740c034420f01200d0080200c4045030410350844122840750754466002810080380028401c8180c411045041c0c0060405040540ea00407402c03183c80003d6800040f0881c0b0040d042c0b6000c1084c0f030040c040d985410f076483c00c0500b0000c405e40c5131049050300841801040580e416400203041c8105c5500f006000c0c0f080200c1c0e8006424100110b00e024221140070600000300e44050b4000c43c06250540000c01c01c03503540343c00680e02d03030103840302060840030b0034001001142050080d107048612b01c94134202c2c50311380b00e03400035054041c0c1d80c0001b40014808107040c40603040c2000510010b201090303d042c100c92405404002e5404140903d038100511207261000c0445a03025142c9551002000d450501c0c0d03c520030741004141c00c004802c0003d2031042d120449040c00314100b0a07045025056180301130b80c1c549884840740301c041c00d083d00040b6029000001c1507034041c401d42d9000d03040c2c0d000326140707201c459565410b903511001c0040c45144185e5540050f84c10641c0c400c01c400c8062422003610 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 889183776 1250 889182526 889182529
    0x6100504092408010618090c031118070306081603020d06020c0a120315140306071d0402160c05060c210d0e06040c080102070314030c4501120902 64
    0x1601c2c00c03000c030b402058100c0350220f5498010341180c0d042e50341300025001320711200414070080e540281000b400e000c01c8040b040c00400d1407054008010b041c041d002466003410904a5412114100d5104000903620202880824001c0c04003500c0043e08030510508581107400142d00c040c0c1024004001c0381e400507801d82c40300024072804c09916002603484450020710700000d405032200b0841c0c0900042d090101007402e0004485983d041040a401029260f40344c000c00e450074984c52015039140c407500000c4020031340c0c642c0010f140c0e41c041012410782a810324a00440030302c4040d0030030fa1145c2c00501082d5020180020360740841259002d40a00c203030b164414580143c032517203140148090511915001c04040000d1700d07130089100c0c40f0307035075515596800c0441c03c0b0f0265400003000900510711036458400d2110145400010076401a0314200441000361f5a00754a100c0d030900d10000800018464410700151142011b02d0050804903000b0400009045040d0b2800001c3d8065a41c07134442d056 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 889185026 1250 889183776 889183811
    0x3030306061b030d020c3903100e011b0228030e090c1b1204030201030209040f2c0105070e01050a1e0309050c0301060803030601080a020d0203070806090610050409 72
    0x3485860ba050341d07a03400d0f600e20f9010103503102c0301e407040d05032041000048041e2070100040c0800c4580724406d000000700c0d040800016003a0044a40e41440781801201400c48903221381200010703448000a60305003a03103002400812000700e0316095400140d020b280d5860604510551048500051894220b0701d00d0299451b14082c07491640007440d442c02c001071110303a4002070115180380144002c6d4200c50114103a9251244c254643c4003002c03c2c0001c000550094000c1c2414100090022030b502e0120807072601298141740c8810001c0d55100003200c0c0c2400c610880c4c2807101300c00c1c0000d000c0e615183d0805814011070007170680c1084030016000786a103208404110401d803590071308902d00010079000402400b0890b1041d591800b0305159135009203030520440003103940c198081c5085507612030041d02c810350001e0015501c04d808002c00440600c0e0761004500ca00c0d4a030321030f40407a0070320030140044280010590303401140000c8915040c141c0060640e0b08503040c0d180089900e900b2081415078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 889186276 1250 889185026 889185067
    0x10081f0b031e062e0203040504090b0714070803192307111c0f020708060c03010f1211120102040e01080f0f03130b07060603120309020f010302090303030606 69
    0x1001c4180068103a8074a0108000c0086210107012500e0b26010040b00c0188220054420040d4400381d80c4101140d1070080b10b1218940140d0341400d64a0f00030509841134428105d0302c0c480484200000340ba08004050056400880c05506281d8140e80380c005a00c0058007404501d5200940f1100421250b0050100c041007092200c00311027120311074540c5140e09854500100d006484909510a000a003000644401c1000041e004510780c00c180c450104030b01c140021070103901c0b0046901101003148034003c0113084003866580d8540510020b0b08400342d00481012009406c080c00403c2640c085290b090000f00d0703580c41c0a8803104800c034024852540142544100300c80009500c3e68045052a0300100c18000c0e0303402e00b108101c1003a103038462035801400d240b25560303050280044c2c420140c800c0f584a6080016881d48a80300c10880300042d2508000098842012504501344040d05120740142070900b0741c1040400c2001948a0000a160a0240034040b4405029001c085950304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 889187526 1250 889186276 889186289
    0xe06010b04090b0d290c1303111212040f1403060708060f03101a0103020c0a140a14100f0c172203170f010609050d03171003060b10081f 60
    0xe000c640c0d080310340c0039030100c0002ca014034144018002581d2101180072100342d42d2850004074034440c25a500d011089d0700072408240c0100c0524481548400100140380302e0810103800e00740c0f02d920f44904d04800c0000b54110a00c4442c0d030a5084a60392000510b640e009451400c0100c59541c2d28404209120b811001140d454407861007060f21465280c1e1100c0042002181c00003050309000c8019000d9101d100490040340d4060300e40f40300410140308a45610085110654482d60250b4440740340d002d0128030b211203260851642656003203600e02ca03410b41189400c200f0311010705d480c08068038003103d6030020700203240d2450024940365040c0034103d1a01c44401c1405020b50304c0e50900030030107100415150034002e0408003140640034102d00c898100d80d0329540d03d442050811003030080740a82c0f41e03411018070507068045400318254460603841404541c1e400031490f86142840401d49160b8455140034040044c6401b804581c02407040e41d00504503d81c407002d203010345120301850540e551044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 889188776 1250 889187526 889187543
    0x3040e0a3809060d020604030803070e0d2312091543200d06050708091203010f03030e01110703080915031302040510050a0314010e06010b04090b0d 65
    0x26030920840e5819142400002d0b00d041d040395030351509020b41076204440c06940b1100030b1000b000018000c1c40110781c40030043c64900c141640c808042001e6035416072044500030464910555400010111500c0c44c3d44005e000741003000c20b5440d9071030760b0322039048018020b038a035a8101e1aa8100007088441a000300d01501c034542400c0380c202000c40e2000d40f07141c5161884540b036840000e02d610600844641c200e80c1e49107810f5800c0320003841200b286000c86802440c100c2680000c5140344c070429110f81601c2e21080c01c07c1c034181540c1030070715a410848070345540b01403006000f00500b480c010002d0343da150074461200700d4403400580f024a140d0000c0395291042c0b000110801000c81e020f0006080c0075078090400075600d505c0080c41d07010440e4065050b0890384014809860a40c10854002001c3c2400604a640764404242d070b000c0b407a00203440c0f90b155400d0070747c00108244180422400200003a082550400143d4446481640b04e031089058681460b42065034179032401200d80340d44256203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 889190026 1250 889188776 889188851
    0x1b080a050c0f030a1505070c020d0302060108010f020a021209060c060c09010306060e0108060f21011505040b0d030809070506160c0608134805010203040e0a 69
    0xc80e955009066116020b03603803461034603446050025072074503011361010030003200041c1008040001c0c04001c000c0010046518001800b685520a00e45031513400f990192031a9030504680300e00303565484140780101441080780056041d07000c1080c03113045814402c0c40f5600c001d4600021580c1c000c800d903200b0715010703007014004608990710013046d040c1e0080e20184101680ea11080e81c2c14405860110701041060000036400d290003034440a0940001704080804074406445810791209010700d058960340d1580901042c0d0468204180100000c540900c124500c1c04081020500c0c4044020284860100402c0441d0411300454002d231401400c5075031118071040d40003680326001c40049d01c40218640340420020302c507001a505c00c00100071010b4000001e5a508040420340c03c0660310310000c07141e9900481c0800c4888240500000022003110140d000600d00c00d90bc0c459110b0b40c150350081104200f000d060000c141e5220f19010400103191082200d540f21100040e030703500d09140070440a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 889191276 1250 889190026 889190033
    0xa08301204150c091724060a03080a0306030204060510052209092307060e06090607050111031b0405030a0206071b06110f07050303160507090e0c01080f0709031b080a 73
    0xa4600460b883d40c49510381c09000c080e01075448183c0c1000c4000c1002c8000082801c1c503a201c01c0e120b80101000e0040448c1d142e0320b40b40d078541d58220700c440e0b1000030b4a41d0420815840c040c000d07400030b00401c48030829801610302000c2c10310302c82c1000041d13142606002ca5864548951a2000240300141080c44101810300d004140c9003000c5001d6104034407013081d202c034803050000e901da041d80c4143d283c0302c460f01984010410703d81c010701c800301c0d4040800c04c14000001d200b80200460103a100c0955600c909010661501440181102403418403051204012550700010303940359890b0181c030340d07a81d078040380d090400541120401d030b404101030b03030000010620350203004685d030b00c200c4000b50382807a01c62145994403016540b00b5107070306074028005590300c0c1c40074100050702140b040044540303030b590b111401d2054800008510340d1503081400c200c452944c200b080e155000504100050b40c62401d80c0014119040501001e40300c0e40390000800712404201c144a40908031503000c440c0701298524 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 889192526 1250 889191276 889191287
    0x1030e10151212170f0c031b0d06090e0a0f3f02070501020a0c0e070215070e0a0f031a090c1c200a061d0a08301204150c 53
    0x20403810020381c81404113004088801c0076030b80604140304c0034050030b03140e003000c0c22425000500030420340c0000c0440c0380790354481e0f0380040000446050002ca204e074940480081120412a0741c04450b4100c030210a0014240c0060164200d506c1811580704c00c00104039000d54002891300191a001c82c1002c0c5442c00348410035030564850baa9085800b600d880b00c00481c3c4400103045d00400c40d034143c41060003010030038480c45900406034811550305c0072a8840381c1284004c2134800c1000f1030300d440400001410802c68110141a044040700d684a2440d954460648051040351039801e10940100d60784010910542d50030500c01020b1481041c40d105010840c4404d4060445100440c40e43c100c80301e4010408002c09400d0080004802e1454081c041d101d400f00400207903602d0321000c444101941e130341d00e0381c900070304400f10040c011440842100606181054404900c2c08040c01050b81c000030410211344800c1c11040c002c40392382e03c440c0b50115844285c9a032103801113040030070703110010303a211 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 889193776 1250 889192526 889192553
    0x5120a120c021f0605030712060b0319120f0e01120f0c1701090c1707030e03131d0c1804020f03090307030f1d10110d02060604060501030e101512 64
    0x9501c2d01e50040f02000c82641210003a104840e05508242400c100280c094014000e0760383c014070000c5081050f800001e802c0070b0700050307050141f041090005090103080098038040a1140c1030106c0d6184802d0780c0076019510415210f81041604428100005c1c801c0d0404c10b040480c280c81445540d0642034050580c0740caa501e011308200c030190001076003202d18020350b42022126101c2d00c4140031421610162071100514800030f05481d004403901d0b40c0d60810040401070110031840348600d080400b6081c0c20403a928401c03014060322000e01c821a0015003c0310030f201520004040c81008a401103000303409007200050940501008210095401100804480344a5510700003120724851042d119044020803035150264402c200180c036003010084441103880d2410003980400c9483e0041c0d07e8030241000301c10043e0000000d0081c541004d0080c0005050242001c1c80b8983d0486020b594a0310b285004079102c42c1c4a0103004d00000d0780d0703442d14000d408070418200c071040003030038000080e8004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 889195026 1250 889193776 889193803
    0x30a1b030e010b04050c090103090516180c1718070506040b0409060506131e0e040606030302071d34091404050606070210050d02040f080d03050405120a120c02 70
    0xc1680e003503c50314080c41050720510000c11500d0030110000c0045005240da01000c60721445200c1c0c041d90340c0c9d141300803120028510001c40b100c0d6269101d82c80070950b03640c1c20800d4144004285100004400c85020741d5003d03100d8090a45044001d50209140480c2c039805035070007260015010400d6601240100262005520123025265541c801d01030203100316140118080145482404005d0301d000c40354103e1007814503402211a101c403540c03001204140e41c2150019a0384104004068060220100514500344d105620f08550303c452050070174010414043d640b03482254048003601d050300300c0e0b40c08441c0c2e840c0c0744081c80c00803005090202c0300d008502c000d9012002c900020b01d02070240741e00c5400043d085c5400c0162560a10601081480b644401e1020034841c080d02c1d01c0c1944068001090f11021081c0c2140c50700c11b0040c1083d10021880701014209010000400c8000540c10405205954000d59074508101e049645815500d0085003860070402506036880c2c0c0003440105001d031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 889196276 1250 889195026 889195031
    0x3190c05010614060706180c0603090b09010c0c030c1a0403080109050903180f0406181d0313052206030308070806010c020a0522020703030c0215100b030a1b030e01 72
    0x8454143c00506120b000756158084410001000041c88941165503c14003002c842ca0740c1001540d2110005001d580004000030743e01c0c4680c4040c031080c680c0850300b124014000b04494000340303100400f070a070000000790601c4019100f0f4802c001a044105030b18400080007900c01d03042074903000b0040c80003807091050103810a004558000804130441d6485440004c01008400004003407040d40720b46140415441503540a00180214036204103510504584000040b200d1807a00721100b5402e030942e021905503c248070380d81103104110520400d071001112005440300318208644628100080301201c290b0404000004240d004a80217011312000d848050150b5982c00c011103140c260500c010358849400f143c10482401c1c001142c8883c64051800c0070a1804400010010b9900c103507000c60002c1c0da1005d1404000f1347810b010071050b189001d0308505045c105031a1890700b403045402a800d41c0b0f800000032450b81049640b11000d145802402c1c00072210040d940580100f00c10249403610f0350 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 889197526 1250 889196276 889196279
    0x103080c0d0f080112110d0516230402031b0c010516050307360b070501050f01081f0b27090703151d030c0706031802030d080903190c050106 62
    0x10300812810030035518596400c1844da1824001184800c407940301600d2840c4004260f00c066200c60780c00c454002d004200408035440104510081c41119030300060207421182c0c910260468030200841d10b034103017298056107940718840440c1d000c9866440410340000c00207104040c080045d0070051044e1a009202554a1024141074035140300032102c8400152015005101000c0c581803040311080c0c685c014a00101900070555688554540246101440100e1403804112090250307951244400e480035106501d0096515a61507498400134a00d1a1240307940c80c00d010756500006502c030009040001c0c03c00c1d42039001180c1488150049005000382001600351500084c4000440f9840f0f0864084928004803840003001c5404403400b240c180c511036280a0b4034100080d00f52540b14001170481240340c000040c040b5494510700c51040b203001042c00700541c0d404640c040790881c0780d0400c100707980c0d0303501c04080c02e502c03a89544480300e10112040c088119070104640360643d120390020010113 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 889198776 1250 889197526 889197553
    0x1050f070e09071103070b15010309030f03020906070b01030b070e0603070c060e1002040305030a02160e010324181401050609070c030512010e04060c1107140307050303030103080c 79
    0x418080300c14401003020a2400300290800c229515840002d0785480c0c04104596890030b03081d90303c1200241c0c2c50101d2070044c04103281c0c83c01c0c6649180d40b800d00307080140062580c2c000c3c05404844260005040d070120300c1d0340c6562200801c440d10182c0c452005921582c4a10700b200b4044000e032045400181c803121282d80500300300d0121382c0a081191107882138200305640d80400f92403c4460305800b070140503803803413007225180085d101030f44c420006141c42e10f002c5100246840c0b08201c80c0c40680c03090040800907142d03100d05650560f60811404480891805170400c075000030b540c101d21440d803914290080d501c0012207003a202c2d03840b4403a0010103d0301c200704e06081e10000e4602580c4080c0d40e001154519029504410b00d03203109040071030a00320924940d01d032a0f8001d81c40814428040c2d4104801c1111130305c15254500e859091a8a214107095241c41d070b20381e01c43c080c03030403044c5c5200c0c0b0b20415560304100b0b510041c072004040f03903543c1d82c40e481c000005801110719044140304050502460 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 889200026 1250 889198776 889198801
    0x1103010f0602010f270614070e09071e05030901020705071413060f141906020a110907020d05030c2205010e15090f2805010206100810020a0329030105 66
    0x2000145e01c00030303956130004601d03903080301c120040c2112400e9032006511504a11603500700c0c480e10054840d221156000700034083d580b00c0003400030041026584502186200d800410900256140350550b180c0d80c401c1c641500902c02e03a50041d10301d2140c030703d0015840c46071050003203c0001c20f548508940304215008030960302d66009503800c0c0482c0c08018044110301201c040540c000041108200c01c0300c00c0d500b188800c5507504200c0050b0400d4aa0505100505205402d02d0344140d074150442d03e04000029201e80c186601e00c01080400808100850030203400d5600302040042c05030201800c0c541c1c3c03203441038458802c1a01055003400340c0e10803032a040f46d288210408810005181c080c001080000c1c08003142c1c62190300002c07011407551f41600480101c144010300c0d068a04840d4280400a45003e40051500f00700360080744050104803404140014406c200e00ea0140e101d2100e80ca050b070103003190b0601036608002d9000821070001c03498024800074403003a0020001d035114401c4035000d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 889201276 1250 889200026 889200041
    0x1701270c03080a030204051801050a0608090604020d020f0406090b090106051303060906110406020109230705120f0322050409080702330a0806030606011e02011103010f0602010f 78
    0x180d10031103441000460121001440300405070302d00145040c0d00d60000400b03c0743c0b0502203c0a07140b208006200509202070f008002d4102801e001040d49800d004440d41c410f0010402401488482c1c0c4c16021520343d9410120b100800030418000b00f901c0e80c0300e020003014009601440340900900010341c1ca40250110740300804002a40c00c00717582942c07a40d0028090414080740c4241d40c170790030b408200c84014090000b6240da40e0010a802e116400c0c1003005030000d0509690702090301e80320490010b03001401908452003910b4081c01b454140c1501400c040b48003410050780d00001070108403582414491101310402c5080100d010754580052000312a000000100070100810441016103170552484100420048112442c3c2c11020000100c90700e0000d0404128080480c2c1d404400c0c3c0c110000c01c0d8090f105500520103450081d0001701440c2e000d1020900d445111742040e0700c100c0c800c0d001908401e46076070390b240d56543d40f41002100071040c0d22401005520308001226901c032140520305 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 889202526 1250 889201276 889201283
    0xc070b130b0a050702030d052106061e0904180209010801140c180307030c05151306051c15031709030d0e0402132402070803030708040c170127 63
    0x30344003410004400601d500429241c0d05014040c004480140c0d4100504070364001c01e59219910740d401c20349044460807a44081080450b402d1080154648400c003c0d112444004111100b2803094803c5c00c45a9100b5094600e41003070a01102c8403141045080c121a241d1090718201e215aa076113000c6822501d80c092080c0c802c420980209003035150580c09000d8070a01c0310a100e16281507100001d26158141d401140d10144110003044940703072100641d03411842c84240f071860201c8010f2350850402c3c42d40030700701c184480803901c1c00e1003603d500212005500072040401c24807055541d034070006062031008a401c0204075401034a11094801511804100640201401c6401c8802910603241c2180d203181c00035801c0c80216150355000d9100402040c0c0c000b54001400201760284000030140502d0006651004070100f03c1c80c41e00104980d84036402e80341454160300d03149014289110254801c0300c145142c03551031452210b044d4442c48603035410701d041c00c14100c5182100060440b817100d024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 889203776 1250 889202526 889202557
    0x12081302040b0f100305160c02090a0f060b0a0201022203050a0b04061b030605040606020309010f030902031504030e180c0901180b031303030605030a241d01020c070b 73
    0x240040c00d060700b08410407100240302800050314400402d040c0084030b042200041d49540c01c1c844034207806980031400c58464600706100b54a543c000c20400c08001d00305400340e958030401094019141d62001000c0d0401001450707483c0485203009010390000c08410701c0182d41a03850540404a007000d18040700c2e402000350031700720710710f4554140ba020014070580700c20361560440150400c0301e008060429480c1e441c0041c860b401c20091200710707a12500b01e00c0965004010120081c0e82107501d60f203c030900713031602043d00001c44c800300781041000b200c12014058174005200425820461905002074103803005189100d03010050f0030302200c284d0307644122407010401181d06510805442840d0008085d200c6ea0942da10207051515501c21201024031b040e00361003100402d035040c0203407001070100300e008011040c43c0e0f44030040b0441c0c1840ce022800100c03034030248122084c81d0018000044071002c0fa81c0303051640c03410103020b035120244048190280c644081064603660042e03990200406005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 889205026 1250 889203776 889203811
    0xf1209060c02180411060307020a0c0509040c0e0c090a06030203011e0321110a08090307080303090303190b04060e0a0c02010501030b061002150412080105271e0a0203041208 76
    0x60f0a04040043c005a405c1404142d81c05580d0310380c00e00440c0620000c2d801028503846605040c500942d50b5044244140511800c1c4804074600c0c040c9081a55565400507500b910740e84048442407103240c080603002480c0107000201c40360168040e5040302e15004a441d00001c030039906100d1860b1a0100500360b03c0102490310001d50a003190b603072001e107541095180f0f0064080c1c0d50b880c08007001401c96a0700390000f1410103900303051100f84000c0001070010b5055051040313845480c5e00005001800e400082d800045052301d4680000d0100c0102a00c104002512140c0248082c03c0c00c4a400450b00e0418011340380c2c042c41481901d0482c0d802248100481e1918002c010310320700c0c203c03600002c5100d074864240c1c6580d076482e00203008620072890065440e03a41c43c400740820605900cd41d01c80c07100c80ca00040c101a80c03420072100964028482c0400342e81c0c12003814001100301071031030b074190965010803e010700554011800b4502400000b05118440d08003201c4990041b924202c0002e541c451 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 889206276 1250 889205026 889205059
    0x603021303081c0f0c03112502060d020309010507031a280f120303150803030a1512060e01050901151701060504050408030a06080316031b0f1209060c02 67
    0xf0300301c044203800b0440c121180003000c000681d044500d200d08507a995420a03000c0319010300c0780c41c4003107980300c40940c10501c05182030010851113004c003074a06000c1c401c00c0e00855484100301d500b001c80c8075100710345074144004e5007402003000f100c03000046442c14208841007031210610200c0910002c02451b552030f03d840780804d44c0c48150800001c0030440d2000465089002c405d100c000d41a8805030110a00755400d0040c01e88950040c0b50440f540481014803200e43c010040343e500c030200c08008600d035078400c03140400c070022030342c428042c01400901c02c40030000960000c0da0410745250081c0081d4443c0403006089030303441001c1070f54005000c60104149502d610140c0d00307600403031b800054007035a180d0108040c0c4004860445218000204010100c900f9100b004040c000c400003c60a01995203071411900110f01c0d0050107000c0007010304207440c5120f1210300d5031980d01c03e40c100c520048034580042c001440d50a541c0c003044031620081a00c512a010800c1025001446228031501c2ca48 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 889207526 1250 889206276 889206293
    0x3021c050c1f090602071a13020f060715060b07051002040509070c060608011d061506090f0409050d0207080d050a02070e0408160b1006020102090a0e07021c050a03060603021303 78
    0x40c02140d002d510b82c007000700030404620142401c1c5001c0c4085640002c1080c000c202a40e8009280589000c1300d0360b070650240c0c4800b101c90000b0742c02980e456646840608200700f1244c0080042625142004c0c00030810f480c0e0f10019000c454800d0b4102c4030341d60240c4618400368016401036030b805c101d1800016603c45c1c030a059500c8c1c0d56000c0d0000058440d1201c4049007075814050038082c000341529190302e8081400c11142c1d620507540740640c0c4150f0100d1001071183d1041d56910b40c400c98414014540e10358580d480083c1ea01e900c04100c4a00040e20034019440700050301c54a40980110301050404501a100320380308801580c0c0070b00001800c0a648054010010708140c400803402c1c8003040b03001120003000c3e00764074026107210b0480e142025036240101d4a90300005e0840e401400341c1402a19010280d4040e641c4881501890742d889007822880c2040c1400c0501d100c2c900e0045000301c03580c2043c020a00c914880d42c3c00d0062a8540c032084d01644101051018110841c0008002142186 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 889208633 1107 889207526 889207573
    0x90509040b0a020c0106051806040605090103240b0907030b0901080a5c0105120f1909050c03071a12071b03021c050c 52
    0x2541d1101e0070710380060319200c2070039000705192405450039005074020f02400350407800f565040380100c1c04501c000341ea150340585d240540210b0b040c280040110b050320740205401e0358450100703140130441043c83c490b145000f9521510344055030f032101103440c01000c041d0ba01041082c0d540042103024581a4480c450581c4071545150005103001d01c9107180c2903d09051520042075000c2104801c1b6901c0300b901858045025880c15200039a84142d1044405028051b80802c3c0b0310700540b12407045c2406c6000c001c85100002d1505404140307030a40c8050740040c41139401341035184400944040c10805c0b40c0075008080780019900301003040c03d0003030140d01407598841000c8101c5480c2c038895110003280c0ca01d2908000344a1501820f00da0f00780b561048400c06510b401c50030001d4841d030344a00038415581043c42c01ca460039120314165035122085e00f000c2d011080300c1c80307030000020114 = true := by decide +kernel

theorem cover : BRFrame.Cov 889028776 889208633 := by
  have h0 := BRFrame.cov_init 889028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 889028776 ≤ n) (h2 : n < 889208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
