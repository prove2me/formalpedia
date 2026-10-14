-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1498
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:16:02.533783+00:00
-- url     : https://prove2.me/submissions/d7676297-220a-4034-b3de-0e5f55a5d00b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 269244604 ≤ n < 269424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 269245854 1250 269244604 269244607
    0xf120b060a030609230402101115190506010f12060b0c1c0201110d1509020706290f04020708040509070f030c030b01200a0b0a020403030e06030f07051b03030c 70
    0x40141d48a030703e01c5000044002c42d022144805c0e01e1a030410301800c064424100242a030280a1081e92070480343d840300d0058600e8040d000b00d4403a0747d071409072540d018800e00001d01450210307040c03003001d2140b403051b500c452080a28403c00e0711402c400f040f0040703045032502c4000c03811842d08001030500d0b0340c4590051241114007551395a644038903850030001c59041c00d082104508070300007a12042c00c0c00b100009680b90442400d1803c01005520082295001240000c04e0105641c0f110b0694107400490f4000c0c4440b001110584403004010036074032228041028086003443e03809024110b22401c074892415459000240c03d490086814900240750112581112541402031040c03203001c43c18184540145000080e040070b00222200c2d240c408400804a440c5070700304242010503070801420501818441c100d18007940c024042900820340700343c043c1e42c2c02d00b4060100ca00c03880d981140d40040c2d89648104070b41c04d2303011910340c0d03c00360f0b13103418031010450003800151302031304020030b40c2c030f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 269247104 1250 269245854 269245859
    0x10605030609150609040c05100c050613031b080406050f1303080405131107020d030c1a180604080409090f080406050405150702031b03160e01050a0e070f120b060a0306 74
    0x158043c1070060500380140320210070b020003d4000c0154100303843c01294403442d103524141c0115040e180d01d8101400300c2c8122814850b9810700c64840900031130083c1e4840441d550f082010b07054030003c01000034110715081004004043c840c501500c00701100542a518103ca00e0040484500003908180c985100002c5c00f0070103842c0401c540c000c030642d400030900c0301d0050315a0390b07041c078050040b019004182080d8448201071103520200c0783d10f98086d074042013580e003c856885500c0c02c00c0b80c112122080c19040c802d209000000c000780310702c0e1311603225483d282c101103041c8042e15040382c0c21200c825062501d54000f0740c0f01e030003074000752055546081e1a2071800c1c0c204a80c840d61518101c508010400c01c0c1400358902240030040d6025003410340c2c500003c0400441c0c40e1949000307070b5011400001002085a040c0081694121041299008000b54950b15103003003000c01501d00070701180f44400c0e550720050051303800c100d40011000e400035107a43c0190116100741d0140002c0c07400030340c0d0b0340000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 269248354 1250 269247104 269247133
    0xb04090614011119030e06030f090601120b1f1701150b0405030309100905030a06020c010b01021501120c030c090b01030606080603031204060e0106030f0c080a1211010605030609 78
    0x400a16001c240303092607802060b185015240c000440c006201103807104181002c0c1406242d0080145e2405441c2507a245400c01c540d001408058171400e0060203114000502400040c001000054110424000e03641b20b0035001840390000901c50300f07400f81103140c009504014170701c1c050f680e151000700100c0c68510103000c0060341202c1d40c0050161000c00d10003400140c07800000c1c0c2d000e02001740c031121080000c0c81e00c142c1d01c401080d80003a034140701d0140700100f0050039401801b000c801e0031000340449034400005a840b41c0e010b084224440454200410010681c0c08801c0412806449c012442c00d44907184c100100c2c009030007940e031007600c0303441c60380c020350b850300c1408005c200e1480e083c1d038035041c054002912441001c071807100c1c240c004000705080c810540e01442d00782a9510080103015942c0c600b6002c0d01d021110240d400130400140041d00a4001c104802c01e990b03c100103c4c101804100d00340c9125450b200d001d443c40d0342e40c40c001706075514100826805000060700900802c0c2c0401d41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 269249604 1250 269248354 269248379
    0xf01030234060c0914010c17031005041509050c030c0928030308070215162001091209090501050306040b04260d230703110c01060608041106120f060a0b040906 70
    0x701785040140384043c076000f0070500c01c0e405401c1c020886143d5602d03140c0c1300082614038201d8100c81d911525200780c0d00d60651540c00d42104440d00c3d068103004603914042400b0281c007046441c520780050412044a00307140c0000c410a580d2140100800b121000d2202ca100d811059002107010903681001c0c0103000d50104070401162103c400760720101d01d0400e00d00c3d03261507072000c110700602c480c881c1e45c0342c0d1904152a2b80142c40340010300800c07840c80745081034a0404d00920b143c401140d59103c020524040500a55040c0c8102500500d804d8071195918410200014030940b152812800b010f82c07503034444812480c0c920700061180743c40300c0c40a10158111043c44401040900080d0182e000c0100c5040210303074403901074200002c01444900d01c140c143d100380c2c690002c0c65440c0c084013041243e0800b4405002d140a0003420144c15200c1c0107210151040c50802c440041200001a03600500000c85540c065030242c4000103da80d100d400c03c00c00c1d0829000360156070b8440c5400e0041e494000c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 269250854 1250 269249604 269249639
    0x409050a090b0919260d0b040507111c030906050403020601030311011a091815010816120b18010f0b030105090105070f030e0721020f01030234060c09 66
    0x10080c10344c40407800183c40e0520a418001000c1c1c0d0201c025007582865041c0e1001a10550703120360a030f5400f0000f0f80c00c00141b00e003180b0036120b54a00b01c04501403610420901121101c00340c000d0400c5c06800803803600c0501c401c0d0b111401c050322a20208005049030243c0d80c041c42c400d400501c00e9504518020301190004082c0f264542c0c50000c403881e250325400395030504080c05440c01460b40c2c0324040c0c45c0340e000c56103401c54001c0e07200300e15400035070050888006049408040a562250340801e0441d50810170b280304000300729500b044507802044105003001e03044102c0510219061034a1b400041c2501c0d0035614081e041540c65040300081d00342030081030b03880494034000708040c0c0f8160002034192164501703c4c0007099a81c80881c3e18408003081900c02900d680f448991601d070101c4100141c860709420206d01901c61290b40b603420754040d00030baa403042074800d00f00c11408003090140f0078800c040c40e50803030b2001c02c0e1092403001c5900e510843c4610001c540d611901b42d030418224041000528 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 269252104 1250 269250854 269250871
    0x218150d1116060203090c09040c030c0905070504090c11010608100b06120103030c0602040e0c030601260604020c0709020301030c031202070509070507061b030c020d021b0103020702060409050a090b 87
    0x1c0041140d91440040c02c04005a4480f10041c1c0340c0e01c410311501d1802d0611450f09070001070440500080c400403014920880344a100c0e40040742d5103c20498046d0351044c0c44040c080303841440180018440e43e00314449040b40e41c9040da9080306112407041c251640c503801981c0e80d401501411400b82000e0080040080c0c0940d569071a2800c05240380401180511020f01000114020303030040ac0441d070102d0300204440160610a4140081868025071041d181140030404a079158032140b1a0034114a0002c0140484209180d9511041c40065440003020100d43d00440300041600303402c600c0a0b6020714010540241c0d914250710b8a2215445e243e51384c003040d035220050810990391042980750f4018010300c1c0c1a501c9d154545030003805421900c0494a44081c104501c021503a851f61100c1e1400c1070304d034219558481218402d0781c0755121515040c015054041c81161254002d4000b00704d49440508218541a41c0b16240000c07a0000ea0b804440d02d43c03952a03800c18415402d05040d00b10908 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 269253354 1250 269252104 269252107
    0x9062004030f020105030709030506040b01170d020a170d0204080a0c060503090613060902041a0a09200a1106090c15030c2703010e0c042d0218150d11 66
    0x75625185030450000030000d04000c00040080c1009100c1ca200e00001c503030200880e5224202841c10440c040d809000e91104800141d801c000c58000c00035aa6503080500d4000e810820b140d03440307081042881d540c0c0190812810003124501980302e1009000410521014141851940ca024413030006954031550801c2414414080c8a04001c10f6075500f0228001c08540354010510301075000e090883d00c003950040c0f405a005960b881e000c854540f07041001c94443c440315890340343c0c010403070f003031103101a20400e0036007141c2407404000401842c0c0170390b41d400d142250312414007416240c40c0f0100d55030680b44d0000340b107040d2542011a20074540c1042c41100314114034024150020030b0207032084a40300c2d0359140342c0380a0300100d80644a407203510702400030710a1841901ca80c56484904005042c002c0e4605000c50250340100060311218061021101c005112401c2160000e90000f18071300107c4004186441740310f942d4001c0b00c12080d40c54070a01d54459482001d07080842d0362000309104440320 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 269254604 1250 269253354 269253359
    0x810020c0303071101090b07081503030c0a1502130303020f0f03030f0403050d0f020f040f09090b0f040c0f0906060e030105070912080d0e010605030f010c0c030e0f0409062004 77
    0xd010095903840385592400002c01c80e0341d42c3d1124090120400050800ca2001c0140005a40d1200071035103d801c0c400212034140d42500c1c2450f540c0d201d10400c600c4640c00504160000034100c41d1904503542481d00f000d0f0600441440d140c10324817180c0e1080300960b001080701c01c07030810180010540f0180d0300c8051400c0d071400b4040d11074440070042005041003000581c1640b0000c44e40e1041c803d400c184541103484d8140384200013810350141c000d080b426590002e00140c2081903001e401c1c04254026035406094444504480328014064001c56001c40b8590b40400c411000c00a42c07802410001b001180f4131349006009040884e41c0302840c0d0007a41060200b0291a070400d11000803a00d02c0c1006903100d2038541402c10032030042842c404600c6082c001903940415054100f4000d88034220b00380c843c10350b19130031406d088448000301c0c0408141800303e0800401c1c00344218000f00c1c04003400da40f01804400c1c0024088600b80c11040f60415035401c1400381c81001420110701d59409881094903050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 269255854 1250 269254604 269254627
    0x5072d0512070c0215040501082707060801050414061503100909050105060a06020607300203131205120609070507060504030f021204050d1101140d02040e06040236060a09081002 78
    0xc0050a5201e1081b1a040703505070110b1043d00c0e01d20001d8ac00b41034502e0b594444200812000013803240b40c1c0716504020605000080d15a11070f0301545c802089441e602c41e08038200406600001c046144114110f030340000c10040ba40111040c8910950001501303103491010440c0d00356142d0003040840d4000001c1000d4070750452504182c0e45c101c100305400701681c00260101031070b020901403000707500100a001410060300b24689203a0301c502c0b5882c04185007844101c03082d024511404130602011804a0543d0400d246c0940d08a552403506d03e252240030f460300c3c0d054400545003200007500100301c803880240d060044211000e801d00100341750924100000b200020403050191071000400d9412038903a0140c0550110501c0c400010750300c0304500c01001c80203402070321940c40c1030301c94000000d4a80c9020b2007200c0a00c10141c032101840ca20089000f0002c900380e55130381c514800c208a4210041d903411010301090b251540d078154480c0d003840f0038141015001c003680400715005224452045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 269257104 1250 269255854 269255867
    0x604030302070b1810050408041a0c07090b0901060e0a0b03071e080c1b070e041a01050a180e12190314090a140c06030f070305072d0512070c0215040501 67
    0x1740c1281d00c04070f1161074500f80f48a0900c00c80d48125524a240035034113a07944a40009000400031120995029503134550f0601c00b600d19011b841d980c800700d110010700005000e90f21105591001900450000e5100d8030040130702d074000d030703112808540c49203c4a12607403400130f651030360242103191990712800c1200d0b441070640910040ea00da80c55900c2000b21101d00f04201440c010011181c1e20850b509003824445000c200d481d9420000b001c0c0c4c03800101d441c0c10124600021250040d40f00a03003012010703102d40040030004940300440c018071900301040b040349001f406103000351188400c4c00008041c8080c044680008880402500910800c00d40503800702d510f101403600072207010483c458041101e402d1164080405510010100074441e0000b4801103113880390b400c640327007004941c480c500283c1e1054a02c011001d00100d4540c0510503a8a4403288082d510030070b810614107140b20081c0d502221081143d6050024660004480552410404104440d07592401551515040c800003c0c0074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 269258354 1250 269257104 269257123
    0x1326070612091b0306051602011b03020f0903011104060906080105061615230c031015021e100b06181c021002010504050c1206011401050405030604030302070b18 71
    0xa440e42c1c1d030550414400340390b0040741400760010407424090b8036454290020a0103940386002043e80c014840911401449000040741c070f6a1195a1204200c04080f0040d5011060820b800c100034019202541c03402d001c0d82d20001c4800040c0c0341c0321410103130002c0480c02180c0c4898200400780d80108040d40b44c01d81124074224000c985690229054144000c101e10070810b60b1005500d00050708060003041480c0d00c000e4528101c141186460700710644c20346000a03110403508070404a0f04000c14a001c10510500141d0384c0150f8000352818164022011074801204242c2d40040312611700402c2c2174403a01c006000120b401c181001846031038401804040d5507080c0c064030012084551444480001c844001c0d402040c40d10000c01400000b80640415036046495106000468645140130300020036410362890040071140c5c41c05040c00007030200861100d041c09004c000110341500c1c18003403d40300d94083d8501583e00c1400e490442440072000b801410090f8640100448800020458221 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 269259604 1250 269258354 269258387
    0xa05150a030809040b060f07120f0e1014040e1602010e0d030506010c0b13060b0f010c0201030b0f1215070f050313021807020c1e09160513260706 64
    0xc660300140c0203e00100f21403420b66500c540007181c41034000d4120720080034007500c1271000005a4801e030809450302c1c1c0b05550078001103207000c10003040e5802c000a49888040e17027807401800c00d5140200d007030600d81c45030300b000131000200320030000d03800c46004403104c3d1210644000c01043c1c0003146225110780c144003403041015110000b040440e0304c03c01c2d02d40000e54001d880c0149604090344201c2030000ca41808a4410341040340f003000c40c2c45d00451044858606858902c1800300581c01100102540441030354407250400b6100f002d0303200e6040708901341c003610f001001e01010056820b204180300801840410201403030003481d0366404002e076500003480700c025014050052000441a0605851104100340910108804143d0001d44030103010810b590b40c0c4ca001c3c940fa01e104c07a075014024801d58001d4a1000800c81d00c0101c1d10b02404010f125240150508501c0c4102c1380c00d5280c145c0c010b0200800c00c03001c407841d80c0d00d00c0840200100d2103030000c102c00d40c50f001c000381500c0803542c100030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 269260854 1250 269259604 269259607
    0x306050a08070e150301050c040303023d0212040b04030221071104020d090b01050a0603051003020609060f04030c1809120302030601021603060501090e0d0203340b0a05150a0308 78
    0xb41004201131520031138100c018020f1050f403a0030900008a60011f1205500511a00709822944c001d03521068000180c5a03010000ca43c000c030055850b1004185040c440d0340e036081041034042e241200c0c0d000d00980c8a40d6000c43c0d41e00305070500a1800d215001044440c031090980d00c034098158800312104154044100c2d610007401303c00283c001c0c042e00007401e01c610f0030040c1642c01c000d644002181031320411595a4000340e1500c5007101102e008440050801f60b49800c2071016240c00d4024094244009240602c0c004542042d00c1c00d039040f80c0d004036602018401c0c1400400990b0403ea9540704540b1020042926907845040d04240c2d0301c502d840505034008049485a40309010902035a441480b2000400e070b03481ca80040201000d11460740c54030324000c0c01c0900c40c0d4001ca20a80d04400c181e000718102200f40e6139421503921140319100c1c800840034909112082620540c40300b1a0042030070304424a0640c0c450300c01c0d40c100400340318200a00c088801c050707565070515242039030307005075155 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 269262104 1250 269260854 269260861
    0x150405060d0813090f110706091b1502060105012c0f030d0905030c040e0703080904140106020d02060907051e0315010803042301050703050903100f09030306050a08070e 74
    0x110398030011040a0400800003500200500c15000c00b08219003031800104001442410170380300705c030504807450104500030030100004c100349821508a01d801030404d0210950703a00c03084000c3c448035a000d480260b1082800b844003a03018800c0310300400003070a00c6048030a090f12550f501540112400e0441e0001016040a03512120360701208107030040c04941000b440c1d104060b010200504c2a140300344074140ca0f404960810f8003405503010080350090480c5070440d0b58580803600880d02d107a0700103596120081c2d00f41d96aa91840c003e00c000d80207061952a080360003410000020030584203a030048004120382d44400e08110020f41c83c2400e0800080c01c0c0c440064100441c48803410014040d090001c910048040010b0040b5069001c001849031001221581580e28954003a030104605202500101c0e01a40081440356802001e4070042d9504010080031520b0241c22254030b40d0b90307503200d0710405415108940142c581211226039503440c183d60566209814040c400301c2c0b40301070703020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 269263354 1250 269262104 269262109
    0x206010f050d0b100504110904050105030703081905070606030f020301150b0301090e03090603010e070210051b030613051527070e030f0f0d0f21111c0603020f01020615040506 77
    0x8005840002c0c4241b29030742e40d02c01c04280e2500062219480384ac94000005030a19000502d00e040760385c000c00c918241a001c030070804d4035030360390814a01840000c000301030000d28184210006148150912426100745005044c215214080107901d545c0c3c2c2010148a496041006d403411140c000350301141e40c070006292142140030f008a030f00d80001c404400840e420020101940c85100c05030700301d8034500e03141e20034007054950075184011310102103940c0e41d031040542e0340290b5110f030025020114600e604000f904c12100225110705452a0300040c8668074540086d032000182c6a02c9500103100084801e0314514440c081c142d64140130201d01c144186d80c42c01e2001c09041d0780446d00343c070030b403100042d4801d86842403040720800143e85c1101040210f4000c400900b10083c4800e41c00081201d410700240080000c54402d09070040140034020000400541072402c00c1d81406022841600c0c602c14400840c014010340c50542d0001e500700109280040700b9402e95400840300410741e41c540001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 269264604 1250 269263354 269263381
    0x70218060d06090c0e0c070b0417041e210b0a091713150f0206070e01024306020604150f060b1c050c090108041a01150206010f050d0b 59
    0xd2140b410041444113100500c10f081003214104c2500d028a5038611400f00c240e0310a04d07000404041101010901045207200d4860a002c0c01d04410b51410382c0765010315003942d25401d008001001e5116050003030342100e41c1001350a1000714111007003c003c0796100040c00900419a2040d5039465a07544280024215201800f00e4034401e80d42e6603464400c081c00390101c185c010031035850420742440c1e4840303201da6400900d19255501520700c80e114042c00700c5003080d010009504610031100c200f0304084d01015030000014920a0b20307088691214286506109086403008480e0107158082100035000701d010341c0e010340c0c0702342e580c003549010825040007082202c071010703d00761a0550100c3c80741040310040142100d12034107040c00380000b51603001620412542c0c11500c400901050520707500a120480e002449203aa24600b0459102003943d120800d07071100018460411200703803115010722080303015001107080d510445007003202050045000d0310000784903900c40c4000503851000d114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 269265854 1250 269264604 269264629
    0x31f0204051504090b0d0c180f02040603090b010b031b03130804030c42030b04051303080c03010f0303050901110604030e0a051813140f2107021806 65
    0x42c0038002c141c00030032081c849500507024804c0040d142c5001c00d0b11314030300f000e0a0589542d2250207100140e0a008801d5170a02d61030804190064a0340328070012001680080c0010b08100c0c3c1c0c00003803101d050f0030605500c1d041a0b00001c2d90010030014000c03102541c080800c04d060600341555500e80b40c40110882026698201519001d0302250100c2040103501d401411140c4a217940c01c42c0c0e1040080c048041090340c00419100a4540002402c1c00302410b60340d402264542400034040c012074001c5001e842d0200e91851411050114000405030000001900400446007850442d0304040c2c0304402d00c2100d00004d418080007080d031620341ea1007002e040511082c1c00d02a1207541c1064070b401740c500c0e84401146849098890780103d8036003460f01c00a43c0300460b40740c83c4141603d551815201c1e140e5401400d036030039080e0015012041c00c007009a003c0040d00390000f80714200d49420b003c03100000c114688421003c0800030b0101581c0e031031021401580403040c182c1616110880084c02040c03034078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 269267104 1250 269265854 269265859
    0xc080408060705030726191107110306090f060402061612020f0c010c11091503030c0a020a060306120209071110020d060e010e1303050d1b020106080705031f020405 72
    0x10420040e20752010280d8007420241d10303400d09000b1601010000d410340d50000e005507950483c0001c10780002c201c07603141c080340b00c6803001888e00b14001583e0380e83d40c00fa0340c050b079104200a404c107070a82410400e090b48480c100c07001d031105100c0d00000301e0300c4200190029109280105011021200000c5034000d000c0e84200152a00031000002a4540600815211490241c503041d040c0039402221040c5040340d118034031000031119002000503c0202800b40c500000340326110301c80d075490400052a24207602c500030140c00515204110003031a04e03402217004c150900c80f040060150442c501b02e1707842d504440c120540c2c5e0b00c0340c0080b18000001203002d040d81c170030f41e6219164841280c1c010203850300642070074070409854103080783c4034440a01c154501c7c0c00001000810503203a80003e219010f1082ca4030358540813104542e4400d80c2c1141d03944000614010341a940f5843d02440340000600b85100038107049482d01000a890390a40b00c105031101602c00c50a0f5503010a541c111000f0b001c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 269268354 1250 269267104 269267113
    0x9100207031d0a060e04050a0204030c06051b1c08060328030215060604060c0510020403060b032b0e0103061205010e06090604050703140102090405040b0603120f0306010c080408 78
    0x1070400030000710150700040490708001003041d000d8100b00d0100d00035210141c440e102c0300303c81c0d0710a02000f0403004140080aaa090001000260180d08590000c00e869900e00303032294620002c0403031000d40849112080c5d0700100141c048003100580100001c07075181003010340c0707030b840001103400d00506105914800119588100740007003085610254607009030300321100d60003c3c229001074000260742c416800340b801c0c00100043c2e44504030304040d4a11640c1030710180d0343c210741c090040c0c0e0090342040f184691100c0381e0902d107041c10440c5141950510202c080800f07070000640c4220085880088108201a210881564006e0b00032000802c00b080780c1c501f1b00f0186003811402046640860001802440c0104024140c002841c078003403900040648081d034516919030040138074002c032071826550240900415642d6a20070144140c0c01460107140915110301054140100e4104803c401841446800d441270084020b0b254020000e090101c00c06516007480c8101c1d024503481140326108 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 269269604 1250 269268354 269268367
    0x30f030e0d020322051807020f1b040b18060f03010605030708030c06060a0e010902130503030a0306090b060a1e0912030e031b1f03061d06100c051203091002 69
    0x1030000041c85040701840d2100055504c81003a0144443c02d03124050f4819015151360b4140044d85000301d0304110180101d60f10f2030320751101e842c1005100000c0c0400c44c00001440d50086c2480d00a100d60b10000b11068040518400307120700c003400014240902030040540e1001080c1c80941c05103000d01002001c4411095440d142c9907074942c8401015012401100d010036041d0070900c1c1540183c0d04030f1042002507a0a10400d20000e4000421000c0c520060000000315034a0510040c80100c1c400d603804540e050400d030300310062f079800c0c2c0c0f103a43c0180300c108410464654080001150504d20a42800e04078800d000f0032a25110030303400c40c10001440e903075040101508007110a030030f48019000c4c1d400440c0c41c0e6408130014042c070310706a50800c0716003805641010090100042d02041801c0010305191034041c8901090102c0c1840c1907000c0d075000a000462404500100000e0a90714000c001c010981da0b407070b51660317403000469401d85400b002180524000b4030684040c2240c0c040210748906 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 269270854 1250 269269604 269269607
    0x150f020d090b04020a0e0c0304060906020403021f09080c030706110a0c0605180d020d0803040f0b090304080c0303030402060a0f0e190e132109050d060b011404080604030f030e0d 78
    0x21050380c041703100d404186000034841a1000410b84a07400710307002c3e1810b5546130385030300c0c01921000d042110023540c2003201000503035410b046040703246141e9a001c8402005a81c018151450359001000e03a540003088141e0140d900142c60b000342d80036031810b20201c02e03102041510b00303a80b05d071004101c03c0c1d481c8004030745a58804058081e24000825802c109003229003030002e4907021050103900311740c150080c440031400d200019a04148903500c80c031107010740d1381c540701c90800058a00c8049500700140030050030404100004030240304a000d0351460800ea800100144100e50541c41882002200020b465001d0105105e64910180007400287c8140c1c0045540080381d02805070703c2c000030400b00d041c002031020310a49150340070045480c066049502e81c0107030000342a08800f0090101c0d400305154907000000c2020501c0786034045501510200050510003d44010400d0b028003440304214202000814a81042c1c0509001e035100b107240108402a01c24916000c0c258803a409501461a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 269272104 1250 269270854 269270873
    0xe011101060e10120302101a030d020102090a0e1314100e0102071a1e10120605040b090d020a0602030c0f130905060f030c06090d14010b10030603150f020d09 69
    0x91030508030f9100c20f15100c2d1008003920711a081d0240c01030b07009030002446403085502c0000002d06d44018408000c043c0400a440c102105408000607500810760041278142001d6800251588000022140c6061001c6c1c00c485000fa04014080118003903001d10014401d000c0e040100c1c0c0d41107418030000700c1c000d403058081d500c0b9002c1201e26200502c000c026040c504082103000309002d9600004070684400001d001c0341c000380c01039101c440101c030000354955120500400c0d0b1031003803002240e45c0c40c20703050185061000a103242c91940141d00032071113a80c0d002c031740c920055600110041c0c407911071017020780c1140030f0602c0e2a141d006000038400b90003201e454075042201c0c2610001c4c440c5580d00c409120381000c0e000401901a03212002c600258a0003001030040640040e01c1c1c8038403111030391200d0312071a05071115458142d55480e800c00e01400c040000114000c0c0760708040c80f040f451359a03130a0031000740b20580d1003407070380d1002034811480e907d404440b00340e510480e00f0300c643e107231f00d090400d01c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 269273354 1250 269272104 269272111
    0x60a0320130b011d0a0b040612050903161412030408030a06090219030519090f0605010b1309090c03120906021b0901050d0602130f060314090c010e011101060e 70
    0xe01e101c41001c1100030080d018402c1038a5069683c4102c450f06900600ca1131140c0566066001241c034402044130340b1044090030041c0f10f5541d0b0a06601041c00700c0000310b550140050700140c10800144e2044441c60aa46405540c0304224414003803404401609001200b00c41c186641000000c1c0818003107010060b5004002c4000100030080c4e650344883c00302e1180c401121b42c0d218003503028201d0a4001c2e031202e544000320111316482e0712809001c50049400100c000c4900311041ca1003042449510300c9520301400410301038610305001101c5d0184601c403540324001c03041d515580504200554900c90000940d4001103965249010000140c80413803d40600d0b0b00500c40c10721044502008903c0c2e44441e941c0141100220340d00f02814006c54a10106040d40c004e602041240029291010642c000740040c20650341114204140213040e1103000c0026080000d0000034441f1590000c140c400340c0f01000d003803104800200d6030050380c0207500907d40a01c0ca5180030400249040303821200c074070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 269274604 1250 269273354 269273359
    0xc010b1908120d0603080712110a02100f0302090402030a021309090804030b041a07080105192d15020109030807080411061809090c0a05010804081e09120705040b120c09060a0320 78
    0x3113009e084004140e5a0b02c0021010b035100b40c1042c1c1e42c2110500400c10f10000142074036000d460014101c0104040c0c1c2d02c19101012465030004001081c4444070601c032001e4201440c050101d100543c880130300e14000c80c000649982c0424002c10108924551400e0001c404500c842000c0d203070002000d0010715091140c2809880d28200110020300052041020f54080a5407440092003050241d20303020458000254000031003000030402c1008072000903400c946540c00441c20480c24940103002d0800508402c0502900c42d044c08005501480101c2e61000192809611428580c90190102c0c0c40480d030140c20130401414032030b044d0303070100710244070101c10346450002645d2000110b1b0100c0c1c08540141003c50107103c85a54101000100901e001c20203108030704001c4004002641c907520983e00e45440d41c40841c0805c00c072b0502d4001c003261040e044480b45441c0c00f03d80c1d4201e0711a07100203003203407007080c3d16400904c031036942003c40e0010b59003142c42440803602801d0001d201080740190240f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 269275854 1250 269274604 269274617
    0x1a0d05040605090601091e1a1c03020705011b151104030605220c030f080f1c060f08030d02070f0b0705030403030f0902010e09100b0c010b1908120d0603080712 70
    0x2d88900744c0c001c1047c00754044440482e0203055080c0038008001503582c040c6108031203285041140d03984000d41c075452080390801c01064001d80b17000f034906070050748450b06204000c60381443e20714070300c046061001d8004440d200400300d0120301c42c00402180140f90a02c0c1c0c0301007070200500010b644698410444054201280c890619841030154103500300100340010408044c40024945213200d030003244a40e25040c14211340700084c001c00c1c1c008518500812600c190705400c40d0310b00d03008080c0185001c03120280e090342400101603da00c45c41c1452171041d81c0025081c81017001c01410603c04641000100400307052500c40100351354000e0f40d01740d0010381030809840e00507016100341c00c0e00d69030584a40004045050070302107040c038020120840701d24000d01c00200100c170300d0000c10240e074440700001019803001c002c00100d00f440c0c0840100c1c030400d29100713000c0c141c00000c0d4000058080e1030400d0f11080d010b41c0744404ae01c1140c00c0288070b5200070038a003003001884511128500907684844 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 269277104 1250 269275854 269275859
    0x51e0406120e03032505040918030f11030301060302090d1217010e0c031501050c0d0f0212070503040b070203100906150e06010c14070e01030c06080f07020303011a0d05040605090601 80
    0x76903c1c002520a1408890b1741108604a8104c00c010300072044001d04106080c2070741e50a034a021503550895816141584c40e100324101035100d0036000c042c1070340e820310010b40b10a84144030f42c0d030f010500640c2c00389035000418651958079010703004c003525440140c0d8410f0201100000700826801d24004120914000002c5501400b0500c107511401075441d105041d585c600f01c00d145001d2800c01d0040c18003e042240c0d003140042400031403414000380e00c4824900324840d000030b2070088041c1061070300720300a1085400003107001c02160102d80303900c01c00f00d443d00c20700c2c0000390520034145001c0714038915240c4030f101001441e81010031800c81900d00e6855503907a81d03000580c108021101c00780081c00f100761841c00030348007581120b03031039541c80e0440d1403568a4016103506190285c000380c80500150504201c1c0d540e00c80103850b48280400c21910b1a0f080800380a940d0b40018050345c01e00803a4540350000e6101c414058944013001060144010308160034124010007003600d5030501070103004000b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 269278354 1250 269277104 269277131
    0x90605010b040308090603100e0a060501080718090c020f0f060f010906050303031f09090b011502030c0d0509042310091104090221092404080307051e040612 69
    0xc2c0c900f101e81001c04c0e9071038603003200108101d581c4018848a62403800000120b400082d40c0d407000c1c460601c0310b000050860900b4005803040c2d1004000300e08001550f003504840c40e0300b1100f8a0300f11041c00380c1c0480e501010420690801c0d00e8010041c80d28414148000d040c10f4001581a018000c1488a13000c00d90701c9046c0c800c2031b1403c90140c207805510400200301401008004a8002c0c0c041d601204030003903c800b11070701076a40181c803d503002c0c20f0704c0c2c0c018001030880b17000c003074000e070710b9400118541002500403507116032254250206000c00419400070b00d8442d80c21849940d0700240e80031480f4100841000c56502060310b0f1a101440350f0300d4041805c0116100c0e00b05a1a40204001d0400e40380c064180003030b5001c003464110010b980c002014103004081d6503503018142c5800981001c0110300400542e139821001041d0605800409001c00b04030050212034219400d890215642c0000038400c445000c40c4140092800c080040c000407070719407042030360b40c2441040105200020202d0388 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 269279604 1250 269278354 269278357
    0x11404050d0e03060f01030b07090801060b070201090f0f0b0a0210050f091c022107050a03020a14010203160804050109050a080a020d0203040b0d090f051207021309030e010828090605010b 82
    0x3c001401701403580040c00820700c58407080b5401095898501c00c02c9864100b02030946440f503010348280e800100740b00086680201800d405081310b040b008000500e4047c4500103480a403260545440c800030319524094030900c148841c1c50302113a81070000b400c0c92608090f2500084400340300d1401201e0b00001c0d03490540d0f81145122110742d00404103001070801014900c2c1d0a02440102d0360401c00111000407402d0020701e0200b030003038001d860080d07442c0c03c0c40200c0d8400101c00405c2079204004014071140c1c00c0110b452a240540351803c0965118681f00340100b48001025013107114043c800010040c3d000000e101d40c102d41d03170035035200c1e127003220059030b482c0a1401030480c1c25400744100c89041801d544040b00450185148085108194079200d08110030400480384000340056132030150305000040070103040d0407420400c200192070310018411047c03c5038a43c1001130f00c4002c6075070705401d04002c070310390202240019511408003010000400740000d003210100c4c10039000141002c134500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 269280854 1250 269279604 269279611
    0x905010201020c151302031f05070504060c030507020a1211120106080619060f060201050a0c05040e13060608030f131d0c0a051209030901091520011404050d0e0306 72
    0x4000f0b101420f004e800c28200c28800034049041e40303c503814804056501008180070503040e56200c1315036111000c10850a03208003e00181c14003070704000801405074030941d5800c000c0d03003514000e5291202e5200050b41c04081c1d50200b108060440200c006011021000e001011011070310142600c200154041c2a5400c504c100c40d03070b42e0070010000e02c618110442d002c4c52440d08401c00114582ca80d54414000354094008a0050395554200404100035114000010150741002e505061510102091103003000f0011244c1c6508d283c404001c016840c3c200c180905500310035203403240b5200c40c8000d0640c000488811035008017a8002400c2000c0c084003211981e0840303610500d51b035039504114460b41c4254400c908101c8100003001c4003118407214980200c40f4003001e1a561400000010510a13a64022020400018003c44c1000340c100310b008484407201500384140085143d041c2c1d0040c103101000d5910741005000308810400c0201d040e5000d841d80361240045102c0c1c04051654820084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 269282104 1250 269280854 269280877
    0x2012010e0d0e030727050f01150333030b011202010801050406030b0f070507060c050306032a0f0607080307110d05030105010206040f051903032903030d180b0c040303090501020102 79
    0x65824060f04445c58503181c03100400004502200c124466500101c40c01180c40c45807000c076001c01481342804c050348103071101301a40743c02e010a2002d40180d03e10594485030510f40780d0840e0500303022041c0300c0e030503400c011900040d03090415a500c5003094004040d91001300d0024601d07400103d05407a00744074841c1540e0300204015842d556204851801060103041c42c0300b8840188130000c0021002c0c0500720702c0540c260b03101c80c0c50341803080506203030145008500440d95150b001c7c84084074600d02041161910490702d15241c05070900106e00503110b00540034246640000030400400d400c902040c004080e00c030704840080f00030400131a12030200f80219030050700301c0b80114011442e01995112031502500c25907001a408403040100d01c0008441200400d46607100d600205402c829502c9141580c04010521110140300013516446a140701c10070701a51104019491686c035104030210740d41c801d0000410b41441451f443c00303034009100840c00910f1a840100303080d40306000342c2e125200c98 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 269283354 1250 269282104 269282113
    0xe07081501060509011404030c0509090a1709011115150108040f030315050603070305250c150209031e0709090b0f0403030b04020f030406060e040c032012010e0d0e03 73
    0x2403140448495000c80304c0307641000041400e03000340e5072010004000441c0300d1942d180c0b010380382c40c0030b01c070780e100b0300410241031500a980c0000101d5010b5044c000e0f95410030540c00d5071441a46c00507900d00c0d2450341380744980e104040d044d801101040210902440780b66414043c40c0c1450340044480081c116030003020031004140201c0000e00030f401030460f491031840241401074540e0040344854104070b5008000070340301e8043c0700b0800ba00b09103007103c0b050840c403a500700c2c0300c0d009405040704001c410014240040c10200754800812681600ea02441c01025900414002803030078140c201ca02c07240310b086014006002030f0b000704074400c0001c0e144e40b100c5060151b590702545080c41410080054091544407140300c903640c1da4500c0100303541c40b500c285d141d450f418982400c20031100180c00c44020244003074240400b042d10080101c0440760b008143c0d25002c03500d00103140c0c5150818000d65040119055001e2610034103401481550f607064046a45581341403200711942d00001c40160f070581c21 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 269284604 1250 269283354 269283359
    0x114060a230604030f0f060f05060f090c041e061e0c0f020301060305030409021b07030f080a020f031207110604020a05040b150318061e0105090402130c030e07081501 73
    0x10311142016420028441c9041c96545e40343c050150000901c101c0b00c418180f0515800c1202520030710819001380d0300d040210f460290081480070320030b00c0046102e42403080014214000d1501120058091180040705a4800c480075044c6c00c407003070040502003801400091544810440b1004042d6034035640d4070307080304103610b4000021b9070b032410a076050f54072a08040003103041080108000d000b03c010040c2c0c1c0711488501000240da905020310000c0c1c002410420104d00241d80c94007803203400844103640c90061071020307881d00023211490005808080b031624085a0005105845281d0948031110295000c0302d01d2600e44508031002507002e40b44490500ca241030640c002c1d0700f0074a001e40300c0c00c6802c41d0764054150540040300c0e0a807034090440c1007100840707018841550040410200f0b9402140542ca62900c285014012680210300343d00000b000e55a425074001110000c0c3d02e010003040318400801009040039041c1103034603200e251400076040318001108414041d03480504480c990 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 269285854 1250 269284604 269284649
    0x1003051506070218070203090f040213140d060c050706050a0e1e01110415180b0405060d021209010603060c0504120b060d080a02010623060909091e0114060a 69
    0xb000a242682c220440c40c401c140c50401e04c400c0c00d409195545c00564a03070408108109911039170801440c0228010300c00b21140482c1c8000c45825502d080011804440414010800c107130306a010280034036081040401d01503030040001e11180e0b002d80001d01066481d0302e41007041d03803100c3c502060141d01425034400c500f400d090407a180814950004216a8000d401c5003949402503000044824405605000d50540000d0f17000b901c101800b1031001e02c00c1ca08496121300c0d003e9845a580281e0000540c1c01c07600c12182e049642108042d0180c840b81c1c142180c426000f052240400c0381c034140303440c4079103950768003640c2640c003190341d1400910003060300c50303445440c910800f07005590440c942d0003641c00000d05580107420401d40960000030a01d20301903a1502c000240d10032690a118100981180760f12248121440c0030415203034100705844503c1d100e450078844404160b400c00c5030300200c41d034034203040d005082a5806110f0040170741c3c813190100140b881d100e00c039440203107415502400811 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 269287104 1250 269285854 269285857
    0x2090a0b060409091b0801050606041802090a031a070201050c2203050a15060509040201050a0c02030c0913020906120a02210303010f090e010b060d0207060605040c0e1003051506 78
    0x3084050415030030290746018003800e0f2000018103c904000030880d200502ca0b4002030039004051040c001d000c5414040c1c041030280c8120302640c03880418a442070b0800700c8094044444541d8050702980b1040c1d40c03800c240b1244024144030603d5500c00102086240c1d00c1401103d004040c2d8032443ea14021030881c481c2d00c1085044180b075580703640350000101051082c02003000c06070080c541c0703082400038181d0704000c852081e0056031040c507181c030900015036401001c0c0c07601c1c0d05140c14000b680d00402d00000c0c0c54004190b510341c0e032201c1e1020030410713540281030305204110710940f00d05c04c02c0d80f86c1d5010068108150b1104c0b41682c2d010384524070140c500080204148050402e104070f1002c2d0612017141151300981003a02c010780d422904000041d0144a0145805006002000280e02c070710b00003191807050910248000342c01182040a200480d8000030082c038000344200105103d040c0003404004034210124880c0320724441200001d07010f40a458800e64803c440d40c01151005001c00106 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 269288354 1250 269287104 269287121
    0xc01140103021507051e0609060907060206340315080703080313030c060504080307080610020a060c030209030321251b060510030b0109090507050409030e06031513060302090a 77
    0x12441b400105095455940c3c1000c0c03219240c41028044038909030b4802d43c600f6401514289843c0e025032410800298081000703a0410380d8501900c8480b01c503d0001040014141041c030071480c0c50000c180f0449815601200ca030a5002e450275940b40d588070360068a03070a041c0b0001e0320b0500e0800002e0000d0083d51031943e444c0e48282098644c0c10300b180c440104562080398211406d1400206100c1c41c01d4120280560062003210030301058511420000d488816030b24004003010348801307800c5051030083d010f546854201070b00320798644040800c0284241d00c040b032410003540c940300c041118940c1c0307180c440d8a010381545400c1449070b14010101c80e00d08020022040b400107008031640080d650f030142e46e0098001450011200e030a5040804407100103a104281c0c99281600e400c0000e00e0111340481290411903000a84401c0350070103868512029101550000c40001088103400200400d81d501003000c5e00e10180411000d8076881c125111800060751140c02d4600060f100702203038010f80030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 269289604 1250 269288354 269288363
    0x29130c091809170408120c0307110f031014060f0102030f250818030c01090303230301170c030d051207030603060c020f010f0603020a0e04050a080a050c01140103021507 74
    0x50092698884902c03503540b1620300d01c40f846001404004019041007203903070f01503c1c00c054601e407101c4001e80903681c0c440c5150003803503c0021544600304d07955050a20050004c00340c155210306214a400c3d10080100a4400481c0201d05001ca111818480c20320b0000b0b20068004500c0d000e00d54074442c42c1904074101801c601d4605040740b0004900d502c041484152041c455561120b8540e86000c41c122101b130212400b0368000b4007e00000eaa0040350141103942506020f009201d812076801c503076600d5010014540f100000002401c105c2038035118041048103010b5424600003030b0109511010880134540c0050301c240060505000501511a001072090a0006219541c5d54602007a202040324100c05604150b0081c1d0800c1000e0041112a000d080c0081080509660003e00d450701d450060101148040000034100001000350b43d5a40d60411080c0382c460381e2940000b0120749c09400000510f501b80501c070003405070b10055150503680c0c0104541542142d420302000c2d43c1e0004001502e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 269290854 1250 269289604 269289611
    0x3030809030d020a09060f080f0c37090b13030b0a15080c04060e0402030703062004030c210c05010509180901020703030e070305060601050a0329130c0918 68
    0x4440391280b00034100c07131a40741c43e072061240c5400c001a19024001a0240510030b01404012000784540000c40c1e1003148050741544484c0404401541e218024401100305400e00700300134804807052201d001d482c40c0503521842416215480303c40325024000038000d40801414091000544c0e60786000c0e03015041110002c4c1194010f00d680740003540030740c05030060713070004c284581c15400c10780511400fa001c0c0003001c2e1440c0c00c0c60303804070780d1f202c01c41d01c070180040395200c2800305e6643c10805080b52039644000010b8685480303050480000301640300300c83c2000e400041c00c82c40408403ca100200c0d0f50003012500040e13160000560b007680c000d1440c154000c2241031002d041c04100c0f9195801103040500051725400305140240c100c4a001034083d00300ea0180c0001c00004600058003584005c0a00c2c055840c0c859142c0e0075406041256503d041c98201c011000c82091008c0c1810150b1010880307040302c8408860406804032881c2c02d0383c2c0800202410018050016084095103900c408942d000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 269292104 1250 269290854 269290867
    0xc050705120904110712020f0d0219030903020a0b1218210f07030206060a0501110d050a120516080f0915100801110406030b010519030b0301090519060e06100303080903 74
    0x102850788141006c45119012203c00003d60b41d04000c0c1c484102513250003800c41e030b0078030400a580c0b8600d88c02e00c2c20600303000007820820188a242d85100555014011019194989a14010303d03000041c414051544800000c0e0601c11103840d076a1492032500d02801c0300c1c4800c4050b5007145890040d2103800c886041010704070303d02020004000380780c0603901070712071401d1050170071a4010040d80b01a0410410384c00e00160090042102242c803640360500c0ca40e1000b50500607208400d108141d20070032484c1908010000b403070041042d9841126680d181200d80d01c0d02301c00388100c1030a0350002c01581c030903001800c440384044a840d4010368800c0d00e0350161540d03201e41d0380c01d559103560140c2c40700001103401c0100780e8041c0103008084409003019400c15100c14182100050020b21001c01c068503070a5040b62502c00790710405005030001c003075859500c401050002c00381701d4004100d903080c4c60115002ca2000300442d03d140a081007203000f21645280d610210385050b07014084800900040101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 269293354 1250 269292104 269292131
    0x1806031c090305060606030403080f1b040902072f06070311060a0b01020f010c020c0d06090f3801050402091903050616030b010c0204240e06040c050705120904 70
    0x1000010301841e03440440c0319081d490024146100944494001c1605005000010350060f00c0d0692141c01e510303c40c2480e5035010b200d540c030001022045400d01314009004141042c8070380040008a0190080032941507442c1c0040e10f07134a5201404007840310028200286502e4220000c1110b2030083c42c2400d5080303030340c80400c2d05110055440d00d6003260f035840e02c1060740d41c051202098100044008000720440d01901a4641c00704910852040050306218010131803d5802800d6641d041406800c24404614141c08a04800755141c20f10414021501040480c54030250300e1046c0404070620b8140d203050140720194100b03126280c2c0c808203611504102c2140005070b08002d5018800809550a001010341d1100e508903540100301400e058250100740d802080e4007100640c165000a1152800d8842c01124100032541d01e0200c1500c1000042c1c8850003035405009000444080140c400c54080981d25407240c440c0060413038010107a0904c2254440c0080c100890b03000e0404101040040e46 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 269294604 1250 269293354 269293393
    0xa051905150705070b07050c012604030801050a0503030c3d0204140901050315090717010902030705090915040f020603010603050702070614070f060b040207051e0c180603 75
    0x20501d180072004142c08042c4101000000e009104a185007481c19040d6100c05c0e46500200d000d050601580c0800c1e0704011803502020420310307001c0d0131400254100b620f8020130b07400081c400e803071191282550220303103850084115005400742c81c1c01402c0b84484113a0032101d0b090702800400c250840f0248208035880c001b408200003c240d694016501d5080000700d40d90300701c2c01010b45e40280846e42c018010b9890006031100c100b081c41443d841c03255a40d0054074582620344d0401212000304003410030820f041500700001051003141038540c0541c4400500210300f0382115001c1d455400b03401400c4000c59035180c941c2c1c010b401000d450f42000c0445d0045401507000703a000c0c400090b82c803020440071903810b00c83c440c058981890142d1072841462841c1d601802000009001082c00706400c00c02c020b010782c402d94208401510179515200d0604001cac0c0c560302147c51328501281c180026000c506000700390b0509a007002020345810301503030703c041c2c014000c2c0240280d4041c4034000c40780030142a0640d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 269295854 1250 269294604 269294629
    0x306190b0f180a11070f02130b0406080c01230f1b01060b1b07062106031b0f06050c0d1d041e0609180605102408070206060a051905 58
    0x588072112420070f04182812111520280300828000b40410130000b6400b10320401c071550100da45102050358500c00c00018280d0303d04840d03000341b500c000007501907000b03c0c03840d48408090300d500300285820b0b059829003508801240c41400000c01528040c58018000b5208500000e14101a940190b0800300c4c215025900040d02c039510100c0c0c0c040381444100c413a911058a00b2000d400c4082c58468082c01103400e0b840c5054107846c44c08423103e0790800300c0e4449001583c010450102642e40c802d0801030040e050b00070700d0030034100000f02040740c6006004503404402540020324200c0f4840b5011680003110f01581c0c121043d01200c170301a155618043e0340303c284c51001c0c0c0c0c0c94840031220010744c110f448030340c06031034041d0504c00704049042c00d20200b200800c2c0c21000209440d03444107510011400140c0104140825501401075004103292600d00901d000f5110305680d07454400043c2d940304022034000d588540400d805102d14201055010a180f044503d8944840d032107000007200e40c20300c003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 269297104 1250 269295854 269295889
    0xe0106020601140105070b060103110702093c0c0a030608100b030106150c0f0c08070308090301050a09020303091201060902070303020c0607030209090c03060d0b0a0c0207050306190b0f 81
    0x2103005100108a0050007280c688003420506e16003200355a41c40d4400c9001818241815640c4010716010700011080b00c10060307008110380540c0ca401c04010305420142e000c01d074800580e01c05030070742c00d500c60307144083c0c0d10a060090745050303a90000004115030001c41c0c000300305603c406001a40602c10021894540800b8801091031680e22081c5800c40e0280d80c820525030b00120b6501c440960041003589405401c0220031090700450700b40321012071031541c400c0381d9910075498004107210818014003000b0100710000d110945070b035400c220a030346070313002c019626401c00c01121840f450441c0d28101c1c000801400030801a0741d5401001c12604028020707800f00c0c0d0002042e85001d2814020703540d1060a03400c2c210300f05044180132442c4c0348802003402d003820310000080380781c03541c4013041a81d21580c8094401c2181c9040c02003140603000300c0000201501c907a10300410b840c540031030b14a100b480c0340e114401e08417680d001c880c0042e00c42c041348685c204c00110a070b001161500c14104c000013004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 269298354 1250 269297104 269297113
    0x81c0207060627053303070f09060e04020a0501030b030106030b090a03020637020f0711190b180d0807030c170708041503020d29010c020d0b04030203040e010602 71
    0x9210062500c0514070102400f14640300800013004042c0c0080f40d104125203000200340c03903c02c0610803101c8001c00003070b6454802c04400050383c4500d044003070190307640c250051007881d580e240b04412900003910000d500200360744c02440b0a51280c2d1200c0c6400c5001070005c14015030f00e0b02c0d100c0b2200400c0c2c4420030300d50001d0300c411050540400800b500040c03160702e9914004103051207103548020b41d96520140c4a41f129121540c407281da0156283c442c4401281e6030356890380c1c42c208034102c5d0010303c1c01d4001d44241216146642400840328122198500300c61300e04000301808420114201c0c40d0a54400750820704440400d440502600c0320394804e4464044c8220203040911490305d00207500343c007400c020802c40e4001050701003541e0494a03e07403070f84040607410b00f8080d00070b03005540c00030280500e8a42c1c282c100300503110000338002d04c00b4080c07110030200345c2d0044031061140703d000fa40044180f250000007030385041c1c100b544680244103803428640c551054900c40482a130103800140d01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 269299604 1250 269298354 269298389
    0xb091f030204051c02030706050a0507080d020702100305090601030b06041d010f29060315040504030e0906041104050925020a120f020d12110c1b090103081c02070606 73
    0x4200d140b81c80e98406148101d06092030950006c1d0303941c800f6000d2501006004614001d0711801001692415a0f0110030140c403807200714035803402034002c0c2c40b0903445000d403110f00c0b501c0e803400391040c103008003203001c09005a42e0840e1154403985901610403508250348100a4244a900c40011407116050700008142694406050f1042c2c40340d1440300e443c0f80c01004108410741d4015024201c4000c4180c5002340c4981d03480c0f40301d0714000207840346160000e0806d4104801c140c0d00c26039030003503102d08480303482450300c40c0c0041c131007154841080358000040801c0140118a4040515a480400c40d0705400d00e28041c0d0071402500c0e0700450030000582e10000740b041c20071000314a0f0086d0003400e840c00ba02285c40c51503000f55180408180302c02401582695140201c1c0d040e00100340c01c6090712407695460802c5103506903074203c0d1039000325105002c540207100501c1c18600c2d50f0704894204c0005810500016501c5450044024036621910b900300803100009006020324401003a0729003011b16040c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 269300854 1250 269299604 269299609
    0xf010f150b0a091401020c04110c16080a0201050903031603081503010c0c0f03021e03120606030103050a1202100f060905060409020102030a0c02060409060305060603100c0503010b091f03020405 85
    0x8401d42154210001c244071441040e50702500c41011a0080c04070702d03981d283c010b00180c1c01d00400c11030060304203041c480809480c041010050900f103a160086940713074400928194a46001d0340101411600054078550256118402334034041400074252440d00348204042030204484441c100c0108410500b001001040c000c2e0a0340d0004055000340b2a201e45084000c0c0785141c030040003402d46070b4004034102030510810010030a2110034a40d02c10032001c000800d6503d401002a1000d05080030002a02500b000f005484c101e80d800382c01800c401f000c690b81c940a0307000101e4207100714850303100c2680822006009039a032081c0c0707031840001c0c040e04000064007951401811540030341c0c244034070440103036800001c032401c1003580e00d03004082881c1407000035080c0c82240c6c8041025800c015000c01400300100300e20340903035021022111101e91811802040d40c0c10b401080f0041034051004200d40b00f0300c540141154080100700e6107441070445100c000d9041c410842e6800654045028013090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 269302104 1250 269300854 269300891
    0x61508070f0806150c031c1b030e0a030c1b0603060603050a02120f060409050f1e07030c03061d0a030c020112060f0902160b04120e150d05090f010f 65
    0x91189801d1040d4a403c801058524814000c0c010002c600060040241d03e014029240600015040c2246103000b849800001c1d210403e0f1404003824403031950b001481c007920130703a010400c881001c2c2403000c7e2503403400d90700c00440e0711081c0c43c03804c141919080380c0c03520046003401030481a00d000800750b0a101c0004e0840f10000c141e08902441080144503425001460640c0030410140383c280541d9028042005001c040070000e00354415026080035508000c1012601c045078420304000c101200782c2a541d650520b4400074040000116041c400b1071880d40010284000b00820800c0a0088004030707482c005958030700780e000500440d02c15045680c0564a1310301d40000c08801d000315421b00164034401000c0d8425070410030303400185001c00c6200492208461500b1829110039481e090401200c190612060100040c40403101d2094500d000c10418880c03140d0002600d00705481c05140d903000323203006001440300e44180c07a1103d2040800340149044950750175800300340034002d862160545c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 269303354 1250 269302104 269302127
    0xe040507060206100602100e03041a07110139140105040b06060f040b07020a09020705030301060809061e1e01170105010f080a0b0c090303040e04030f080403021c020106150807 77
    0x528000030040c21b6800940c40000005546000650b10404080d541c0365129681c0704070a850f05610341c101203001d0040c042c204083c0650944440b07107078030030011038040c0751500951070500d001d11540381d6282110b030500170441280401e0111800229200d42c1c1c186801c0b4015100c03169103e508110801c03c668007565008501541d0107070610410701c2102100f801107015040c418103010130b2010566484513130407001084d02c0c08045684000c40e00705030b91254406d02503003020806c00f6020031040c480000d5a144505c1100c00a81d9410100d4101e01c03890010180514481c403540001800010034007185041c000d140000c400d680344908800f40c0c030700790b81d0142d20420b86481892030400c41d92001040d40d507071043d4849021b59003591902003003003090080d02c0c1d807035816200100300401d41c0100628500d0003280a41c440b5803482804190440f00154102c4004005170080d840f5800741c0c0e042d100b48444851824000814419210301c5814510710301c0030600310020b548442030107801074000001442 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 269304604 1250 269303354 269303371
    0x201030c0c030e0411040f03030504050111032104080c0d02010f0c0206060907030e030f0406090e01051903060b010e18070e060310140f040905060a05060303131e0e040507060206 78
    0x1c1081c450710b016000e0050f240856000e41d80b20f22804c1c846002520484000d8421031034501040c80d20390400400503082401030501046047c501d041210000001f50340c060780e60107081c60380d0f14004015154182002410446809000303212010160030184442c03110201d1603400051085203040c8075005480555211800f550064800d003c3c031502c0d11b81d003441e07101000f401c2c04604c4044201c18149903200758003803201c16000100380401c03020b5000144004a60510000402c241d0301c550811143c0358203070111400c00f504850040000906c80d4004136074500d814100010641c20000108060001c02c890450040700c08604100300160400310b40a020142030760441c1c00e41c5022140c00d040c00720309000c0c0081c690703000300810442d0380d202505d034404144040c1052014040324501107a580c0019125820340341d00f4440003c040b4180003059481c04c4540c806209905440c0007042e8006207012003099801041e1501c0104c2c0c000b440000d881d0065200d07100809c103071864500000c0c05c10700054440079 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 269305854 1250 269304604 269304617
    0x20a0e10030605060f03150d080414270606160f0204060602010902010c260c1c050906040920030f01060806031b010f02070306051305160503030a051b1005040201030c 73
    0x705907101c070400d40e852020203145d0195203403505080b0040200701c400382560b100100b44601070030401c01c0c6d0060000c030f40540410355401703030203101003140c5140c180410000c002c070500d800310303091191201a141c0009020307101e2450f004440308180030f03142c50a2002e81305241d400ca0504114103151049000402051000b008201603039030000f0b1801080e002d02401c42021500040051641c0f6912034400c007032501d1040755103403008402d0603100c4040d585400c940864032a81d000003540140c00700c802c071901c01000d0174907090034040c0701c1008144d55820440c00e201c252004e642c00401c90340c000c6000c1d08150f00686465894800c0080076140000c02a0b03001e504036540304a94000342146a40e005902403c0003c821060414102d152440310342c00a001281005d050100711300d03e841d1202ca4681c01441030b40d4040c00d07030413074000c4500070034402e031501588100b007a00861449440903000c002e00300340c600d07650075145409041c5420420b181241900b682c3d082400110340c0c141c0714030415802a8107000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 269307104 1250 269305854 269305859
    0x80a050c0d1703250f020607021c030c14070503090307060306030206040501051b010f1a1f0c02031f141f0605030a060e0405030304031403010e060d0312020a0e100306 73
    0x100000080b212903400c2c0c40c803000c00482c040400c1e035200c903d416a420f41d1280c04114080a006003045803ca1001d0f01601038080824215403002c01d0603041c08601e05c0b00b40900b0001110201d0007404440c2d1361a04008081013083c08403149800140202d42c05840110f0312021034400b01418900c0a40c0220305051910381c0400050301e544041d64100d8000b400c28a4480815221801c3c06884c000d002c1d88540d4038082c2080340c002220761105141104100d4460048800f8000340301c484c242d41c8803c00e125000910361041214422000c2d8035401744058203582c044064443c03140781031920240c00410f816202c501407007581000688050340090800403240011100c04003c52020006000708410000000000b0740660300a81100008141e03040028007145420708003152a5001a24120000750b41d000180840100042c1035078185d4461880f0080e29856a0040080d59510203104030144214038444c1c960750322442c0f02900c14101c881e00d0303524400041c60104482c2a1440455000703051400105 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 269308354 1250 269307104 269307113
    0x31c0606050301060c0602370f1701030609080913020903010c0309030507230312012301021b0102120301060507030e030619050c040f03030203070c080111030f041b080a050c0d 77
    0x10b20241c21480048e42c1d207c41c800c00494168012400800081050020a03640c1c0c3e40e2221200c0c00c40840d41d2501100f0340340e140221a1070507a2002440001b50480c0144040b40180d480202030901c038040080c035101416021031507000c425030840d0f074031542c0030906c005603040a000d400c00c00d0015140400109900780d8025240340141c001c040d1020141990320504074003c00303c4072408040303ca048a0711842043c0b40d00c0c0210909009203c4680000f40e9165031031700400e074031031604980503006028000c3c22544c90196418020762810b04602c9085040c8100301c00007001140a40001e030f032050340d0350b052410041c000345c45038400300d4040da00000400c4001500c0d01c1c04c165910442d0000810241c0380d00c1c04016813405035401128828031950300000030150000002c0400d82d22550300280c6640c1c0ea0b1016034200c82c041c81c40c00750040003c100040d8150410600c031540701c1d01c55802109180040d003000645146203410a035825482003008405200341000840c0c41e0000840d00d078030960303000390385 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 269309604 1250 269308354 269308367
    0x321020c090708010b16080d060f14033a080f060109141302070204050c030f0c03060f10032c0f060105030705010f1b060b040609050906040209090708031c060605030106 74
    0x149130325400c004124070a100c90f9a8105a00c4280c0000d165a2511800c2141000401d43c0344501174070700707d80c804001082c5810bc954400c2405c001009042034401071004580c03002c607121507059066524908124900e46182d01c503481c0d40290307542e041a5403420b0b0341c4d0a140d00c48058842c606110010341c04202c0c0451000c81142200000d0f540c18170110800403080340a80600c020017544142810201720034150107070007840c4a0703012011460702c1503e030700380d0995a502c029564079070405070750402c01d6440c0c10101d07901d0031403107010701d40050103204c00c4c1002e2001a1000c041221540d41d40c07406000011390400c4800708050401c0041c1c803895142c800040c0e40c500c4140b003040d060002c8102130781c0027140500789030052013001691280b040f0103d454094014400c420205101d60b00d44100442d800a15105041c0724441d030030010107941c0c5841c1c003000784140c40100001490f105000b4081281c000602c05412528101d0141d000701000b91541d00e010f03648180c2241d03042142c1800104100340d4040c0b0f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 269310854 1250 269309604 269309609
    0x30501061d120316120e180103110d0803040c03050c0f09011403120f072d061d070305030904051e0c0705010f020315030105070f050708090a0321020c09070801 70
    0x1c07264445440c1c1c2c00303012400d6000745030681401d110b81554140034807100c0c513030360b4690148507591608200f00d02c108101c45a05032010591400300b00c40d00600000d072141e1003000b81e2a40c01041441c40d03424035a2007100650089400b21060400b001d420001c019080008204d850003c68100b4102c0c01580d0100c0e13001801441102ca40000002c140b91003904d0600c030000fa80404403042c6583d8001404c4c80030b074203a010050843e100040f005251040c42c0000300705550100c41c906071100c0d51841c60321008040c0001028200c0b011131150b61041080c00c0030080c43c2c0046100d82c02551701d54011004200c111070008200814101d01403461030b6074807a40e200b10550203a080600c240d240ea00b01d007005401032036800159043e451002040c000040342d03030320740c010039158110000c3c4504d603582c100484081c00c1e904d1740d150110300b0902c5070000040d4428094140720b080034150907034440c5d49031034986280c819200003001c0b03800c541091000080c0e0610075a00100c1d03050b10610fa40d4100722000811104051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 269312104 1250 269310854 269310859
    0x90d080d060608160c0219120b010504060f0603020a02120d060f0902030601050712090503070609030b0a0c020304050409080d06060504030b09061b07110909030408101109060a0207170d030501061d 86
    0x740340c80455544103202047c22090701c500d0b0008540303034113848424244911098a92a00b06000007800d4603090003480107075132184020700001c0b8600513040d806504524418019401f03440d1400d002c205100c4017401005070410400b0038001d140100114201c0c07000e0b08050340c0d0600400400c051660800216a40507600c1080d4207010140141d040380c0d241035903002030740d140c0100b201c0020410b0344904c1c40300a8900070020306226441c0c01100204030b0ba0300c0c44407075015800c28041001103281581c00060201d014107040c52034000139041200899140b900050081400440c0c14400e02003035204650380040b0104c0140781e1400c0003401c80c008001110503030021620001900c00c1040511409022041e0010704003400754108503513001e07226085070207190700e03521a2044a0301001000c7c00340700710007120701032035a180c850720005004803035020540d41e2040d4802c00000040801c04040c9d201d004041c070741c001c3e040e8159104070041c02c1d0303001a800502008405080782c044540d41480001040008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 269313354 1250 269312104 269312117
    0x5091c082a030d0906050c1e090103060e0c040f06050c1002130815090c0103110702060c07050306090a02090c0423031c081e0108030403060c0203090d080d06060816 72
    0x4040c0c01d4000c01804000c90300c814040070402c0c2203041191313001400198072859041c4950b51f1500d01013003050080014010a16403101c9a8020b074071030300d40040015000c185004203500c2d8640d194804034000540b0801c5030944005404c00100c400030050740e0182c8280c1c50401c0c502410b00055581e82c0c41004200701c54103500050844a02803420003c0f0010000b200564010840380941014800000c5a5000c414044c0740724200c1198401c0c882d81a00e03603220806a03040403515024441c807071700b241010810901c07420700c2c00b04051b90f01308800c501c81c02000c0000c0000c603405106000c10240054410518400180800c5c44410810399404002d41d1203035500c07643c81c119201c0043d24090001c0303030b10300940807000c004105455022140d40c0c410760301c024000706804020006c14540301000d20840c40e01f41c00a1009000040c51600080c000050f548102c90a10711007200094035030705090011130301c00c0000182d00401d6003090280e80014402818030841c035103003100304d0101100070700b0842d004200c3c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 269314604 1250 269313354 269313397
    0x6040308041e12060902090901051006081e040803180d050a12090209180106050a2417010b0714010c020309100c060e0312010e040f0f03020309040c05091c08 69
    0x4040c40c64100401501e8003401030b00f902400c0c004010f0a2440d0284d01030104480000c994000500445000d090040300d095000b074580a400c58000b03402a1081c6001300310382c4009100d141440d0361003402540104001552400d214000b000c0740c02080102000030340000d0317031040d81c10f41c001059498103840da007403d1651800340e0041000802140d00021b50100198083c48030450f60041440400d0310b2a1000300007454490080144151641c03060b003001010b02c4103030b517420000c071107404641c1103000d0034000d40101ca2001c1500401409820880c44004d0200e0038000f844900e044440c12048590f0007049a040120740c000d4992040704910b41c0110140161505090300c10440c8000641d007000c002c0005003104d40c0210b499034044038030050420201d40c00451044540d405090180340d0210200074240520796aa40d60301910440507415030100340194a456100d42c09003000e0401c07140e0700c090351402c1c01c004101404051001006043e8580e819980010302c4d8502101c0c200040171080000490 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 269315854 1250 269314604 269314649
    0x9081c080f0915070201020d0b04050108070504020903030c0604080d0f0513080a050c06040f03140f030109050a0221180304050604090e031c050405010501060c020904150b10020a020f0604030804 85
    0x340f9010350074030b050f4a82d100700141aa8194060141003180480c2071207120000300801042da1003c0c060a241034200000400131b074503065008017111030b800303001d0340d04109000320003600744031080f03c0036241ca0b840011810003003c4548a040d824003041c0c002001036040948100b14130480140c0024041300d0001592410f05000d00c0903261895060302c2100c7c0c242c40d02d450708000d0b000e400c401c118045010902072f4210504920140c50340c6107a52603809017168602224000541000381803e80303400e41c00c01c400c106070003a188202610058102011a82e07052242c2124048030b8546203140391500140401e01c15942d0b48000c40301211072241c008078400460009260561042080246072482e10040034008813102da0000352185000700000c200c0baa0b80d460040d610014907040080d03211f440c4100040004a400c4110114100109000a201c0b2890004174803030b118540200300141e4000e6500c2c50840c80c200d040840480c400760380c5a42030616542c2c41d01d4850249014601800307040c0c1c8510b60703046 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 269317104 1250 269315854 269315863
    0xc02090a06050a080f1506030d0c0309031a060f03120d0207021c0b150d03050d05071206140a05060a020a021e060d06090b0a0305060105060a11060709081c080f09 71
    0x188801440c003000b40c1e0390f83c07441580c0e9180300c41076019540101d01d041c0701b00341e0040140c0c40c031601c0c0c00f50151a403031007022800c132040e001c0039504500b0300c04141000300114214581c210b8a600540c100d81d055400c059003081114900400054420350018401c4030f101c0c1000c0341a00c40e000c40d00e88015071240058130010320300e841c0c802056151403d4850a040501000c20303400c0e8007400da03190040d6076034842c1c00c05100c41882e40c54000360209004001c2004000483d500140c1d010010707140c05041c9815003081a0150b41d069030140007551041d48540c07000349003d02c0580b00404040300d080349041d82c2ca83d07000e901c07130a507054043d100b20300c42201d01c07801a503004443c031106140148101c0e62460300c4514070005050901800c40010300d0400c02c0303400380c06e00c4080c007001c0d241c000b00280a16840c040401c0b500da8800c901013000c20546000680c3c0001c4100001c5001c0c05071a1100e00300c3c3c2e410039521078a00700a91000011103040107000c0110b49802101c0241c00401c400340301040b5070303103101c01a40340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 269318354 1250 269317104 269317109
    0x3051914010504061e0b01140a030b150903160e0610110d0c060c0f0c06021c090b010303020c0a03110f01031d01090209091209060a0c0503070b0411040501060c02090a06 74
    0x441d42040c08100411204c5d6101c80d508480c81c0d0007024001c143c00c07011034100d860920900340412681900d62000d401c402c00504120710403171a02160256511021810448515400012420b40450750098a00c0c05100350092071044c41e81c0d020314a490076560043c2a48007400c45e9004020400c84901c0d01803045000100600e422011034800480701d020040071802d030818152201441c1c41c1c0b602e00181d200360014280c0104a81d254454808541c89480095200741101c066480c2c03061000b601c10810742c050f00b21141c0c05801c1c0480c1641c0745080190030141c1a0000900c40d500d45e40007400096004941c400d03034840140c40c1810410b8000f00180e00a0010002001c0b200c0b400a680d00c1003810150000c8501d46c2c030980320dd4440b51140c1500542d640418154000200d000b8041000d15080200150682d45900d2605d40d081d40819100c01c2d056500103401036441c0b031000403c0000380700301541c00e000f8006061f03804001d19803400780010040684c541c4004d10070300c2e901700440c5042c81c03d50011400b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 269319604 1250 269318354 269318393
    0x1030204020f0c12030a1107020603070e0a05030d03051f151407150e0c060a0f1d0904030f091a04060309060b040606030e060603030c0a020d0501060e151207030519 72
    0x42403204441813940c10b4208694400304581080f50b0001882001411740d40c40d01d80c00b070525400d60700e42d0001940c02c051078242640d0001141007001450f0b035020840740801ea49181c50020300c9040980741d0b601d410403a00d02520886100340710420009525102495000c80e092928820380e540844d06009540322381c441c06000d81001c030407240d00d02c48440d44807401c00d80601007120054040001480030343e0040d0040341700851140b00d10304660f43d0042003848030200f40d0780003017421180e130040082d0800c003040e5002e60014032030020380301010750008103520141c4003141c091038450001c1c0c240a02030388110300079a070825844000340020010207400041c03580c500107006001198560750010003d16801305080010310580307000c02c00500707004c400c6980c900f01e02d02c0900400c183c190203110229190240072142d9646c0c9140000700e20b0700c42c51042d400b40e8840f4a00e074041444400421020034003140f100c41c400d80181104000190000500c0d03900c003c1c980010060301041d070704011154507031020a402 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 269320854 1250 269319604 269319613
    0x40503071716061b0203120d0b27070e03210c1b09040f020120062e05090709030215030618090a0609110d0f0605091501030204020f0c 59
    0x54812031000306908500310000803600c840020360b220030360249140c0301e03500c082030b080303040001d40d07035010710405107074500180445a0b02035840e50107490f41e41c86083e44841c40340c0d54130641c203103526290030004400f045000580c11b450f40c0c400c080d403205070400f40c224001e0200c01c444020305038400b40b01e44d5204100d26074004d00701030b82424910000d070340441c12031350580c02108582c5942c810004c0521440b0700c005002c1030140e503541d903103509100c4034444044c0d0501c20700d80301c3c2d031603600c950409103c00321404030081d114508000c0302e0051b070581e034620082509400e045070001d40141012581084840469410b441511054001e503440380c41d50b003001c0c1d08029044044400885a54000d5000784015100d5950142270400c11412071003003a02d0003042d0b5001041848007040d4982c001d941c0301c0f401112010307415801440021250b0b030500004640380075941040300140183c0d403155a6000d011900589018451440c84040c10401400000d00c6550f011500c201621050005d640244241c5800c95 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 269322104 1250 269320854 269320859
    0x90714031006020d11071202030a020910080606101d0609040903020c0907020a050615010e120a2a031401020f0307021f060b040605030604090803180f0d050415020304050307 76
    0x801e2410081c080e99000d80700348446070b1038140c40384d125041504000e802505206050400100280c0560071080c0d0f8188641088400540c3d11055080d025980c0542c40303480300c84c503100026003401c1005055520600182402c4020590454030b40307408403101450700b442004204002171322030300480780704d550000e241c880001c1c201078000403800d03504841207846000a540d502400c070707510ba080c140014240c0c0c1000d00070800181c44114001054041418001c1300c80341080080f5102c4d281d50441e6a62682c04403040740240008000505418100c002414041d020a502c50451202c045c0c84024078400600340c2c3d101e1040710a5050310000e649200301980d0b2400c0c0014002d55a0900441480c183d0303601a00704c0c42103a426220b000100e65910f41c0d188e04152400384140c07000e400080c0030580043d03c8100700e10000c1c070f0380e000443c03003038940c040c001e54101010260946800003007605010250302080f000054140c110041d41e040f106803054542400c5400c0d03500301d096015030f0380302e642c0520032000003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 269323354 1250 269322104 269322121
    0xc030c0d2406031406010c14011127010c080912010212040501090b07031407050c0a05250801060f09020f0408070303020c011103130303031113140913030e09071403 72
    0x4402102e81c80d6406000310000a00b26511404040e9110350108848074030300c0740040d0305103510307014400304c4400000b201d4480d91400c4034194071028820882e2002030001ea144410311001c00100100c0070300e82a800000503564100381803040c2070070a032181e0000141518011001d404443c400d060542481150b402c140c44c056001e800154404c60300540000000340781c86102c0e121302d0080300a940754040041d03d68140c1030760160b2101081030b00c1800784000dc500412410001d0781000340e0343c6a10040302c0380440740410449241900462103c2e410050300304006851001034005852009500503519104003107000364904c96036000342014002c030304001041c1600450baa4180e91020780f254001e120006507542e4a0344126840070f00300340003d02083c00428402d82c4550b540014445840e4600b00303070550001e811f080d580e03222100d10401144950581c5c01c048281d103810042c441c2c1c82e0a4142d98aa4018001c405078414050003400d074040018001846500d010f8031a0f2040c150b0141c1d20300300300b541d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 269324604 1250 269323354 269323421
    0x8070b06010801050111070603052203091509120204110c070e0a110a080f1b041403070b0c0601030602180603070f0e0f010e060c070f080a05010608060c030c0d 70
    0x40107030220307420700d000003010b5005040c00003540700d562000d00003071070070168240e00800d8040d10036016207003c40910341065840c0d608590314180281c0712621103034039004052a250550150f4482000721600b4100510001401c40301501581210080340344904440c00070402e0041d5405082184500c0e90001415950b54400c54002c158118080c0a83da0032000c151170703a44500150f12000510b840f0000d001241c10501490300039010031518000c1c20721a0780c1140c0c9a030882d402c003d40031a13200550917400d1408110810007401888000c904004100380b119888260500c40640070540029000e11002a903000125010030004c1841e40c0301c2c00e2102000345201108800c640100f40708081e44101032405441610346414160754800702c5501901c14001243c001000d444030610a081c00483c1c1c08125a10b210050801c0c000140b074000101c1c14036509540c1c00f640040c5858200e0014072000a08210403240d0000320111007580c5d03200440d01c000000c1c10929000c5550f00d5032000d0200008401c40c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 269325854 1250 269324604 269324611
    0x20a050a0e04061a0c010b1003140f01060206010e13020d030905090a1b0509040f1b1e0206040201110309030109060e12041511070f26030c070302010e0a0308070b 71
    0x7030350403400c0d032129414403048400034020505a8400713240c0c200c1800d80040d008110644607400003041c42d0400b14081038149810030064800300343c40d034006240043d0008400e960005240c8078142c1a945050070107500d41030180602d00e840d41905001903036144519507090381580d800381c80003d042d0520304005010040034000e0754071034070046000c0303142c0c0d0240d4050300d06140c1209503500c1d07030100c18950175100d0b0340c001007141790410b4550350605c41482c0c05115440301020390040b03045501d6448400203201200c004003014508070080081e0243d80c2d80000e56581c81942801d01e540d0581e840380c2c40500e140501c007010343d1700d5800c02c4400d50402c200741c1c10000074440440b00b111023500b40c1110b9108507012310300610b401d00345400c1001034000e1084032120720300c0400c1c8060b2500c05807660f0b603038054280e15401c038140e00050782120342000074910550511b0030300a0300c0a103041c055070501542c1c4a4559100190401600c0c00d02d91203d0354a5840000081d03500001c841e42c0e0b00c00c28a0414403401c0f086 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 269327104 1250 269325854 269325857
    0x80309030d0f0b01020606010f0e0315040b070f1409010324030309050a080a0f0c0308030405010902030c01090510030e010b0a0909020a0b040e0109020c070e090604050c01230306060d020a050a 84
    0x5041610480324600410b080703c1c0c8141c0150000345e0f141c40045516484484e240030801244c1e068540307490324180300c46001c00f1517140d003050003442c003800c16611001c000b81c280fa04200001110000c544c0e48488010400d0482c008115030390030414004070054038521403491800300d1b84101d540e002585208411040300d100361550004a580c8008100800e02c86105039141600030a4000300041c070004000f1071054070035424120000d450307440d201d4094108940854143c3c2d5644888000d6140410400100b21001d00c1c201c02120700b010007007404d6010003000780040c152075101d00c507003108081d0440c00310004003130180c0740203c0e43d400113040540070346542a40a508440780206841c0400d070115000c0c1d404003003a140040e403a25041500950114640100c540210100824801012107600340584880c100510040c1454201642443c0364400740038180710103200c15401040f5000910421401988a0f49440396a8080425510321400c81038a00303441c03000030f500108030740000c050001000103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 269328354 1250 269327104 269327111
    0xf05071706121b03011805030406090e010612020310052205010f062f011121090d120b130c080a02030606041406070b0c0415020a1a04030c080309030d 66
    0x7120144910302c014a4400406500010b2881180e51042c0355550b4100c1d00140001541038003400f441c201c2c44103c0003040b96603070000102001400d5000c100f000150074044c8a1009951510801510342c150407204c0910082d00440050140d90403400d10741d00410014000c40e00c2452401d1304451001b4044001c4200e0500d001c0010809a480c54800c02c251a03140d294001d80440829402c02c1c62841400200030302e10590916101d01e45082c0200319541e1340100c0f0541d2611520841c500c0c6e01008251038409140c84030302041507040c6c1c002120b196078400350070101c0001c0046641c0101400702040055040022601103801000a592111291000603501c0714481c3c0c5803540c0381400d03031009560040c1d011106020a010200d00d035460441c222400900d96850290999144058040c048030610714862012904011800c0c284019044104044c8040c060903152990b031888041d00e102d10010000803900c00040416000d07030b51646003560000055a100d191144000d941c0703034000322400d2282e504 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 269329604 1250 269328354 269328361
    0xa0c020d031503030503040f32012309031b0607080f01030302070e070509030d020a03030605060f04090207020f130906140910050603100f050411010e090109020d0f050717 75
    0x11034030420103080d01114207a0a5589940c404645e035400c050401e40d2180b545500c004e0004510941c9400440850a0312140e1a8030845c0501c2c000c68101e4407468041c1d050210010600c84409a00b1140352000b100508881c2c698264251541c010450748003000002d0104a006640d0b00041d064440c01c1c003640d450880e6614090340d11080b500038031005000d82e03c0f24006011142401c08002e034001c4141c80c200f030a168007940000d28082d50b804141c4050380000710024141507040c016100035080640d000ca26210764064100c060f446030f441070311100c5034003240500c21559100301e8241400001095965500c040c505000e00601074100200c1d08a442d064428000800220285220b81d43c0e074809403c40510070680040039000041c4403da260081c0341c0c010501c018a440383e8011148a036100042c01d00c0c1c0343c0b40166480c1c4508a005050080340c5004c2c00145e510f0410070340c19103015060140c0c6491640c10140e0240a43c0380a000f08142004100071240740d00ca0098040e0407410250003a0b00e48 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 269330854 1250 269329604 269329607
    0x12c0102071a04030e090c1c0204080d050c01020409050c040f1a0304110d150f06050609212d06060d08030105010e2d0108100815040303140a0c020d 65
    0x45180070050001a40ca000400e4400841d41919030003400f034200f10000c20050b1000444c115021200c0c0c080030000070428041c00400008502e900e0340d0510702c11440e16050030040c3d9952036610f1903080c100305001840018064081d0166801403030181d100780442c2c1400c0780040615080380c0035100301011030712400114038080d40c7e940021141541c1c50a8510385403503c031081c0d80b41103414000e4000f584085104005814104009d009030701b10400014403441d180a50400e0310300b284c0c4468402d0f40103004444440e500ca81005440100000c03920040a4840081c0b6040c040d0130100c0c0c10300051104440010786102080b4036030000280000e4a185d40d44036410003010030320500c40907064440520060100354010040080c001030001c00391051402c41204812405500e030880100c82802580401d501c5d5800034442c58100240c03c2c3c010009038240104207a803480380c89104180f04500601203000e0501076804042c6015580f00138100d0751030013200c03280280581040640040c440c0000890794503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 269332104 1250 269330854 269330857
    0xe030d03020a080402061602420301060807020f011505120105250504050409060e06061c03180801092604080705090a0b03030304050a020f060708030604110408012c0102 74
    0x3101c0b50300c0e072444070b407556001c0c0400c0c1d0300300405665403100b6251003070300036aaaa00c00700f0003000c003c1a8048005250b040c200350741d42d090382c0010154402803509043c00140f00d00580c1c0c10b443c40d901c0c1070940c55440714400c91524658000c1091554607010350f443c040e140c0d131403041c82610301c245c800b048105040300d2070307508807030080b83d00713002d881400b503003042c10600d1201c1220110742e103610f0301e1824980c50f01c00041c125640d02c00100d4416546085030440c8250030b0018541c0704008076840c0149a491241018002045603402420410000d051506201d2000780c07100103040300074002c00c40300d030701d502d409120840c1c02d0303409503601c00c00f88005040d040c448500f1241501c1d0150003400c142c902d010140705001c0c202500880145441c1c0d15100c81319182040590300c1540907500520b900d1a0070b00500c820356141030341080c01401c0400402000c29028000c40b07800c8041500c00203202e01141d00800f50500171504040d015500340800400401a1440c1c0b54184451010742c1c03004944138002100e01701e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 269333354 1250 269332104 269332117
    0x31207111525050405180109052a0703090b04090c090515040303050d0f151a0a0903140c040203090309031902010e060a050d0c051b0a050c060c16060e030d0302 70
    0x54200310202481d01c0e401c0d0300301c0b100182441c1042030030035860700005000850b000280c040d482c0c2c0d03500700421600102d4010b094005540060f94951f040e90382c0244040da13041e07801400300800c0d0015004003014841c01603c0014020403100d039071180c1c0c4440c04d10000d040d5140042c4002564002c000ca82450481c02c1c440c0c007001c00d503030004d190915542d02980c66401c100351074446a50f4500c0e4200b10010b0fa03004241c10f021414080c0e0b0002ca0409015005072112400b285200740c0c0140242c13160b4070b82100406040d01d402c06a0200030f00d8180d40d845160050b400d04090f0403c4c004400e02014580002c00ba06507010114280ca0240e15045034040070240c1c0300d040a0b00049074802d500c8040e0605a0091402100702c1c6041803500007110410f00540e0b03015020000010800524141903d031074901d07203018614010050824004243c84e00d44d5100d030303009512031040c440010075441e044001c00901c5070f60316180180741c08040d5510405000010b0030b808446c0a80030b02d0600b0303002141700b03100b10b914 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 269334604 1250 269333354 269333371
    0x801050d050a05010f1a01020c1c060b0301050403021c030c09050d230709110903030a03050c0c0a050601090612120e0f0315040b01080d0f120b0607050c01120e1b01020312071115 78
    0x1107215440385448ad8440507240103540c2c46648031801c4181d41c60038003c0b140300d80e00a400a01883c041009043d0b4410548800082094a44026010b5907503000403d8003c40314110303916400f1f00e0702403c0814202c0c1c1c0240c240e1820180c000c5100a02c2a80400e05000310740300d80380204200e051112050420b44140107000f60325400c04c200041c4000d002c1d03030085806c00315032907159003002d807050f140a10303240800c001500c00340d04c854010410703c407942c0949005130000800103a10f10701c00f5a03541c90003114a481440034440c5400054425403980e0865104045d0014116130904048040380070240380d065500f500c0c2c0803040300001c117009000003582600d507642d0340c0d658480a00c510104445102c10040c603108080d84411950720b480d9116009884a94040c0d0302401d0101d50380780000d80000c603800c00c56258903040c0361040041543c0402c407000074402c40e0040d05a2070412400403400c44c814000100a5058130400384500710b54031103400301c0c2a445080442d0400c51030200128170100e03045802d0305 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 269335854 1250 269334604 269334619
    0xf03080304060e1608060906060f01020a031d062a030702010903110a0b030103080a0801240e180f041e02150903150a020c160302010801050d050a05010f1a01020c 71
    0x1e0000b00703141d000c07aa851001409554504052000c083d24000f80342d0b00c140000e80c8000d0502c0002102880716a4003c001103410055010303450300040d4030748074016005070034070000246a600300c0142c02d426400441004045681d91a40d40c01029000d600e11200b48043d490361040c4540b9801d000411250f180b07405031207800c1003c2c0345640d00c00161400785159074000f16102170000d04101c801010794040c511550440c1c3d02c4d8003504030014a003140503400f0a02220005c04040b840840050154200314000d1602d10398504800001c10000b480083c806000344884030f04116030640c0d00086207000700d204014190310f5030080d101c8102ca81070b5080019500a000ca030f4001e51001c0400005c0550000c0901990a000c20441022200c00011070310401032540000341c4070308103e001c0c041c0380107000a14001c40c68040c1180c000800d003400500440740586000640c09080c00030801113080c40c1540000248403000c078255150020b480120840b0070a03040c110000039280d030020418107400080941311a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 269337104 1250 269335854 269335861
    0x1209090609090106031b0801140106140d020403020612011d090606130905010f0b011202030c041502160b07140f152707170d090504090804050d0b040605010f030803 72
    0x100e007000010340302d54071665071042c000000884038031003655080004500d4690b128903214a40342992520219603440001c3c4000611400da004038219203a1000485d03040d49030081803600350020b00ca00e400c003a500c22808204001d41452038050b203410b0341d26180e03414004500a152410b0160030540b5030501d02e8001900148180c1821001140740059031100803801c01441c1d180c044c00c44080703030400610280c641440102c0d030350700700b038002070540084a001c601d580380445c04c0036807030700440c021b2414484080e4203c6e000e15201700300441005504d0140c2038111583c400300286594000f2038100d5980f030f101c0030348030240c100101d04d40b062804400060011058a24000d1210001c02010741d080c2c50884060074448108220006204050100c000c03c80c941c18100703600c0351780c00ca000202c0840d50065141042455201c0310500440c0c400b075902154061803444d10b00c2241c040c03078000d9900814030080f6034092181d412a070302c0c02507020350030400c0140d0b07c84142444811312404054903406081011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 269338354 1250 269337104 269337109
    0x10605070b1e0901090b01060c0503070b0c13080705040f0603081219180203010e0106050d030503040213021801030f05090717210c0c01090609090c020c1003090512090906 75
    0x55000700540b040b40003858548005a40c280400d0303801001e103a40d80c054410030130044203d40c6014101501305a0541d014580c1c40035540c1c03003000c80080042c003c01000c20b5010100b0000e582c5040c0300384100e00807458030707182d0f003698514061094901c910b00b04041c4c222030340c400f40700760400d80f6045200c19242c5981004c400504010141040c1032408a9101c2841e890007140f140702e141542c0c0c0f81d0240d41c02c800a004040c2503c2c00f01d91484582e924010003004241c2e101601564500e5140c280583c49550354000640a01c501c0d803400c80085000003041c040c081032503020244450350980701000380d950592404e201315201240c0c081c5041d44682814450303810001d580b50049606202120020001400c0d10380b00b4086110700292090400316080801d40c109100c144880c00080c80c22110b25450043c00030b140070003c2c4580380c0300b15911032542004603c2800582c0300103001804089180c001d2080090082c454543d056a00f8000c0f1908820501c6110046600005009242544d50707102e840c01c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 269339604 1250 269338354 269338373
    0xf0e0103060b0a170c010824010c030c1e020310050106090603090501060512060117030708180103150b09101704031110050403051312050a080318032a0601060507 71
    0x91a907401401014006041c05000c40c3d000c442d080540c02600054001100142120701c0180402e22301840c4080c11f130700c00e1090200900b82c3c030030003440d011404074403904080e6442c00304618060300b0b140100f000008100002d0f062040840d00c01c1d001c80b040030341302280540880b07070207015000014a040c101040070350b00c29041460041c1c015400010413a640700700151040020b20042d03035503038105030010002da14078803000004e0481e00001940ca13185040c2c0d03e44250380714407142c40e5184107500141c1c004a0344203600203a00ea190007014501e0140c3c0b150041c5000703400080069100c0c414240440141030301c80c40150b22085c1d10501704070041e4840c0c1e5400c0da00b0003442c240f11a07142c82001c4288000c03502c1c0340103c500a50098444540d110b00c6554481074083c6560000310fa40c02550720300c00c0000e1000540228580e4125034190385a88030301070071624400503420789100c02d110100f030b4540c4600e007a400c10b011104280011400700064140d94944030702d0248604801318009001140c085145040c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 269340854 1250 269339604 269339621
    0x70210030c090b0c010605041d03070609060603050a0f060b0a0509011214030301060e030d080708060904080f040605190201050421140304060e060903030123060c0307080a090f0e010306 81
    0x200b0707040007625240f9201454002000c06280c40c0e448440c00c1000d400c0510a00541c4400380000000c00482c08035495603070721862100130480c0390760b80d1100040c04515400360018590090559004041a0801d8240c1c0001114141c40e80342c5480460300d0301d4a8103403003000440343c0c06812a030403030786041c3d8880f20f843d14030041961201c00c0c000351001a124180001c50281c651078540c2040861b17428141450003020542103014805a03400313110045070082d4420f40e1005041f21000d00f503039114a094246400307907001c5859250302c04075000c20400d42042c0078240c1000941e6600d080c14202503422420f0319019a4064040c2d01217213140103008080d5914441c0c4041c1c075060403181844c6503580c1600c1940201d400342d4500d039a40070800e80390034082c800a6004940c5000450455060242643e800046254091200c440281e10318005450360000d4800a12584064a030ad540c81420110700307075800305460400082c846400407441040c04c128080654400c4031f5407c00071313800c4d6a50321300141101c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 269342104 1250 269340854 269340857
    0xf050409050c190e0901020f03010b03060d0c06020d030b09071b06180b0718080705010c050705211c14090d0f060c110102160303110d0509061803070210030c 69
    0x181c002c0e500c962920102c000780700c06045403034080b0f90314008200018010282c450401030740104081d2020195000941381900d1150010681d2900c46000207882040c1226005102001d21200014569004240907021a1081e101442814400000c10081002c215044804a081e40b1607000c01080034030010505070344600000203880101106405115516080441d1b404c42d0302070401560036400000003090340140d028040300141440007003520741ea40c0d401880c0c10090b406620f48240281003103440000c140c060060302408000e00c080c0f01e280281301c1c00040f4103114007001a00141c8003241d80808030070042c3e81d01b211000704912031104e1a4000480250311103c0750a0110218518240c0201c03400d2098500003905000c1d40b00180c41c40d0a113204081e400e92041c0141d2000714446c055805c01251b2501d4001500003005121200d2402500f440d2041c41d45040108000d014001070518081c0d1050704488030030014101d4207907500e22030450700940000b0403040b000d940d1130090b0801039100d60f45 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 269343354 1250 269342104 269342113
    0x40602090d080f03010317180105090402220f060504140108190c021506030a110d061104030302030a0e06040308120901020c0f0102220b03011406070f06050a0f02040f05040905 77
    0xea4541e40b000d038010300031200e510300001004000304098020a00710405d00c0d071610908120303410300011100e51400c003070103041c0500098071140340d50301d42d030440300b80b000204107100c41c020180861200208090090106030315000a001c03610074010810b88085030b440c6803150030010b018000454401a001d4000040203202c034940519204580c0912200c0321000e0b40207100b004000584018001006000d003402a000f1a41c510003156180c10b0b0380191000640e140c050b040b90360b2801c0b00003002010382c80200f4850100e00407040517030210041810394401d80e240006510316008100300b5114520000304106030030003040e0304401e110124564000b031440300050030004402001401d2100640100c0703140d950008500c80d070406250303023500c03082c54070b4421882628108407910505203c1802800c80b8400740301200989581c83d0070465650b10381c0030a040800003080c0c035241c4054442650741a405608004110004401e14401c0d80c0131204080b0a000c074992500c3c05210041c9060801520140034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 269344604 1250 269343354 269343379
    0x1103030c070302011b2f281a1608010e0621011e0e01061203120e0d030606030b0d03050f070201120504110102060a0b130e030c070306020903070803090904060209 71
    0x2481300ca852401466620745140c611003844065845030130f829081030028240c51080003c4107000103024289400800c03003078a2081200c0d10340c4d00d40140b448030041040b016030381800c2c2c0e481e869102627401005190301d2011380e458040f4068400400c04d02a100d020240100044d1052600f6000d8014030000c91140050b4020103845036429980110500207410150850ac0141c00604d03114900500b890b410081100781d040400201c52110211405010002c0d01c03d020070042043d07910000794040f0b1003045508401e01c0c41c002030041e0110344600d5000c07902d0501e6075181c9060242118030680d034103980d40303803801ca140d80c140d10352608066410ba04101250442c03444155007441f41d180540c2c024181c2e600c05027040000207142040041c40e4009850070700326038203826100c0c80a42c0310303001c05030b0b03802182e004050b0340d0240c84c6024200480c0c8080c82055000420300c501e0350300038001a4026401c2c0c0c2c17070440d00d4031011642c3e482084503194125401d00002000b0030f02a6000e024076500c0102940038125 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 269345854 1250 269344604 269344631
    0x50907080f06060a200304080d0305010302060904090c0b030a0b01171b0a02011e02120c16060b12150106020c0f090f070309050d050315010c0203100e010f060f05101103030c07030201 80
    0x120110f0b03017844160300c005010300c02130000f00003d5910790194a024800340d0b0442d80030451350f006101c000d60189803600032900c1008410058240a803006032800b42c2c0b81d1034103040000140c044030003c0790100b02441d01d0b6481303140360910014801c0000c0d03100c0152035600c2e5119841184d04c110310302d000f1550b8804098540e000d80d1601601402c0c42040051789954203585402e603008006000e09a10007003c0000d035550303a10301c9006012854020000141c102d11460100319545100d80c2c010f0fa1078002c81c1241c107800160198a10b060320700a5080f00c3e04114503400b40034420f85e00d5000b150340101030b0400143c0002040540c1680181c0c82c0c980400d8000c07540e900d0610340003e120345e40012880c00310130801d0b101c0e04900030611100003483d0850f01a2460f8010030f445a030200280740c0410b40310081c1d0b0b0215107094000803444011644100b0909540315011550004035008080c0704171982007002140300d200d500181c1d0101c0324440910318645580c5031300c0085522024044056540f82d01d0640f1508 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 269347104 1250 269345854 269345897
    0x4030f03210608070305070602151b07020d0602130e1302040f061502030711060301140127080d02011407022a130507030e0a0312020a03110c0304050907080f06060a 72
    0x30f0007900d005264107401c601d00760381000b180e900b05404540c446180e032211883c0303511080b600240f1040401809a05070401ca02c110b201e003101c06504510100903460070410140d00408840c400074620501040e10744035031454404060300c642441c04000000500075140982c48100c0d15000f840300042c42c2c0741d595401e180320703246d07824902c0090f0304042502e40a010021072804504801291401d10f1581403803030344141c1c00e020f50b01c12410018810301200d041032910001001000d1281032041c0d1503035441c41d03100e95a0ba80c24039040010b508041c07c20b655080798610640c0150405c0e00540110a21040319080705004210001458500e4000c201079a487d0400c0000881d4681c40000c603c5140a08018041e28000c81001080c2d80c44070b046035020a40c040c0c0c0d80340454801d60000350740c9806c054400c40281000b15034680c0034400c0064603041c60b50340040100110340082c2c0c0e413545140d403842c0381540c140c030044070b403507903003500a000052551604100502da007092500b0101108903c0c0750140505 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 269348354 1250 269347104 269347109
    0x30604110c010e0a030f020d02030415020c0a0f1e12060b0a0b0d0603120809061b0405150a08060a1203031d0a0b06010801090e190602091c031404030f032106 69
    0x5038004040400505030300111951603d04070340010101c0d02188c1d10025964030071b52207800803042c1e2810900c0d07011071080c80070400c00030006150010307003038590380782d101c1030310617807082410140580150180c1c0c1d03999842c0040c11215400d40540400001d902c80380040d060450f8a20362140f0701d03c001182041d000030103011003034055a40002c00d0350071460070000803044006d004041c0801d400400a00071000944140d10542c41c0001903000c60068805465900a540100b50b001031421f80b80c3c0d1700c00d010300d006071200400c9c80d96958a1798440b00203100004080d40500c0500c400d103040c021000c20300070342100e202c840700d1400d22200310340242d03000d0307040403001141101c60040c0b0109220456910000c02805880760b80d0041001140082c911030307641500380030b89243c2c0c10503000400d0a11000e581a20500d45002c2c1003403413113818007125181d52020044048000c80d2041703010042140c044410744003503030380c08840f021022010751070a44841c11000301e00303108c0c04030340030194056a42d81e0103401c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 269349604 1250 269348354 269348381
    0x21b0307180605030c010c120e010e06070303091a01030c0e06150301030b070201140603030a08130209180609070b04180603170405040f1505060705101b0f0e010203030604110c01 78
    0xd90b181401c041508040c62085824100040090414046000e0b0428981c070000d150a1881d00543d03c8401078800e100e41040c82503018102003030791000e16406800243c0b026104111155a201010085003502c580a000142023400c90340d6052240d4041c4445a980100d0002c3c0321140b0484070441141c03040d4400d810480751420200280b1120507024040c90b140c44a00e10400a401d2a004000c01d50702d000c0c4903200c0c420414404042005a10b45440d4149180d030081d040c1c003464901243d00d07024005900e41c3c07200c2035100b910009101003001040e078505540010000616092600c01c1502800003003142d1244d01c1d541d100d800000180c8000d0488007101f100e58050760f2140d00c2c0c001008111006014500380160414080c03598132590801d0301e4095880c100c0e500c544804082c02c01f50300c1c01d060702c0e4001000c0d5240210761300c84001c0e8039803094110765240d651010440241001212070303000c070700400381c0582d0042c004294189015040502260324080149040c68a44507151f400d5a411014014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 269350854 1250 269349604 269349611
    0xd0510110d05060a0b090402180409080309070e01060923030d02010618151215020a02011401090c0206011a090a120b1b180607140c0112060501021b030718 68
    0x7035203002640980c681c020011500390401d00c0c43c0106040c42403080341816486558000f641c11400c030415002c1143c00035005c0c1c0104a45a01803070090380990058a1070400c900c5503500001707a4200028400d4143c42156940ba41e08601d040a0500d21055110313102d40440c244c0e005d40340c980c1d20304000038183c2407403c0c0d0011410304c2c41e105d420380c07105901c1f0b81c1c45526281040518408084000503030750840d5040046803080000a06181a4000300060f462032064000245003401c05e5054100194010701010900c1c140d90ba2602e4030700c22035081c090840301681150004202c4c0181010080c0d840544c1003107040c0c0f5240101000a00644160b00540c4100240340c4034801400641c2002036880780d0041c001d0741d00072140124060441c041e180081191004613000109103845000070303500e03060307485003035040e400b00b803210034036180c800a404050000300c4203d212180740400b40200c1040352410303005440c0502c0c0780e1002c0300302d415220742c40750f40602c121000010240c0c1c030500006284000d2070b0002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 269352104 1250 269350854 269350867
    0xe1c050a0317060604030f02120102090603010b0301031712071124240901030f030302210a11031302090606040e01060203040303300504020a210c230d051011 69
    0x60b28520240030f1030b000e410140014000100218a03084036543c0458a210050503c5401203000e40714403030205400c20b8001c4000070f082e400042c09107068034410703010340380580304590402c0b90380c2c05000d580860107035440c4041180f46004d104d0111310440c2c800e007981d11507164655850360381c02d111349100b0a0708281c001003001c960742c90b4104c4005040303800f05410003000c42c4800110060810702000d040d8420701d150030020103020303a04881c201021101c94914a503110b0306d400581600c100c4e42d0440b918149514140b9140c1d5070022139106100c40d0b8054110051250207001c5044d000400554000104010210390b0b0604807031541d000b40aaa4001c5643d9030652034014110f07540c217003100740c2e11001005600d00c1c0c10902c00501d41e2140300c0f1103002800740d689000080c1303201403e5028903c60401680703a0f060025810f1610601c6034050580c1042d016a26920040035203030391034060700d0501d40f20900740140c1c50f10341185004a030040701283e820751140000e0808845003030200a803603150025a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 269353354 1250 269352104 269352137
    0xa09030605100b0a11030c100501080d030e0327040207060603170c1207030c021503071107121202150f0403090e0f010918050a0b250e1c050a03 63
    0x3550b602ca03203902c68070303010789160041c984054082c0f0407405050290000f041c48981030104203a1700808006011680a034080c1c001c1c51008000a0041808034098200e044145500070702603a030340c1c85464130055150a003070700342c0c52000842c0a01480768414002e1a44074072036132140041c10000c0e018800c00201c40303156140000c02c60980c407580220007141400380100d00e447c04909400383c60f008900865030f4080518048820101d10310000354020508801d10004002c1000950310074441919a914552031a1104690f12001c034425917521100d910340000020381c1aa106045040c1240100d030803107203c01e43e0824000404440b150500d81600c4204810b00d0f0b8032103c45402030100000103034450400003941a16a0014000d040302c9a44402c1c0c40410f0786002c81b00709160a0b001070643e20321007564038096034402d00640d909202031903540405200f07089100f241500c802c1044d103030340e40107103a85070074004400e180000c6803038814a035185600110700140055030f5540c0c031a80c1d5a007801da060711071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 269354604 1250 269353354 269353361
    0x190e010207050a15110a0803010905100302030a20011d1e09010e160c0506130302121b012319060b040803030717070f03050c0d0606020304031202060c03010e1b0a090306 74
    0x60349030503440306c8101404512800d0489064483c0b041011581c0d5403203000d4403081408540c00207415100e40c4030f9200070310040006000740c109c03800c07419400500401004551140081a02d0b80056010b184102d50615020484011420881781d01d1400301500f40c00248440da8260b1040e05c049006104000c4903521520900c08586002d0410b00081011030311016a62800180002c0210003200820820b06000f00201000503c1c0190555900c48402465102c1c4c03000e04003a0300099820034422a0032121200c10311807072201c40c00c440320059514191681c1002071105185030200e60385410100d40030703a0500081c4042c008420055949060091008042c11204001c000800b040c050600130121350046200001d80103602d0302090b40d41302d20004001c2d40c03140461344003d980ca040e0303000a015030080050030403240180010b03568110404000c2e6255a4110b0300c60300701000410041c01181c943c1c41d04241c01400c10b840109110004280081c1258400701103031000c5548004204100800c900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 269355854 1250 269354604 269354627
    0x4090803150603010b0d0c0e0a1d130305091302090904121704020a06050a180602060103051005101a07021815010207030206030a02250f060501050303190e010207050a15 74
    0x1251940b96614203c1d01e515070307001e404444500c261f101d13900d82403028881c1005a004000040031391030010741da40c44c0014000654070490f000d052140c400102d00c0300300442c4002500350036880b810f103410b004108200380300d80304c0b035038041540c1c0d402d001030f230880d0700c83c00304142c8500d21503280802e41100002c0c02821701e03070130502d219a00c1181e103c100030060300c464205004035074050810035110028190b05443c3d1140a2007040305e1a00f27281000180749500150080c100c1c0c0c001c00659488032101000042965801c844035050f480807107a00304000d0b94000e28416039032a00ca802c89040000590010341d00c0130740301c41d003040700500d18014810740d0900078100001d00b0100340020305002e4515030100d042800002c0101c11030a83c0410301404d0607400e1021074060403141b0b9052403070442c8038a00200300b032910174010b6899924000c0042440e08002046820030b800803c00741e0803484c4103540c110b401e00507103820a811400f62060000d45c90b102d081032080a030030190243c0e1a14042c03000c00800c6140b016 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 269357104 1250 269355854 269355859
    0x72015090f0910090f09061118060d020714010b03070503010612080c070e09061f2106020c16051806150a0912031106010f051e040b0409080315 63
    0x410035840d095031107036028480c0070800d6a4000d031983e1030b4156901e02c0315056112801c5a418145d002c00c2020040c2e02c00441036101d03410030042c0c2c2c07100f0702c0704204600030211b5003181e0025031266840c680c80d014003d04445403a0040c058034103025580c0c0c0070755001e40e2100510307084c0e442e008200c0e800c1c5001e0208901070142a0000c00c1114609031440c5440c2c01c0c0160080e00c0310900080d11003004805024100180040e1040c64909003003a4040a03500c1c203084a64030303400045980703100101c8104000300c100b15856004000c00303d00b00c4001e80032014546a008556065003007280c00014601405000a020946617004003c0c13071420042c09188a51400804c074203c21040412015640da440322000142181402549800704010140e50041003130b00318501201e003240301c1108050b0700408c0001c5881ca0711003640c0c040d03640c1e032465540f14025402910307405200d0150060603411000200901000d00400200f051200c00340400c0c110384100384160b0b4040000020403400c080c01c0404000ca18100703 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 269358354 1250 269357104 269357107
    0x50307020304090b03010209030f0604032c10020a0215040e31060b0415211203020c0c060d060806091207030c02061b01020409060803030c120705072015 67
    0x144802074072845079016001081ea44c9100c000d80030b032001d6054440416000e01200c4072002000072082d501c0d03400300e5088001556656007040040103a40b0515091100049501d0944413080104804d004011908404610406001c03202507980c5100d00c81b00d5818001286a880303042c445a114030820040c50400304840309202c2000a000712071902d408060b0700c0c88401241c034000e02d4064003405d000f40c001580700781421480424103241c2d01c1d00d0011a00344504452809603004104c02c03650807500400f40c442c100004842d410303a80681c008000b004020710036180300e51040c0000641d43d03003000440c03003200c55481d0414030a0200403c04140c204c243c01d0002c00c1121a42c143c11403940c46035090040401600c102008115200e00b401d803104100e10a4104044c5035000749603a0003500301d07106404020b82480e40c001903101c008001c80b4001e0803901519440c201a00e2801c03160030030302034808401c2000400020700400c00340c040340383e81b00f07214105c07a03810000000e0030864074501500910282680 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 269359604 1250 269358354 269358361
    0x515280b040b031b060f0c07090b040b040e210909010e0901050f0903030604020703090e1302152a0f0d08090c0108060d2301090309030507060305160309021306030303090c05010503 79
    0x1485140f14413825001c849482d5110410002240306e80140081d007290703842154030108400040f0340007290201000d0b20100904100101008107980c032041d1001d0b12038101d1004605060218507040000c011078142007450a0701400c040380400c00240d0209030b035121040c0501000074001c1c001e10350040c0d50100400f281b810140d50030752b12884080e0400e441140d00242c0c0408040c01108224000c06007442088224a407008000c03c0506030800124446c072401c1d046001c11842c8007083c0c5282036004160718034001500e07001c0d1041303110100e00300641d0b4030854200c0c0b401c070300b03080113044038814080c0d940e0212818001466841c0021f000621414041d04104002e50b6031911543c0c07003052a0040d0001c4403005d0300001011005c0d112105400300c950800c2c11460902d9008000c031000c613485901125a01fa540741800c600700c4200340c92035807202d407449100c10b00881c8290400c0781c000b80000c000036800e21611824800f00d6065500407030100b80c40b00740c075178203000c0b41c074041c500102802e0170591304d50314 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 269360854 1250 269359604 269359633
    0x1303021e0705040903080601030c020d020a030309020301060e04030507050105010f05130b360a0b01090b070c1d0609070f0f2006011d0703090515280b040b03 69
    0x4036010021030600000384810100a40c100001e100402026208000e00b08072410300130b0504400311180c50109003070070640301c0080d08c0001d106004880950180010001968084024240068050ba419902c884021940c11a401d00603070145200e51030b0141d803403100d49011425554144d101d87c0d070344903030071104106684400d000001c1012110700c0c00116034440d500050181c604004280000811485104e0000e52076825407010b0042d0000d005c400a0740e86000782c00c1911000340e116400207020080400c1155050b070013a100c11442001e540c0502501d5001d00180546008603048a00c11454148001818018006034000c0302c545890f080c109041d000c00703441d0404000c183c0c1d041200c01080450300c0c04443c0305132502c441c00241500c52650b0b60349a04400c05044102c0c40e0074040c81d03c0041802a80203200750228240d001c4040c1580e18010b4191a45043d4024003801030020601100201e180c508a078000ca001c0c2c0f1080002030350007403d410301084844e01101b01c0e010f0703480a0f60024586 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 269362104 1250 269360854 269360863
    0x702060702010309081216090801051902030714031512010b09060613030204050406050a0e190305030606040504090b101e0b09030307080c0f1203040b070c030e06070303050a05130302 80
    0x6075028207002c1001203052800c40110310442c1103a1101d40c030f480081c868240400491010810282c0c0c0d41d500c8540c0d1103440c000d00b01c403411b6a8052070f410035130745004c20000701500a1580000c0c03d0a04500300c202d80c200c0b50685501c110303014241855030480034071039841c0c0781d6406042080c4400c020010046c1715000704403044405131032103221346000f20303401603d504185181c1d009168041d00500040c01c09180c40c02c00f524060311111002824104044100b200000740f4481d00b19121480610740d1016850036103041e8409005180c000804110124607601c540c0500d1003024071444d446c40f0503141c0f50001450065454001200c41c10b10180d84203501107019000c0c03020344543c007071015aa400d0010000380780d4070802d0070040041002180c5003030990740205d85450402040400d4a0740303030483c03480003420341c44225401401d10b04040080b800a0b4130072621960450b1090401c9081510400005070207500f110314102d0000b42c880080001d0740d0741f02d0045d560454560400a80548555500651503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 269363354 1250 269362104 269362117
    0x9070608061c060f020f091002010b0105030a050a060b0f03040302010e0304140405131707120203030c1602120f2d030304030c080904020d06030501050f060a0512030d111c02070206 79
    0x40740e01c180044028083d442e40301510a02c50088215540d4641030089581c41e0485200c05115100400340c43c410a401070050301c06200b016036509185580c0c134000707080180720241900e150366070307201740101e035240e1800c000300188810400740a4580c5040c3c03400900352900c0800a0881d60002e11041090741d8030400458141c400c221800705181d91a4200724a0094401601410540c10045143c4c5003034458401071640314002e0740d2110320311402890a03a5244400d840115085000f003040301990041850303031034817662009095407010129000300c24681201c00c0b0900000703400c40c00e000803502c0c803214034440c0031400c041503c4aaa0710032500b031546901000300040c003440a01c14028081010101c00c848401600410854880c29142c0c1d41c0c200800391030004480541c68180480ca46070600000e40e403240304000d152001d0141007009000c2020003aa45100040c8001d00000407050f03014005c000f42c0b52124040b86490310104035074800103811400e000035400c3c0c4100041c50168681900b1640c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 269364604 1250 269363354 269363389
    0xd0c050c240c19081e040f031202030c0d020c0f010806030a14070308040e0f010504090b0106030f0905011812080c0d05040309030b150a090b01050d0c180305060907060806 75
    0x49400d11081c0e82824404824a4818211030711807030302042041c03000107094200300034446011150490700729440d41b03105038006c90f0b41c000c111b90b03130070000174140b854050810801881a20b09049142080d145007085000f2820b000d03070000e010741c840300d0400350402c046a0000b46070500d01410084017180d11941e06840250540f011206040c111100803c0404011944805610b9070b46507180c6c0504a00e400c01d680b800c4000c03031002d000003642e02d050b0007152040c5030850700070b040070303441c1c100c094005080c182004480203480e81305805c04074030203101e21100c00000300601c3c03509840074940441503d090820300c0081c41f0201e0b003400380c044003050036641c0419039110005000d40720f60a00b0b0320800c2c02a40000c010119080800001c507076031441c5c40400001c03d80300b0010154a400c050002e4890110341c060001c4c0c0c003400406029600c582100c4000040c9040007842c3d01451611001c00c204203800540f01380d4081d500f48030000380c0800007540140701a1504202c68145070001035502c0178071102111 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 269365854 1250 269364604 269364607
    0x180405040204110a083c0402011407050c0f04050c04060c0203120301080c0909010c0e040f020c0d081501020d0c2303030703150803030907060c06020c0d0c050c24 71
    0x28215101da6100f0020309040c941100e0f00d991004200410740f840466082000b601080700b002001040e10031a40002d03603e1010768a0007100240c2c410b030556038010401e9040100f00d501c03e40c4251050380c0200900c0b4016009881042d4420b8144004000c13107169844c0250b00c0c0808204985038034200381ca003a58014078080c1442ea200c1e0000900d040203025255a1302a800000060601e1340000d2000b9850b405454601042d5200c030302c103a088a220882440c01300349102034020052410b40e0141d140100445401401c00e104d8014243c903210041c2200350204100806004080c41c2013624261444070910040c041c0380840e0310001c02d08000900014504580080d0728111a102e202006990100e041c0c203d03505da20705042c005014016070401002000d0320800c010400081c0801100c0c070819002c030060100601c2c0640c22500741c1c410002c00d5070700a030700b8480a48051010300000101014a6482d22b0840140d8140142864004042c0a1082da0407000e00a21181428080f9011840906929 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 269367104 1250 269365854 269365861
    0x20411070c03120e030616110d0f200d030917071703040602090301090605160201091e0512040f050108010e130b0718030f0c08030a140d0b190905090102180405 70
    0x64810403010a1308550602980c41041a01503d486110034104025641c104008420911b5140c0790000103115200081280c514001c405006d0048040b4100c0d07021011007098a0140d60603042405100c080c00019031a125640f09001c0c2110341640ca02030000003081c50810b955603440303842540006a85810b01d000b100181c244401541510b04010018000b801512454500f460051108441e900071104110708003900d06031052203a400341c50b41c0000d00c445c0352031019185013070079050381104070707003c0c03191110040814981c00d001d00010408003000341c00721800c2c14005444000f058220145000d180b400b085010b00544450400064001c010994181c40c0c04204550120401e24203141100c40100000104440d403c52111114000c3d51441401519080206c2d141d100f00c50030000000d01500a64014410400040c10b2130301300224001014141c8101141c001c0c81040700058501d621900b0811a1118a01905a00c910001d0003140340c0f5445803001c03013020075002c18003400b95a075035001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 269368354 1250 269367104 269367107
    0x2307031104092102070909020a0e060f0307060504060201050a0207051c050d14060301050606031b0f0d050f04030914030a060b1c200d03080606030403120f0207020411070c0312 77
    0x3030800d0f5040040300e8007040244034041d000c0c00030141964010300c120000054a03926501c90b2101c2d003a8010b00040509151028044258a0207092558080c0d103901c1e46ca06e066a041005d4002010141c8500d0b454518020300a42120ba0007002280003e0040040d83e00041c030110f40341c41c5110840203000320381d000e0300d0412100d41c02149000d10382d641c681b60300d011a4009030060b10303106820480080c0a1543e034402802582d0206a40c007010300600100c1c10048580c5d02800380c100301c14111a10fa00300044034402000380d410980380c00700004168400d00c02496445290800a420108081d0401021b0358010a40c0c803a5003603406054580e1f20315960240340c0c1d560b0b0444500c40b40807203001c180c8203064240884142500c10203e44104010120000d0604100405201e6603401d51112100d40d070b61001400402c1d480104102d04202e07c42541c400743d450144240035130038501c10350051f11034050b44140300c02c8a4050008084041c42404413a0000f40800564800da07580140b08054075200b10340d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 269369604 1250 269368354 269368361
    0xd0e01060504060603020c01061d130809030307031706010c0c06030209010306150e01180b0307032a12200316020a1a06040c03020c10020a0e0303070507032307031104 73
    0x20041d84241043d800050283c0d15401800108080a00800c14942d42c1e914000b000c030b020340f402c05291034800700000c4191300c1c0c10b0400f0b11414028034845207010b4105000070b00b168400c1d503044001c05e180110b002c070290f8294003026071080c000c2c05c1000c194403140d01e40c04804051407043c502095000540c2d1285a4400d4002c40c00400794000e40309404250107401a00d0500d8a400702070000754825503030405408110f2030740c0b044420444150b4610385400380220060400d0314234400c90340c2221120040310303030601281c840400c001c0b95201c039401e800d10903041c0113440598041c8100300c45031814444c600b544c1c01003206e400040e0010060300040c0c80c100c0590400c16250300181282d00883c501c02035000d14114800d1103440b003102e080041d0010994158102d0282e002440e5090b48000b13840800d108050b402060040c40c0c83c10050940e4441a0000e4696840b15a0850300c940148a04000f003140701349002d0346002d501130518040c0a00f030f440303a079500c036103920001d01039503c118403904564545a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 269370854 1250 269369604 269369609
    0x911030a151e0e03090f0612040303050a0204030b040501470d140a05010c0807050904050c1303030203132403110f0301080a0b010806010b0d0e0c09090a03091401050d0e0106 76
    0x11001e000c80343c1814186134413600480c000600800d14101204000d1500d2405c481c004051301200c0507141d11191400c1b0010300c001010f44c0c8920368200408001b166110781a184900e214800204505251034503c00b00381d01c200c0d5860154003000b040042c40c82010529090880c03002c18901a408032415000031110805444003401110100030b40d500301c540080740098055000300c0092002c10034000c8110750840c02200c041c00000d4050061103554034080d0407207030b007010030303040030600f0a26545050a102603441d84202d000d03a1001072549a80002083d8a80c004c02e80e403c0f29001411070b4154840c1c2d40303031011701084105959500c0e510400e82d80b03030f41a0342c01c2401c641c6079036441c0d684465003940d80350907003042a90342800c040f000203803904c40007030014142c441e68a159820207448202010240000140c012006e0051050443d0943c58101d92140301303a41600040409201500780a00a0300181e00005100f2400d03441d80c048690708182107409000403024006911281d4900183c0149200d8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 269372104 1250 269370854 269370911
    0x14040209061902121305061b0303010902041d04030816090312090323030405040e0708010908120a0c0203090d06090209040804080723010509030a0b04060911030a15 72
    0xc074000306084480c02ca554a220700c960219030031410f00d01451851801070000c500f120091110040c805401c08801400526088035045803484c1181c00040b03045400c02d81200080a9010504022807008415040850204480c0c103145504040d10020980c4000820030a2500b2848021704103840c41a00010011034028107884038401c8185001050404540300a950000080301d15102c220f42c80c0440c1d4107a80e1203031000354075292400c1d0a000190980301d403103070550b00400350009013104080c0907280c0710350301c9154020303500c0c5a001140000c0ca64054000303800580b6004544c0312844d00001217078030bd03440466007142507907032624000d00640030240c0f00079003208501c02400200a43c81001d40199450f8030142c409154841e1852416103210541c0300c0d0340c84540190034101540684000c102402003e020707560000a241c5036601e242c44181c070201c402941d070315242014422502d079224000c2400318040c01c50550683c9821441506846c891441e035075071075041c48003420404040c000142200d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 269373354 1250 269372104 269372107
    0x4030903080f0403020907030203060d0311010e07090c140a090302240c0f060105030f030904020a0306050a03051c05160b07110a030905150310090203071404030b06180603071404020906 81
    0x2100b031214240c0c1162008902074030f4540c01040e6464000d00a4901c151406401c180b005046501d0855a080070a00f00c80c1c81556181403007c0080801d0100300c0c0541003501010440c4dc1c0c0c050350041203030130107800100c001d0609000c1100601d9120410344203c940442c0e4651075011102109880b08007c210480001d0314002090481d0800109414480044660035903019a03030710024161a0060700004000d50b8200300318502032460180d000c0c00000903645400151309031241e000c41d00080e000d400c01e4815601c662003018807000302c408001202c1e016441c2290904981821b020300c0c051010000805200c070000004201c2031090f0072506520958000316040754126060180100b5100d01a060003601e0440d42011000412000c40740540305610000152038076255424000f50000b600490420015000e0300c840c2c0b040e010042c00180d40a4409034059013000760400441c1605440203604c40180d460400c0794545d0042803440c04c9a90440002c020060384800080c000d108004450b680b0810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 269374604 1250 269373354 269373367
    0x140c1507030b01110c2b0203070609080d050f19170c040906080c0603040f060603020306191505060d0c0302040306050c04080f060408190507020a14151801080403090308 74
    0x81c19000150700400a8035002c001c9481d4a05840d01c50000c90420394020040d5038980840d090075000b02880111285018682c0d000ca550002e0b06080042c3c3c010780001d5100720040c00142c20511040841d01c88505055281910a052007409406407034100040c48a5011003880c0280c010580d8404085801e81f410303140d441c080c0c107840041d4025001d4409064981030300070030300c1c1c080003400b8420743e000101903600303603a80d40e40c58108906040c0c00c1200d1980e00c512002006840411115018040a03041a02d01c8420641c1400488881d8011502c42c2c11628000700500e0b02c4603411503d12813148000414040b03100a030640191185e40e000034012881c041c10001010500c0000c3d1042c3c48210041c0c2d02c205a00001c1d0560704d40e8141d80c040c0c8424801c00c0102a034444024038603020103040e05066040c6406070300001c00001c1c0c0c2c3d0b40804410403070056080294601048030340c4160000c0e0540505120006000c0f00400c070302218014180074010001c20181401440303000004e65020703904a94512 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 269375854 1250 269374604 269374607
    0x10906060906020718020306030f0607080f16080118020903120703081609140d0f0302010b040510030804030b07020a0507030507030b060a0b03060409110a120507050a0303140c1507 79
    0x1185106500c0040d10079100419258404034003041103c5c4151803444030301d130703007851204000c0d44040c143d47d601d07100f801407800710341400307006d5644905166118000c203860400d81c240016000200b1016001403a5040480d001d40c1184419040d42d0554194002c0303000072118400003480703078035226030b0715200b48041610035600c03000040c841030b403003540c2c1c0c42207a490b080131281d0800050b803010750114500d00d03400c0c401c0f030071500190964004003d024907040000c54580c881e1804c09034038182c0c0181d44402042d041420070307000daa070700801d044051495031807640d15030a201e40514000100000400300108001510801c001b0600640100581d00c2e1940d80e8505282e481c450742c0b000300c500400810006000e40b034500c2c1c08000f00c82c2c072011040d14654580041100502c1400d030121458440045001c40c540c4ae46031214014020000c0303424000011401c002d442c10788264881480307401d90400c1032000a40c00050180d40c004001d82140d164540c19041c40d0800800301c082c070b04036441c100b0400400a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 269377104 1250 269375854 269375861
    0x60b0724180c03060e01060e0a0b0303040b030c07200607021e0a0608071d010518040914150114030d0c03050f0a0e01120c08160306080d11190b0105120a06050109 71
    0x3c9104040400c096024902842d080c0e0b11503110b10742100203038000041c103203113903030b0030030007441d04010705480c5040d0702c881ca20030282d0401c3e0790081d00d00c540071910a08200007101d015145d10301c130080089800c0704c1840001d0b203d11a07024028010b071580400070751084056040304468003001032140ca00c0a443d480000d16140c0d040300d03900002500c0e0b00111040700c2c1124078400111206a460500c0c1070080038130400c01c03194581d4203580007581c80c00c4c0500450200c225101014280c80c002e0b14036080c02500c0843e101c04113030001c005094403400c2d4513000ba607001415816070b030100c0c200608003c02070b05066815008900300310401c054000768a22000e03520042540c42441c09807209240b40c1c480c80000700446030912101c901103094200404e01a00080070080c2050b41d2501d0081040c0791a501c0ca00e0902a1500c00c072030126854045800b1003600c2802490800489424001c082510b15110181d152070107108260090144120303040110209108100c10250048407e00081d6074032128900103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 269378354 1250 269377104 269377109
    0x6050a1401090e03030703110c06090d0e010e0a052106090109021011100b120f01060e01060c110d0f0f24060e1902090a1206060b0724180c 61
    0x1245a4203001080c02841441109008528000103500f15690500b0070b8000705001d1074514601c00090100d080401010004c1a01c9410520040c1c85a61060b80001d099848482900b40c140108a050407406031104c102440846c3e40071a07a80c10010515040b80940152443c1b000c030080c00f6000410a0721941500803180c0f0620035507684407401c010b49021076100a03c0240c1e0b0000e80c0050701d11140c407213101e4220b0740c07510000404540300d00041c0c03505285010354032510301c2180d9445400c00c0110740da5041801e0300500c03207401d06000c0754005036201c0d01c40d414850550340c03280320220400c0301808001c40300c2070581c950211907805021240d0500c410101038820f04070315404c1181d070100c0c0b260701603030040d4001c031001a100c000c0316486d8224201d8442d000c20a4140310107a0030f015500c0d255854600a500070144c410101d00d040141d414044182c8460781c0080352440c0040008000141d0200941409039a51002c0e8900b807511881e4000040d0980140d4000e00d11000c0071000d0522035404984003c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 269379604 1250 269378354 269378381
    0x50a0e01181b0c0309051c14010b180403030f021206031b0d0209040f0209010308130f0b032202040f0c020f0601060e060c10060b03090f0703050613020a0306050a 71
    0xc80c456840a07064418102c888059401d03001d0003515900d0081000341031180c464103004405640f26400b00d040112200e845603000f0344a00c4114050040c440c5c50f449111039039030028414041d81d40c02094000b180140801e840c841c16600080c00d05110303038000103001b048101d013950f9400a80032194610749041c1d564a1281c001d54800201101052580e00011180078008040e09040341d005c206882134000c00554841c030006101c0710042ea0f454401c6406540316542682d151040580322100000d0180c204103542040b00800b484650710300001c0d654070040c40303240b80c0071044503003450441d10060204000d420504002100c84124080e400c0050700e0211a4222240c4950102c5250741d0307100300384222408240120001030f250704206008120250701c64040724499044030302d104040315416448213111204c08000d0100c110400c1c401885c20b40c1c0384500400c1c0d1141951103d9803034100240100030f0082e11010100115121284c22500868109808000b50719000c0000009052850407011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 269380854 1250 269379604 269379629
    0x62107030614011701090f0b060f040602070e1315090501090602041409040b0106050721020619020309100f06031403031005031f020d1428020405060f070c050a0e01 72
    0x82c1c907520414000585030781100c05032829920705034064009000103801d60205076110080442552600030003080141d81d1025000d603a54540030700241007200603001442d030ba5064a06100440b01d102101c0c4d20080d801144403a0b5800c1c0404010b402400361050051030b070350070320191009001466001d442150b5803400c2110000d08120304001d10240111002010144580018040948030b64054844140b14203079480101d200c1078200e02140c03803070b036203d2001030303020300708001c40d803d40403106400c0388104040a50031800c085608075154403495603d08081550307401038a0040180d07030851001950080f400c400c1d011a80c044040d240d5008a0345010b02600851002615040020740100e02c1d880750911400d2041544040c10042e50154142c80c02d0745072182030fa044207240104502c2d00416a20b8506c00c40c9041460400c81c1b40c5403600401c00c50188144030401c602c0c0c4501c0116403202c00706111982d0b40e1611898010348034084da401c00ca40140c280f42c0e0216030303071040b25440b0b41624240c20702c0e42e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 269382104 1250 269380854 269380889
    0x3030f0813050d1e05090105040924030804090c05090d02040c051306021b01020a05060a1509020408010209030c011d120a1407080106081603022e0e040b0415050621070306 75
    0x603209880f8205506d400500b007000100002c40690f0301c83d40069030380c000582110309201c5000304010029400a46120100007003c1200c0b44082c8a081e107105642e050035800c0120b0200095110410910081d0060703407581c001e90b040d50301c40e1086907449001d9000b0f88501d19110800203540e40325054883c02074031404207210f5a04d40c00012522000341d4000300509455030703911001006480190040c070358070341d2092000301704281c0d2400034001a05502c030006841351484820035181c02602042d031418440d03c0d903c903241400205010410001c1c007910810100700355031501c07510f86119424050300c2c2290140328111546004034124089030050f0000b8080562106141a00d8540181a03041120343c00f444c10801410400c440c0d141014450035881a40d2000240d03020078107110042c03030700c0020401210080d061515214540500d00c05a0307003013003800a0003024400c0980c141c01401d119800228011070980d10240080e4208076090310305008504110a000c1e02502c80c1703000f41c09030074103190b812 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 269383354 1250 269382104 269382107
    0xe090c1f030609021305042403080d0902100804030305070804120e03120301031a010b0f0412021306080105101d0406050c160f200f04020d091b030210080103030f0813050d1e 76
    0x1a8440da5a070130400c50780ca8514ad9589076258000300c00701c000303d0385409802026985400c2c0c40860150b41d503c0700b4629240c14500141150002448082881010300610011078020594090309089a04040545086150003e4545415404c5c0645002c10000001c400c00c42072a403a59051010f4010588150b41c941060761028000c0107000f02030b0326001e10003040030211590309441814005041c0a50a690354110f08055036025049916180c3d140c0080c4020120354940d07940c011f00c801104180314240081c82d4150a0401a2014002c01d071500b001c100b21200100031a0302107540b101030020390743c8062070f01d071505072080d400c155586000c2c08400010403c49400480540a00400c801145510351041000941006014280300c0d60b03120045000103144400c80035203844082c0e680410207140d4410000150241d110032030400968200400009820100020440c0c00a08281e800fa6507540144549120b003041c1c040e140313200d035070348904145400c05034080200000f15016400c15108140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 269384604 1250 269383354 269383391
    0xa050907021b12030d0501060e0103020a08010506030c1216030b040203060f09040c1a03011401090e0c070501090210170702010c021509120c070e090c1f03060902130504 74
    0x40400260700300c00728003501d0040c2c010400740c01c504024070b94508001c8824580349140c008005c1c41020a40c0c520040c0541f0380c00c88059049800e0900c5e0a6141114181000f131400b4010711440740102e8004c00031a05182140d000c2c4c4040c05406009420146000342c441002c6654858440c00484d28102000100381070500840f0f20518000d824191502980300c144090500000d106841020345003102203001a900701081c40440301c4040f0080c0c80c0c1d41481e01c601c840e00030b2000107c0c140030f0440004c1210340000041701e90b014510380c1c00c0320348400c103506084ac05001c80300700c025131219000c8000e046081c1c0018071880144080703410321240d41e4805c44280d003210801640c62026070710104d42440044440884940d0040c20401070329000002c2d80c8800030300c1d8001c2c000042c140d4000c00c03818000291150303d0720b907020100b000182100301e003900104156400c5200e031031100004c40894420134a00a0704041d000300541d034411565510001d2488540140d81d0050500c143e0038004100746400c2c10b1071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 269385854 1250 269384604 269384611
    0x50d08101e03080c0f07060e0f03010c02060601121e090b1e06060f070c030302030408100b01050d0b0607020a09240806060906030f07030302010617061b090a09090f020a0509 76
    0x5104112150a6071125400c1d90080050070013244900c4845824903081800810020111230315182800400c1400300041d04e03a80713081c0c0c940641e14060320b0b542c02c5940060800d40180080c01c0c0704500e82032a07030b00c01c03000c4d103c0c03108070b4014181010301140001105500110086d40103001d40c0381141c54071084251200c1d4400c071040e070012120707008511070f0300e406401000800643c011251800481e90345082401ca0a0350041e0090303040840c0070403940c1c1d000c0c000612040e403225020050700c903104002034014000e110b400c1d0106035036440d0380d0916491704811a28100d0f00149454810f0b039590913840b000e0802c0f6140d07070100b501001c003d200c0b10121000c203c4250340c003d002a1107541e507102c0a2007113244000700036940c18494200c0d071610302403080c011b94024501a50010450030308219200046004003503180380c0310303481041082415030180d000803c80d0505043d007155154045c800040420101344c001c030700194908071001040110b0488600c0e9894801e5540c0444c1d6a5100200508a030049 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 269387104 1250 269385854 269385899
    0xc03030f071b02040c030e010f020d0c050a0207060e010c150b030d0c0f11040b0d0b061806100c11030106060e040510210201020a1203020a080c090109170307050d0810 73
    0x1d070000c0040c42c4c2508150f0782c10100c0d25000807074862442c0000d003035950600e40102d02c2680000e11911040c064010805084602d0500c18031b00100c0c1035000750380f410a4400e540801815414a41c40c5030b1190b0350004109803c400b5a41c44500c612202000521041d143c15203e481004c0c1d404030071034044c0b0903164242e604040d460b242c07110140c44e00c0800851005109520554034514004075035a0003100c03000d61030042d00225554600714051090611800107a9617000c0c4c0c428041040d03541c1c881024509003265813601c500294414a4400201544a00000e906509201c000304640c4c0d480704403c0c1050300c0c11902404191a01030031a4031f201d0441c0203140391512054150055100000c06003060240f06104803041e0218548910407014480301450001a8000480c0e0104130351083c0401c0c0c1051340c09895616144880b80082c1005486105001c0110000c003006403080d0010f000303507049184c00405032000d056400b0300080c90002d086401c003e02030810349020512400c40d0940203d0703130160 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 269388354 1250 269387104 269387147
    0x18061b11150603100c0215060a0f03080a12061701150f062007140f090601020615030c120303010e0112030c021315080601060e0111030901030908040b0c03030f07 71
    0x10204166000070018102609442035140b841110030b080e10819624484941c054890089101400e484030040a00154850385041400780b00903000221441c08407944500901d40e510440344c01035800c2c00e9041c613040a10340c40d118001070f95201c1d0104240c100c81c10940200040f007032111030100c0c40d17083d50041c05400030140c1c005011060041c0300a6800d14800c1c2100038510311709080061800b04281c0014a208488440350402c80c1009840420680811121803d5a00d1301d800001d542c0c00c0c004001c40d541c04014071186107140c40c02d01c2184e080d43c1024190f6882408105413050f6240d10170710968070340006200001400407102461140b1041c1c0c1a61a0700090321150200301c03406a070b20300071001e0240c0d50540402032140500e5400024103684001d445698940780c4007400c00034003071603030905105090704400844131000c8121b400c18103003400d000425000307900340045540540c0c0c01910440c00c0000d4443c1104000101440c030903c0521215a00d42d60744180846024190b41b0402200040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 269389604 1250 269388354 269388373
    0x140a0e0609040302100c05070309050d200607060608030304021807020c09100b1c0c09050a17010618090b0631020c070e0114010e1302090418061b11 65
    0x5024030301e10303007042c080e1044901d08146025208120b0b4445070540021030000503403070003019001b001210081804036601c1d601c169168070741c0480521749203088141580f04888580290383c52000381c9140c290401d000300102ca0b00c4007d2140d80e0361044e0740692043e003904c40c1c0070b180d040821010920514869028101d900c1c050028400000009010901079160b0160040740c0244000090080ea6080c0c040d0044030140c0716051200b01c0f0740015051080280d542000c1c4400c1c2c07079a070001c0c000c6882402c4030605d41c005503400607004141d603404c030310040f00c250035050b403101c062504400d004500401c055001600e845080006424407040c81075402150085212a03501c0000707180d080500400201600d01800418800d08004540c3c00c51010b0000c101d0050185030f20016406403418000e08003c0800e441405c00595008522660307020348980000e001c8902d600d40d40c12452810900c031a800c80900313036a00d010000b5054400d80c0b10128600301300300820843c07045681c4641ca40c0900090000e494 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 269390854 1250 269389604 269389609
    0x70c0608040203190308040b0106050f1c0e010c090e0601020304060807110a0506072001020306061b030d052d10060c05120301090b120f120304150e07140a0e06 70
    0xc0100305981c580180c81c040164410418101138040c1d202c0c0d81e0740c81e00342c9400e213000e42c1c202006070007070000c0080a01003c07802003000421a0a88400300001000300300e0240310110140c4201d441a40b095400d003c601c0001d550000543d40c265007810031080420396036040120b030b4900443c822540001c14840200f07088901072440c001d0340d0f0203443e00352800d900d07560f210949410400d441c0d24002402d08404d40309044580d0350350113214041070000350301d9400c08000164107801404c240402c0c20684d0381c41401d01220800840b803507282d1009080c4594a425001c1c51004100030760000c01c0c04c001c05544402580c414802c091181842e801284074640c2440c5040703030381401c2908215214803518064905ca0324840d0003031402030003482c00218510f160b00c03090111480200040c07802d5a4484543c1c60100e110200e02c14240b028000d024030741301c0d95181011111aa900342d80243e4182c03400303149141a002c046003282c00d0750700082d03440280c581e5210510405440a215010102c0c01400201d412071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 269392104 1250 269390854 269390867
    0x9090a090501090215091306080c27011203080a02030708011a16050a020102192109170f010b0114070204021602031c1202070b0601030b1215040b090102070c06 70
    0x41c059000054281d5442c0d012130700d84031000c4c1d100031003454040b600215524103110325400500c401d000a0020502c0c248070325940d10100600f03076110b54100d02800389800031600c0600e131500300d92040005203594034100c20701c907401a01400c0d0001804940014030500d4075000701c074003840703860b034030741e402c5a1a1808290711102646101e680802c4200040b00c119401c80307003c01c4009000e078000d08001025880064034140342400c40c2500c00842200c1000802c0c03c060302241000d00d0003404e04e080001109040700c030051960030081c8000c80c242c00b0111524030015502240e0803214008100803213044006450b2600d54400b119020352040000c500181040d8000d802c104422030341440c0d461a0940c002030031701c4000e00710541d04104c1c180d8a100501da1003100142a0b2494840851034065261100305841000500c1c140c149074031140711441980b503109040340c0000c004016603200c900f00b8650151014002d0340d040d1030780400030001c00c1460304180300301c41b0450b501410041d5098a04541175920 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 269393354 1250 269392104 269392121
    0x40e04030e130c08010f0909030f030506010903020612090d02011811180115170708072106080d02010609060f061815090305150103050d2111041a09090a 67
    0x642698050100440342c0d0148044404042e1900d00315581422031038064040e95622552400d810400342c0000300341c00c20414007062003140b0b404a015070329080165a64101030348002c0d0800d900040314031404a421041c2c50251051500f600c941d07000030842242a01c40e000140c903a81c9040808031800100c1c88882e100c94103101510700c600b215504001300c01300180991083c000c59403035103030f540201588580341120055040080c1c243d642008040148a6400104200203100401403214403010100d284e80e02010070103002488201e0706d4032191038440f814030002134050743c200170011031900014001c00003031718144103854280c689001c100f22068103041740c072440e1442c11500d003c2080c035603000e0201e498080d07644600307031428a0f500d0080e181c001103010765410110004014400950041040541401c4918042100081c12104010b0401030b1309515003011380340030300010000c01d4400140c01241c0a84480026111070b043e11120180b00c0d0901c41507110301c05200060f1200742e1035005054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 269394604 1250 269393354 269393359
    0xd0b1806010317180301020301170f030403030903020f060714011a011e0e0d060905030403030801210b07020f1b09070206100e1005030d0c0c080f1b04200d060605040e04030e 76
    0x450701c6103040170030700b240c1c4280c00621030350f401400484901041008446a1100260001d40c60a0710f0754a00818054150200a1140001040d1283c40d41e50b004143c502c1030341c00c04881d150f00c0312280040303030003441c0c1440c1c0c00c00c120011520313541056000302c0c246110b544010765105800200180120340140003003590350740c88914045c0010103d4035510a480d6603502c1400210740c0c89086040191900c0c60590148459440b800c04002c01c19000000c502c0260b944980e9034000c90703c401c2010307400d1000001c03d9160758460b0300400c40341e0f880000e00e0204d0b0320b84e003650381c0700b0f290b2200d0170b007261106c9040791a01c1400403582d00400c803040341040000d0703005445480e40000c142c0c40344002814803aa2120080000d1a000030040501180070000c00c009d08204d00140040c0c0c0740c54a03666101c60310411704c42150001c105003d4015207403500080c65800c00408107001042c0980320310714194000080000c402da140039030208281d0700560442d429600383da07950116039134640da01207544072000e00142d034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 269395854 1250 269394604 269394637
    0x6120204051b071a0c0f0a030b01021f05010513050421020705040207030e0f0f010c06020d09020303070506012102151614030a030f0209061210050d0b1806010317 71
    0x704074442d100140c80d074140b08045a2196181040701e4490007a4054190030851004201204c1a0b100010484601000608010490500900042c0c0c2450400d901c10706030340242d8250407200c081a03600c024107803181158450011420f5881e41421218110703001000345203a1201c000d010074015900d15900e140920494803110b442d00041800da8102c0300e0100c000c6200e61300c01120600d0001c600404081c803d079842011142a00002000d5104051025040d80d03400240c0d9070201c00c0c0754110844485d005400c49686030030f0391400c5a036405c0300348500b00100103500e02400070351108001c080011034000f44080864010480302c40d4599002c10164106c60211680c40b400003520001c440c0c2101070b801e0042c1d6211844004040c3c19906080440c03150780e44100600862961090181c4114081c0d8241c0c20745180c1d9160980141c0b544660000b6a02c445c8102d00c1000704850080c0713040c4582c59500f5803041d800201e201260741c1305400e02006222880c1304400e1f00e5000303e5040646580d0aa50000c2d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 269397104 1250 269395854 269395891
    0x506010f0b07151e06091b0f050936010b0f070b06062109121c05040c030609080301180209010f08060a030605011403010c021207060b12030d05060907030612020405 72
    0x507840d64140d861020045172030b01c00806c916a100d00c00c0701002c03080c02c00c940748003000a54004012440a40240d410f11402003049002521030f0f5152110360100b070300700f078000c08400c8600c00700e199030201052408034a0010010a1504d00c0c40305507000315200c40c40d171030b040201c29035841d00c506100401094001200303003c41c41d20942d001200e90300401d01c085000900b410321500c001e003042c0d05199020844101000440e4103104981c40c3d89441240234500065682c90320314240c44408000d07400a0301c404d0803d41e0305d00130310484000640c100c41c08811110b001204d2881c188069018600d0340a0100c3c040417411558940101c44059000400038104500e1980702d5403200210f030801c0e01b20303c103209141d480c0310940341000d11030058610785900052034079014030300c6c80203c0c5104103a001490f440d1280103c030042c0c2c80e486142c11340c4c21150350070360b07407121100046d0b0402071804450307040c030468461001c1034a40e802841490165441040e41c00414440c40d020f100103010090005000f180203003162 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 269398354 1250 269397104 269397131
    0xc1a190c021315050f04090506011205031e0316030c0c02101e0c020306090a1e0201140315010207060305061003090c05121c140304031101140109090506010f0b0715 72
    0x110a042d00c01115651202130a10003805090901108028051498442c44d603020400c000768080c110b0b84061502c19544e1100d00d015401c6010f0550b21503200140380150750300c042002c030f014500c11039049005205408000c0011010b0f00c0c40300c8941d0010810064111025041081c40d491420026040012112855920200e0ba8100c60f13845180002c05684241046141c28803c080d0003080405c0280b94400c1682c0f1800fa206442241d01400402d0f0003860307108590040c450990714045000c00ca546030704e0200c1d0030300c4044400104850050003030580101c1c001c2e0081c412180214405401482040341c43d440640090442081c02d5681150003c1c00243c644d54052845031022580c0001e028480084d1420003050803169440c03a081c010582a92840348100100b500e620580501d00a6000d003240c0c5000c0c1d004010700d081580c14105488000708480400350051181c0ba03101d2401c82e44a0384e42c0b9102d06134082c102d07004a511951007004000e020880020404484041c062000101c000b83c0d01070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 269399604 1250 269398354 269398361
    0x5130e1f09091a09030f0c1204090b09060405090d030b0d0b012702030103080a0806131b0f170619180b0a060302120c0307030b0d0c1a190c0213 63
    0x441d58a2907140c00703803581005a00c4a111040400a4540c410642000c000e002e44030700070145244c0583c44c000c03c1d103514040c0c0800c40100d2134071403091802e44e15910740c0e001c040649408494940140c1810022a81c50308007840342034807856100f0050241c0c00c030340400807009030040d84005940605100ca214011610342502c130760080041100c2440003c9000802c640204a074101d0300804a10510041002c140c0c0d01084030803800ca2894541040d66038070300050b40c1d040300e42030709070071542c40c3c40c80c444050190182c0300070301c5806a03102c0316078103065403504507440d020841e104a0454039420100344141488441840c840e188185010109510346400c0e8055041182442925984610a403142d5050080607403014104900d015071420f00501910740800c0005441e860042900100090825109500248850030010801c100107401401d221203402194013806030300307010b2602141c2c904a00c20080f10b24181c98074191a0548408200507a0310000340401641c1140d00c45880c0b94803c5850b21 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 269400854 1250 269399604 269399609
    0x9050303040e01090c020f0a0204020703090801150306112125021605040507050a080901060801230718091e0f23070903080c0a1e030f05130e1f 63
    0x242e0902c880d80b411601c00180c1d02140030841c1550010190103011580114250001c0c5406a4001d6030724080c070b190807942c0310f04690050000d546800c4200c4005e20000742080b0841e8004c0c4002d21000c6800c110b01c100d64410b40085000d214440282c001c814122594a02d070302516030046da01c007600c0140e604541c01410b079194030005801407600c529001c01c1c01560303030000d054141d030100214600800b01400d0340c4120380c024000d0000c03040000e04583c0342500807201422490000740030600d800c080b031510fa44d040c0250784500c4942070000070640d51184084a02c0c1c0c03030000310704180c0300741742982c400300a01c151140100b83c5c0c4103507019000c004055000721031011075041350005040b86210115288003200c075180700c0f40c01c08148207002002e81c0c00720704c1c2010342e0740040c0b0307050703a8450071074035145045941540140101d11100301c086402c1402d8150100050180d01c4010303d4003118a4100c425201d41a594111320300406001d00020a020382659400781e401000c00050b041d6800c80401c280c86540d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 269402104 1250 269400854 269400869
    0x30206011d0106140d0e03180a140303031b0705071701050f16030b03010207020414010510020f060f04050a0c081f02040518091203040c090b010206190b010905030304 73
    0x140100194803100c040901414001030045040e54101000201844091034484d10740040100e01c000c1c0d98116a802900405030a2007183d03600e00041002c1400c2e02c2e2490b01c1c0d207100329090b0b00d000840b00a80941081d003c41c00402071869030703440b01d080e081504c031403100c803181104e800e000810000d00c003049144080c09800640880c039451601c019400d640c001041e400704c0c070480740b06000c011821008200400c403040c2c20003080030400040400d0080c0a5480d010754014200800100700c54079040e0030741c0c140e500696074681c0c0782200070010307039a0b526100708406050f07024000003818000c425003aaa0464425400e9072900002515815216406074204a1040c0c1052607401c0ba090080e06d003280d0004407026082d030900d072a0100140303801c411b405c1030b840c412000c140000c91800042c440c0c3c28081c24420550ba0311b81c1080c2c10210f2400342c090150a81c983d15049031340103e9800092020701c6000d960300b80d2403010a401d56000c020f0030f48682218180601e0003004145554248060b2001c1c1058 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 269403354 1250 269402104 269402113
    0xf09080306010c1e08180102030c0706050901121505010215040503180d20040b0a0602030306060703050415170a0501140d020103110a05030f0f01030507090513060e0307030207050f0a06110c0901030302 88
    0x410507146c40c03000c0ca103004541554020000811642800320b4103104403002030402640390034034100181c980388144494100040c1c50140001c62910700480300805580d4280d08661a051010a9280c50080159000341940c0e0003800f89a40f80500d404584100754030260185184072342ea40d68224006544441e10400344844030869000c03800d01d031003005006042114a41c1742c15241110207522031002924139401040c0c00145201032501510840c3c0003001e51a20441c0050051000107049030b0070380c0b14a503908012280421411481c60040318162601e800924141d40400ca040200c80c007529003080741490b4840301c61034442526000504000807d41e00c40c1e66880c580404901c0352200002e24404001600d64018408240006000003d8803c21100040c503511082050500124600310040c0f880e41000954400b0400c040041d05c1c00303e10176021203514980b00c4040010a140041d540f6400c202c07407a0082005d90f00c1080f82180e18504081030314081200724012659008090b0000c0d40943d01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 269404604 1250 269403354 269403367
    0xf071808011a03010b01050f09030712031215050a050607031e0903060612030804140c06072409030f0c150609060806070c0c2c0a0f0f09080306010c1e08 67
    0x7000718078450040b004400070482c80b082440064094000c25540f5580b108002c0341d803a002d502e04110320000740040d03440c03140021445140003800380e05a000880401d07400c201030901407010141500d429241c0007003003a04014100014844941c0103a1001da00700401c0d8501024005040018407071141d0113079964070242070850030700d030b01555203d9002840d4003076450901d4010982c00b4072581c2d0451351045c526043d001580c0c010515208403032800030380c0540c00060300410046008580c0d0505c1c0e00054404100c901c02c11402e40484800c50005030229000541c05150f003446112079030a003034461540d1960000c4241c007034a08a5046030840c501c0e040e625001480829410000c46600086918002c280c5451030350703840140007628400c1c0e411609006d01c0c20031111a02804c4440040c01092008507140f800209100c0501070082c59188064600301ca111407a42850042e104803680014000d03185850b4000112651408030740c0544103800660340c404071101505158140041c0034100050703c414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 269405854 1250 269404604 269404631
    0x1b0b0306030c09040503030a020c07030c0e0a14070c14030d020403060f1808090f01030e06131101050f07113d08010e040f02030309040f0905060f0f0f07180801 70
    0x1078000c0400c3c0c407400c41c4900b0407000a40010450b81d10210260380580c584151398130480c9000919040280b0880101e038000c5502094100e1007441821011814400e00300403070346401c1642d0302915480000344841011a000c200c810400c002e000c100882100e280c0701058000400301e0300300e50000c44901c2c1d01c0d8200b0303804030410b9014440d219440301190241740e6821307039a940300c11302c140a8154003c140b40d81c09a48668002d500440c01650404150f54407843c1c07061a0310900d040d540c500f00e03103030744140742540e00c2944144140c0b0b1400b007103480d45a242c200b03980c8540c10105158140c09034448100c1d4009100078804c42002c1d02c444203040c480c00070b80542d50800d1901a0555800c00c01007001d000010400403540404654111b40c00c0401c0043e51601800860b0861040003220350308541008082c0b01d41c80302c40da018070483e07802001a111b1944035140c000e0750912003920820190341695001c245000041158150040011f00344030066624105680c1001e070620352201216035510a0a0b00c5484d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 269407104 1250 269405854 269405863
    0x108060a0e030307030f060b040e090d0908120310080a0b040308091902090403090e0c18090403080720010609022808151908061e01050a030f1b0b030603 67
    0x11000c1401840081e4021000d607580340001001c5208054036086044c040c5074141e88004080d204c010803884c0d641d601c9007006c252040e810b440e4076010340f00719000e55510901c165404400e85044038003a0140c40c2c0c03601144600e581010b480343e02840313411600056103034000c1018082c0c0761700c1003808250b94a0207040242c000d080080c00c100094001c1c15101d010490180011259980c0c1110003203215140d6040884d04042160895000030b1070100070701c085050b1540c00b8000d442d801c0710080140c640d1400511480040a440003004180c080000c00d18680c0030b00700380600c150b00c441d05c0281c3e00580c800d07074500b501d40c164424036a090340001d050355105041401c107080d9a074640100301080c011010007d101203801003c801c401a19004c800300544c4c0d950b80c0144074940404140c42c140e50315514540d8840c2416030b4030380c0004002c1103c00c12900c140c26600d0381203801c010301403054945141c4a0303041c0114102c00c03c0704e000c080136200d020000d01c041042e402030417240c11211340f686020014140741 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 269408354 1250 269407104 269407111
    0x4021c02070f0c09060b0706110c0a200f1809030c03070804050103050705031014191502010605090f070c0807150b1903150b0301020906040303050904061502060a1e14010806 76
    0x138181041000d22448900c0f41c00c07260095889407001070001014a40030036280a80721102d840e6002d449421414041400301d49094400ea070702050f00d4a50106040094210403941c7c07140c1c0142002003149403106401981c00e81c064900c1090701c6c45d0540c1d5550b80b074116400104211100c001c0840c080c020703541e01d8402c40b03034841010b00300545541400070038000c6055152107580b00f00000016980310540b18036180d021414101c14100d4030311500e40d050840e0ba83e0201c54000c0043d07181c290002424940541c1d12405100b08100c101241e88580a048401c8403034020b042d601018104103034000a4492035410720004c131080302c0012598003010412007046e4218407142c13816002544140301089654030700010700b0611b01400038401e80d103a40404e002e40200d05074994003400201d00001450b810030000c110819048600708202030b1545c2d81d251100404810400040e4000000a00501180d510070320590010403900d000b4600c41c01c24440c251141a651040000c2c240401003181a60400410b40c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 269409604 1250 269408354 269408369
    0x50d0b0a060e0d021f030207110109060915090b0309100f051501110705060723070605090d020103090b0108010606080606041d0c0415090501120e030904021c02070f0c 73
    0x2440c503000740204120007240c0c84510440c0540e80d0001103580305140d481480384481405903004504010150007504603500a4071803054150702000107611036041c103010745500383ca0f5038010904000c0f480885091090b0b40300140f00d000700002c0384408100014500c075500680c0200044508810500296000c841401000c0b0307003010300b44804001259588004e0140c2031a00104481c101c4030014582917555000c950000700c005034220501800c03103200010328404140c90007100c0d03107401e0555500c400314820880094005e03c1850303050310b412079424003010b0052601050001c9d064980003d070000070790181c02160354560f01044901d0308529040d50108007144d01030305041c82d100d108003980045902d107411030100e82002500318140f20f030035180a09021010300565040000c0c024120740c41c2c0e0701034940414440094103100c080e00b401000d45c01e07400c01c1c003e5400c000e0604103000194200c03071010460100c10958100c0540c0580c401b508469011795461080d1003030070308241689800c141c10403407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 269410854 1250 269409604 269409619
    0x5151b070303050d090c0509090604051b090f0c0d060801020901020705011706010818010906150e090c13020906161a040b040209070512070e04050c18061e0a050d0b 72
    0x40b07030300101a40c84601e641800844d02d5500e41c40c0c00c2800c1c00d01d5411013a400f202100c00d21204540005100d489513200300100c0d902005a14004106604104c40a50f402500d040c001100da00d041d400b000d8104c454a4180c0f8249038002d0a941e0503545540c001d1850f80c0c0d804650794545603410031005005000c01e003407152040a00c000c01910551008007006c0c1801405000325141d46400440d0240398548c6900800440c102c924012024041412881d0421010010301040800180b070119000d803003450b00a20510b0310b00c0c000d002040340342540c0030780360a40c280320041807921090000c0114038000c020010b8202040d2400f03500c1d42d4031314801c4456500c0001e04110018040710007250b049a0115600c25032030381c403a030341101c907441030308810010924030303d042c00107141d0444510004403004aa06100c02d555952501030300340100c0b000d91103000c5a41001800504103100100b099180c01407001554a05a60907022160700411403003000a43c00a1021032022152080461204080f501003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 269412104 1250 269410854 269410859
    0x11032208032206140405060307020703020d080405010906110a0308100f030b10060c03121e060e061302031b070203030d020a021006050d020f01031a0a091e1803110705151b07 76
    0x580c4d2900440c02082e0080000101246d02240200f0980008650040690031081c60a15000c50701e0740040c8901d9002c180c4502004c05c40314010007401c80001070403001840d200f607050710200c0b08168003605891810904a5010174076541210000000e94040c41c466142c1e420002008008a15943d01400800001001c0040000d80c081040b601030350700e00700003103100c880d40c4250f8104c034030398000c3e80d032101846d01780001a901103a8001d07a02c0703940b040b5545000d000f4110280c1050744001c58a9403110804403000c0807007641da17000582580b41c009001c4a0800c0d000c04070031401ca0b4458094000583e203c6e4003103100000142c09041c02800d02921090f041901035400301e1708440c2c040c001d4505060f2510005070b10b9024412070100c000100400c140303c110381c0e031400403005103801c03c0205110702003140765100c280c80303602540c0744003030980c2a0841580c90b00d0310100c0e9030090009c07948805020316200011150380701d4000303002c07a4844004040d80d80407154018401064a052105c03207640015608 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 269413354 1250 269412104 269412137
    0x403030801180b130906050a050411060f0d090606080f0714090406090215040603060f050d020907050403050703211809020c150a06031211032208032206 67
    0x1411075145050b9030303a1079240045094041c1c003e4500d420f8004030540d00180c001c808640000c20035500848041141d40c4588400d50240c8004a501401c2c0d405500840c081c0e50074860001c0800c1043e11207004d061030307007680440c02070381d6081500355146915104103002603030302031040e8004880a10005c01d481031401000c03505005a200040348104040c50015080c44482d40042407002da001b442c0f80c03040080681c0783c4566070400e014600020713150500220b041380d080c5900401741d0327100a20113070000c80b8035406c0140301c01008014000b0014140310020000d101000703a03c000e54407840c0f8072000c7c0307840001c0e00745984842a91407000c1190311020441008a14640d810640d041003001507503411494542c41e1820541042d481c02c0921402c04110850a040d841001524414458100d0003400e400c400c4075100040301c044001c03074004000c40c41c2d03820001400c41c2445a44410100d8a0b6982c456200e403c58100389a9208440c105111380c02e0004d003520301007400b4042d0390500140250707440c0d17074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 269414604 1250 269413354 269413367
    0x9050f0f040c0509150409031706100203030c07080405030709020a1202040e0711120d02030a0609150605030a14010b070201020c031f0e0c120a12090614030604290312040303 76
    0x510f80039094207400310342c000c00554070000b035145c40500144070612441ca001031060040c01d5042140540c1d14000ca0210b26100419107090790041e0300031819501c5210050303945030312080007261707845401c2000088588003402154000c010040006807503040b030b201c01034048844034400c4c40202c0e20402c07040c06812012510188c0103200d074a419807229049494403464040140b0121481d90740200305013002920300d0300203510500c4051828020716a5541c0071105843c024829401c00c00801441449890b10034406141c5c40100c030800400c0d000c122841c010300e4a1000c0e0000d0512000000c1c9100a40d6010007000c80e000d0401c0d0700600714031414070500c00d402001141d070801090b440380084402c40d0010010380307041200043c682c0800040b500e290941e60030b40d9070811501c4403281140074401c04d0090850300e00b2100e49468030321007141540180e4100b540000c0c1f9842e80140d5901a04018609803000010b00e180851182c0d0707a08280a010140b03000a280006000c0c00400c000500020b6480310 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 269415854 1250 269414604 269414609
    0x90e15100e011517101412070611070b030403050912161701020c0d0806010807021b0609010c0516080f0a0218060a0e0405100c021605010f051309050f0f040c 69
    0x50620302d042040c03c80803940409001305000694034808144110007000b80412022504200b110711310f080841003e0090507204079802012542010074100303c0d4600490802014080200549960a84030303043c00d4001d40041da0280c001a0380411462110704180302440c0303a1840603001000d03041d003c01c46041d080e032024042d40d0a052070241d003140f031500342501a51103186a10303040d01d56000860f90002d00410040310514000b49000012401160000c210b0038900c00c41c1000020200500400303222203984003005685c100516100d0f40d601003001840311074229241d220b1040f44041c5480c2050b1702d0258031500605154011118400c0142c0c0c40841e0341d112101c6a01d0807418a80d50040001c8900d145135005001070710280d0708010402201244403418018001020040d9600c2540100da440c242c1e041c0142610f110040c1c00c0c00b296004400ad041c003851280f40061030720007111001e200102203903010144568454041c004900e2002d2899139000040d0002e50000c0d207010f4403810100300a61 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 269417104 1250 269415854 269415869
    0x127020a211527050108060a050c1305010813061d160e040f060b0901080d120507020c010804060f0e0a02030c0f0913020a030f110405090705010203070813090e15100e01 74
    0xea0f010390200700d28003424a44034264000800a9694803075426485100032205090307050f14007400500d00120713140542d0742041c10401c041d515603003032000540300c0800180401068007000040c980005206001c0d1150944100007020210880c03c094285031030040382403400c0d0003030020001d02101080d000b0241d485900950f091807800410b040820042024240054010320110004035040000180c400032100361a61800101d4011440b2001120415640c400058200c12a180407643c4102d03100341c0c0042c01a8000a1031501c04034002e0304950900c1030481807034000c603140400390318092025000300714050351842c42e403031070000000340c0d0940c000f081c5c84a0090ba030300c000c005540700c00ca0300390051940301001003040205410450342801d281d21402d8480c1d8207000001d1032488000c00d0f00c2c02140c1041e002542007529035a1401540d820032034800e103418882d84c20000ba008018014031426511203000390031403038000300106844e00801000410100d01c825005c010140c5170003441030458011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 269418354 1250 269417104 269417129
    0x9090201020f0729120403091d0106050901030b0f100f08101208072109030219030203031c0b190819050d030e0109060e010515030f03030127020a2115 66
    0xd4188004d25405070302c20f10080701c0c2e0302c0f008100030540c004079000309071140032919001d0035082820052444c0000d0250100160b814409200c180d402600402c4898900400a540c40c0701c8610125032100d101d050020002a40c03c0c951414143c1c0001200360010144241c190000341070049401c90329070a4000188244070005254041c00103021850b03840c0d0a880c07000c8510002c83d0080201a1202c5020aa00c2440b003200811469a45014004105c2c1c0c4d015000d9424000355491000840240300103440c15291904004001036580c25214020306801d80079901500b810701d0380c00c80c80c20f000401040d0440c1c0034100da07000400d40004d40790440c12003516011030a0510102c0050241803078110041c28181071500d2002074174811b4210601c1403260100902040d140401003580d171343d055021640c25074004000500004014000d079040704407039111000b0219280c1d2485108a034050101d4500040c101c14411400322002240f000600800c998140941110302180c295040c7c068403c0c400701054 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 269419604 1250 269418354 269418419
    0x106030c031b1b060524120601141219050f0a05060c130e2e0509040b060402040315050403090b19200a0807050c040204032003150109090201020f07 65
    0x241000401d50303190340b00005100305c0c00c0c01300400315400c101e03924041030b0b100a09451b080c10308040b0303401c0f6107641c030350740040130309900e44005d10801c0540990003541144241c114a0380800c410054028480b1448080c84000d00c010f0421904240c1c1180c0d081d0690741044640c200861310001d051508001d203030014595900481c0c6110051002680c407444205440400700008407100d4020b0718501040c3e220740c908901250500340c2d001e43d103a802220360110286012601084062541591092014000519064480c0c80d140749100255403407028031030319907017000205544144070b20000c1c040440c07500e003411544200c0780580c50041d10000b0401800d2902c4031125002c01094100181c1503200350f07000311f41d00c0c1c2484102540a5501680c8602c02d0000d400160300b4188201d1342102d8010301340008a030a100d1041e0711000c14510413031740c103100b03034044007025440949030940242a10600081c0c5050188000f90600340440700c01441074115500070004044a1240002c2c2e5100602c81c2065420 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 269420854 1250 269419604 269419637
    0x90f0605040c020f1605060406030e010e0604080c0d0813290702030d180c05090a1415040c020f0c1903060c090e150f01030b012102030106030c031b 65
    0x40180d100300d60060400a010280d10707000305941008490420640d8419564602c4415014000d8800d03e42c004104100811000d403080e840f126140f2480701c00130034036402404201340303041001c2d00c095521420000780f10b1810b982c100620044841a800c050145240004071403818800f03160000d0440f4502c441c00140c6a0400b040c6c80a55a10780c02008816080000e0020766a41180101d129180c0c0b9144080104601041c141001ca503404000a0106070600c402c0c001e0242003d00760f090011303154110f42440e4119907a0003489001001604c00884403400704110070b035002c0980c0394055401284402c0700510700411fa00d03c00030b100ba50807961000744950720503141d00c65644003602c054600140e015809501082d02c0703086035440b110500058964101c0d564a4100068400707620002003042011254043c3e00a045000014106402c0c0d1501c90742511941032401e01c90108920340c0000107009068140c1704220b20b070025031408000003401400c0d1100590002e44d5004188114041d6248551 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 269422104 1250 269420854 269420861
    0xc02130f050405030a090501090305070312110703030c0614040b060906010c080f1b240c040909060c03050c12010b030408090a060c0c123203120103020f030607020304090f 75
    0x24108220070401c41c6454240603840c0d0700301d805002c00089001c1000102036202d1890706054035000006000b010340b640e40d41884410881200c0000e00c4007881d0258100c40c42446103400844c025100c2c201a01660301c0c20800300c2e200d8a940c110b03994031000600001c1086c08000e1a0703c054103854441454480c000107032491110440300600b440000500001005416809400b448031a03d21142006452410b00c80c1c03036a120000500c0c0720000c0071541e680094140031002d0308010061681c62809403109801025160f40580989405444611400c03074070790b0601c1000d5000002c121050b0030006503035007801070303000d0621440c0100603001c0081014084d1503000c0b1240a00001c11001d182a41c810b03018112044003007054899154a82c4001009000501c4000c1186e52180021454120030048501c02c41030504810207007002035200110048010002070012007044441110203614500c10810741c0090480070038000c0c0c01440c18401495000000c4c4c50548e0745400b400700b4171325520300c86407008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 269423354 1250 269422104 269422121
    0xb0a05180f0301020706090c12020105070f21110f0f030a080c040e100303021209090f070e0a06051c060f060807140d0b030d021506130e070f08070e070c0213 69
    0x2d544001048410050164825107101e88203c0010754620703503035890200314840f05103001c2d021903400c00020000424020382d10918038454115000102000000700005151440c980c5000c294a103d105410f8901040080e202d084201e00606800c80d51400307007900d0f03000380307003800d001c0c00091000300e85641007550940d40602060b40071042d0510f00342849251020b050310041c1c016008071001d111031641003104a90f843c031405005103041c0d40b1040030483d800380008011008003c400500f0f50105e07a04c1c600c0c0d10000300810358034192100064030003410001c0100c141c1c40f081502d0003030200010300401c158130007110b48a061422032603440d80426608a41d114006030702d0480c0c00141151940d005078010710541c541901129164001d1041c26a69801648079940c0721140b02c0000610300e00c1c1010240d40700800c0c000002c60405181c500180c540100764002001c2d69142c0303c2e0910007507804210100007000300e0b54000a0a0038000ea005e4805215010007078054440d4400d45c000301941c0e600401c41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 269424460 1106 269423354 269423359
    0x130506011403070219110a0b0405150c03280f03021219090204020414010216031e030c020907030504061b2c030f060f010b0a05180f 58
    0x10540008180f01c086120701031110342c06100002004403814429141c140010b0025000c010704014181c0104050400501c410400e55a60010000c1030b6503503c205556600b00c1a41464190700c601030740301c001d100c00c05241000d0581c07240c1981c045161281c1d107258416000d240c0440c00c2e445060003580d10090041d0105906e2116981c0c200d0000c0091180001c98101d1a4046010b90300700ba0300c40d9401c001141c0268042d540c040c46032001c080c44043c01003c62500350781d81c6500480142c40610745c045c40e0600503008150080803000e42a42d001404451149819180200544001c6030300321119801c08942c1840101d51035681e00040b0141c0e21110740030000701c00b10f00a95175142c0c04018076071034803000400080d1024006c80c08040c08000240c80c80e407518240c0c8081242c0180c0c00000d1155007044032581481d4400140c1c4d014200700f0103820700c3c03284840e002030708940d41c1020071503 = true := by decide +kernel

theorem cover : BRFrame.Cov 269244604 269424460 := by
  have h0 := BRFrame.cov_init 269244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 269244604 ≤ n) (h2 : n < 269424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
