-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4477
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:44:33.146457+00:00
-- url     : https://prove2.me/submissions/e1be5723-1733-459c-bf05-255da051fdb3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 805035971 ≤ n < 805215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 805037221 1250 805035971 805035977
    0x1030b04050a0210050d0b1905121207030e0405060f0a23030a110a0b1e09042a081005180414060f04020102060f0103030f14091306030c050307050d03 66
    0xc80d0420108200b0360300310310350141c001e8100601c56600984650071605540c105c8074249071400119240c030b11280300007103100d4000d04e036107075080030180065019100310800c4107209440031149000d6040000c7d00c6180c0c03003a40c5085c1f00013180c070300b8032080e91000380c0164014650079034900700b01c1e1780d1080c0020a4404040b0010140840440c2c101d01c83d500c00c1c030700d0b280c050240c0c1c1120014880d21341c024008900c8143d4503011816901c0045205078882c40820b80c42581c1d100142c010301e1141c85c0c004051840000b000815890b4501c604035100f24450305900c2e2452101c05503d2980700d030080301d001e501c24058807849042c0c41c50400070844800c04152003002c1107203100000350402c47c0045182840307520200403141c1600c3d0124584001030170a840c01d0380540b00340d10003d55040b00104007103041e2541955056400074110200f9180010400c00f225140001801808804d48514000744a000d54003480407611501e03509184001414580040c1c0c001e4211401c1840309807108608921031aa01d86 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 805038471 1250 805037221 805037243
    0x4060c03020405040207030305180307030c3503100e060a030209060d060213060212070c0603090f120207090f0212160909020d060504050f010e01060f090803030109150b0708030103 79
    0x16400300c00a216540100b41c1c400c2c03001c2012400c0c5541507028070702c614003940135408649003201c4503c2d41c1e40204507004000034903c100000000f11321402815550048900341c001d0310b4072660342c05054075120070740d840ca145408070420485030304090410005028114500f0302c60308042e000710f80c2c00d40840c04013900942030400480e0442d1280c10f04404415007050302107440d10009005081444040d100300c500500c01c070100c0100b6003054000b01d03004103912032501c40f1841d03d04031080d0040c01681400703403012944003034401c020611980341e81e00d4004503503001c0d00c80d560420007290300711810003560b0042c80c1e00c1031020301c0e00c40180e03c0406810554229180c50b40c4044040b04032041c808642150351003500118083c814424a0b42008013a140200c405100d02d69600404c1000e14100b48180703c03040780300c24010041036000b03142c020f082d0201d0307141c40b500f407030b45a403001860f580c8280c0c401240e00396244100e144030501a405540580340301c00c0e20920382040340e11440920f000600002d0040b44800f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 805039721 1250 805038471 805038491
    0x1091502030f0a02011515050304020409050118030801060f08090304091508010e010506101b0803060d0206043005030909070302071e0212190b060315090c1003020c060406 75
    0x82050340c030b000c50624140c55403040c01140090190185140d04000105494801b0518100c80c0040440319201943d40c0703401d56450b41c08000c0a400903e100751615560388507441c7e080030b514409034404500031745841170307254580800100110740181c140c404115800090015110002c02228200d403004403001c01d090545c440030004a0303220b540007842c1980380c400000c40710041900442d109800c212072140c00020008400c0c2e40e810000c043c0818a100e03800594070002d202140503582199000d80f80700b040c61059400301d23580394825080612001e41e050881010210384440340d003072030b15156a1003090580144c1e5125500d00402803c07501c50000040004c00c030710b00c2a070588250f26040503071401c989404e4103001c45100c6458030141d01401c0340007021018940002a000307450b0f150009003100003070003a145d0035030103007000c0d1100c4c1d0305004540c2c118489075480d801c2c40707020b841940c01a01920584108011074001084400000d01d130040c0410200c044011400562090304020042814548 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 805040971 1250 805039721 805039723
    0x2030613020f09010e070e0d08090121020c0a051018031b060519050a0b010504091a210c0108040c030201050705070819020a09091e080d0606030207020117040201091502 74
    0x2101150a81100b00d0703c0000500e180b0424145000300d6003034440704051800801440407003401c00b0801791001408014405140d41300e034821030000580041d4088403801c15440c4a81a03900c0030703181d00d032681c0c0801d20490500905002c0c4102003410400b01b0081030080cac0c100d50540041e0802d010b400c2c0002291070600c00d604c00700003407100d154061701c10821460156558420340c0041c41c0f814101510b080002880411107103d50801100c0585800c2d040502d808505030141610b42c1158800c425121060035441d00c0f6041c1e015420103042c40030f003d00c1c0036603407803051410001d110344504111010b0284000302d42c44043c014192602841c0141d5218002c2c14040d2a10304241d02954140c410b03502041c030403110f2280c0322101c241c400c6416103560381c0e03210070b14420b0f40c0e015040a1b18031081807044003018a8850b0340e80c0480762048010b00c0c00c09482c135024070300300c4a040d88a100440d40001e4103404640e4080700c00d074203a94210711801918286900000d000c8409030240400c4c42803224400042c40f40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 805042221 1250 805040971 805040989
    0x130c15090509070302040329180c10170a02132d080c18010b03010e07090b0a020c180405100e03070c1212080f1b0403020306100f0b070203061302 64
    0x7502400c81070660800e0034008000354010320043e1544641030f01100d00b140003146d0108180b006414062800ba2a40c91344c0c240e0f11500e0407000800751250400916031622402d64800018038561107403041c50058040301103509030010300c1403410920400840d01702500300700416055600481c225014100410790301701061036010002c6a001d05030000000d038010703000400c0d450222040d02c44507005022492080c91341e140038041c2e10b001030424801402100c0e242c944156000704240b070946000f555680728001c0542c44000724100603000010f1000e550f04054008030b461b00ca40d0b4000610300d1071f2588409446285a00b0381110041d181e203a02d80c0c04c1035041060720680c41c4c00c845000e0103595a902140c403070a40c15042160380c0008101c0382d0007540c5c0104200ba11800050b000400281d581080c0001c03026000601044000ca060001102507281046003034411800405048001810074510901120180c0c0c00810410010000d0f60b0051700c010403460b42081842c0744c803140409c458400948010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 805043471 1250 805042221 805042229
    0xb031f0f0b060c01060f061d0409240b030105060f010807032d050108100e060c070201021c05070203250504020c032503030b0f0f21070914130c1509 65
    0x1002c910f00301c00c8407065000200b01c9101042100c040c0703541c1e8509443c03112504c1801c0f4043d004031100b048250802e0303001222554440c00004000c02e1141d85401c40d0308100d10310007081a0f50314441c034185820248201900a0b100319403450f040c000101c0001c00107580100018100b58981e032a60000749880624409442c1040110030b010038580070200d001000244904c480e03920410300307000030826440c4148180c1c1850b1401030541561b0385918032589500103441241140310784070603542e6424507410580c81c00301d41c503619143e4486003401003624288083c92a260f0b412240e10031102c002d1002c03a07150080302c0040e0303805038a070450190381c9419401101803a01281c0f1496000c04403c6034007950101c8890310079102000001e400c0018025800d0394103408a41050707541c104050f0a1419013285034a40b921103003800c40c1c1002c02c040302424010309500040110741c540400000d02040c0c88211a4800da11803648541011070b521002e88483d03146c070078240810701503201d22039603070b2243d92508050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 805044721 1250 805043471 805043479
    0xc1415090f03120d20092202040f261b030c0d030302030601110616030f020c120a020f01050f0705070f0b01030f0b0901050906070f0c021801090b031f0f0b 68
    0x10f41040b43c2c00100c254004c40c04038003041e2a00110340c1c040021540c82c21044800102e9090420303c24900380940034401200c801030b07200c1721100b0000c8000d071600003403010705205449000304c985042d2604688039020a460024160070088400380004002105102034404080031000c6040d020040390601c81007105c12a00145516441c0041c1501038000b54010306080c0d07a850042640b910426440707200554500a028a5a04102039140c3c4203800040313607000440401854464043c89503072405040c40b2124613100b0300032440300c0d010b03901405458403401c81c0400078081ca180100d806545c542008080320b051240101c2d00c030003030040c04040000c196500c0311b00f5440c1d030750716418408008041c0c03080840307203e503030b00c130000c0d0030824107000303041c041d01d5640700422250301d0f03080d0255640307040500c811041110f942c0c11329015a5888160780d10a0203e110928140d5040c240c6a8090b01e91b0780540c54001da020118441d03056030b011046c104a00280d060000d44101d1003c803d40140c49100720a90340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 805045971 1250 805044721 805044733
    0x4051008060a0e21030105010c1e0f02030123040b0a060807080f19030e0904021207090506040c020d090b0315041e060e0c0417031905070c1415090f03 66
    0x860b0219501015a018110741141c0000403800a100d12040710b4050700814094140300402142d40648416880c070741c880c0d04180841694000140001c0c1c00f4800c0c180c0b41c1200312600b070001d40c2003e00c100000a100ba800d61600f50301c2c4010920804040a000188a00d02c140e0000d180d5007041e0f40a800642445810740b00d04984d2400c07866230301c03d0840743d002e60301d01a1004402242c03034204880c140715507142d141c0181c0420740a04000076840000d1040e41c00903001c410301507110a05001520241080c0310300010241407610600c8100c490582d02001550301c420304d81c80c1e446401c01110403c1701d048900c004c1c0e0360340c4c8500324102c040401a6226410030305107580c00807128500f144044200109003010480f05507101d2407558000d006559072540014108801e22524000951710394000d40448100d030b240c042922181c00c200c0400411003400102d01280d0074080041c1d00118000030040316400c05021044440000e01e090110142c42e9545171000564188e15100c501c02903001c081c0003070036180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 805047221 1250 805045971 805045981
    0x8030910061706060108160c0c092c0703230f061008060907141201060308040e0402100306030b07080403020f07090204170a080a050705030d0203040602092b020405100806 75
    0x14151075511502550092000180a6504c1030040e980309810440c4e00c5140c03141c0b444819900e040e108d0340c00390703020580401c0c00b040c2c0c1c6000f80141c801d00044641e00f07030341c1d1a4a003080c58009954a214854107500300c60310810220b10050140c0300b40c40b150002c900e20180b0620220303403802104c800c034103080c0d01a08082008180d440d86089040394200815150320b9900c0b008101e850f00741c0b40c0200811419007403001001d40c1450380c0040d2401c06010b00004506850b03443c2c0400307641043d0f024240e403022003001c00c011400d1040220701c0b242d0150505005280c1540e58000d100000200708108120a100000741410b10800c074801850b40c00b2015070308180c2e11121031b03001a5000c0e008414030804403440c20000d1410000301d01013142d402c06607140c180b44001c41c084131158050781055416200902151000022a00c000e41c02244030341130059035001c00b1014400500114020001417406501010400010740d4403178146107541110006482d030354036442e5045443c041c0d04504050321803541080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 805048471 1250 805047221 805047239
    0x6060924090e270a02010f0516051c090f1206110f0a081807030302210c0d030c021005011d2203170105100c1203110a021c030e0a0803091006 62
    0x82615441e061640c1400f81030881010354520100e1030007800101c030380520314000c1c1c1c4a5000b6144c001032000001141400540b902e610b4408640c0d4076480c1c000200169214058204070703008001c11100300800007036440e03d0b000b09070010a0100181c2007a480d00420815001c4040407107860b4001072a60545808910a00801540080b100000d6000401813802960003001131484211b03503040d4002c00703903011155070320f28030b0030108404203044a03000e2242c4030f1174200900c0039600708500c50394005600d40446400038a4a481d00c0c0e003a0340e83c00d01d01070060140206040400c4809010f9501d42c0318152104a282078480200300d94141da0070880c07080030710806500030184002d40046460b003c0c51640c0b10010010012a40c00746507000c070303074803030a403c00040c03800960326178081707240c100000c0d05444010744107040e50240c5d1100006070000e12407582c84074043d00040d004690340b031408206501205000030f5440d298a10041c1c03106401100150b1000020080e40300c60420006082c40551340d06d207209 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 805049721 1250 805048471 805048501
    0x605040b04060e0705061b0307050703030f170f060607030c0803070e0a0f05010824030709020a1b0201020304050d020a090923030906070f030c0b091006060924090e 72
    0x40b582141800c3c003e40c01c10100240c0207065880c020300c0141f4108000c015034039034001801c850200d90009014200104505102100081d4000d4840c5840b034030040740010a0868030700010380c1b84d190164140305403e054000c3d1941e04c01000e40d02140d50710014101640ca4800c0e512006029220000421440b5030f4801c40503000c082080d103c00640790340f2900030300420304d41c6010301070000b20354000141d0039051200080d00036807100c021403441d045155010a003042d030b00b900440c00d142c0e000a908141541d01c01040d47c018a24407501d14180150380c1d00003510303803060780308003403042d41c0b2107985030f065544502000004111040302040034a20070301c0e03c0e4020b0700c48900300f0480240511411b0290b000b0110485e0140e20300180254a1304078580d40b80c1c6008020058150304100300504141c0029610f8508940501c0d8208002c107000b08585050350b00b6144c494100001700042e000003001034640741c500c03150090703070b002100124011a2203c00c0760010440c2d40214030314950f44043c0001c0000039211 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 805050971 1250 805049721 805049723
    0x30c0b07020c0a080a1a040c08070303051c09020a150302040816080c060403150c12050a050a150608011a070203120c0705060408060610260105241b03070605040b04 72
    0x92012142d5842804544880102c1300240000c000107088800b40c2c03031404030b401c7c1e009102e40703210408180c8070f2105a01c2c18800350012000f242c400940308088803071403600500003103142c0800f8460900b440d40481d0b0f2100c0300d4452107205008001d1800e0030607001c0d80554000e05024422940380e10742c05022010369003000d100708a01c900940c40c1c00006400e1031401c9400b925003019001e01c0d8160500035800007031003020100b4040103007410381902010018040c1d0350190340603060104942c18014a00400c40b501800d15203450036000b9010050103401c04a4581101c2d00ca41443e00c001300c0c00c0ca4002494840c2820007075040c0240e1801100c00d042e09005800c2d002519001c5501c1151038500b8402c8070f2007103001c0c1502641c802000102c02d03140015614501e0841481d10070b81600042803081c140c002c410000c142d2240c030041c0103103c5800e108000399540c040d402c001d008415100c0e07240a20358031564402001402a07881d03603080b00102001101c400641c0110108500d05e81400e042e05440401e031381c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 805052221 1250 805050971 805050979
    0x9221406041416260f06030d020c1003050a0b0a03080a09080a02011e0314011206051308040e0c09030a0b09060702010e0309041503050102040b09130501081207030c0b07020c 76
    0x1c0440b010028001041c4980300f06445a120010b0b10b90003641c031946145041d000350060324545113014040e844400340900000f0090102d94209001018100012803004c40110352040d48100c0c080e80e12485000c085171003c4c1030000f171a071111000300340a8410003451a40000d05401d000081003102d20050404140c207540c0e50150760780b1040d00c50340325070310740c400a0700140004480120a8083d90300c4082c900c0014100011a803002c00407400850b8400d9010424401c18142c4102c1440454040c0b1a4410381005081542c1040c0d983c85000d94055401402a60002440001c241c1c1c45a44200c2e81420300090403940341d41134902e00028480411540464a4000e49010540060050280045403402d035001b95080240c00d00030b0000030f025259000b240da1641e82400004601c0a20061020f84031030107260340c2c2c40203c40c060120402d00342c805000b000d072400004000c600d4022800703008031114801d003503540c1e141600301141c200c0300b01c1340c01030000201c0394140701d207a540001d150003407000300355 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 805053471 1250 805052221 805052231
    0xb09030c1f1b15020f120709060201060519090b061204060525140a03021308010b030618060c16060509010b0901060302071a0a1104080309090a060302060922140604 72
    0x2c040e101c1070381c000c101e00800c0040e41c038104003100509600541844000d6100181c01c100c1c9100884078059416209040406c0682d402403101da942070048402070302050303440900c258000303480c00d41102c907507128803d02ca03555500700a00e999a068100c076030b0781000c080c05444034103141c07c1050042c0425141014030003416000302640803d1690014501803160320b5140d0308594501050801d036000b03820407001c00d42e0810a40c0d81460088607080040e11404000140303144042041c185040d00c007901d02d0692841c0140d2540102c0d07000694158032007540c654240c1c807800c482404111016042c800246941d04000410209141c154464603003a41c0071034451070683d0361000140c0407481110400b03400e4008610707100b403621000c045600d400c06101d4500054902c0c0d025005441500103402c0380701c440e040043c0d105040c0c0b0344501440c0d00040c07000c3d003c0194a140d80d0001d0030764400d10450381d0140e400c4008266958204100c00d5500080400084c00b00355003c09105402c00400c45140e44100e1a003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 805054721 1250 805053471 805053497
    0xb12060d021503010b28020a06150f09091101030e0a060f090f08120f07020c0108061206010303120b060a0801030f11150a0225060804050a081306270b09030c1f 70
    0x1050002101c0075254005d40b010282d0703501e071080940754071400040c541c80b080d0800540380c040c840c040002003033340d030600140b4410341e0310345a080300720a11913140c101400c04244d8111060b011440164070307035020800003520018a0884005412240c00c00f914401c80406884e05101c2420002d0281035022400c00303c6541c3d910600703420340764041c1d40810069008124025065000d19996508618000c5c140c0e1802c20b03601d50007038949002600110b00080643d03135160328201060040380c113014001c80c1c2c0300b41000c82240d030007049000148006086024004414410301008480c565a41c0c103001d010703200200350410001159601041c036840041c8686216204000c1c0003605602d4110700300c0301c24400036840c011003180c00d0344000d00269501d01600e1064000514050010224600d40c0a88681845c1ca81103001c0e000c2c40c1c907640c01241921032941c500d040c1d80c40003183c05040d240001d500c652214031a201191400306143c101c0d581182d002020800d0006015201408aa5490341d401700c8400e54 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 805055971 1250 805054721 805054777
    0x70311100e0f160b16060507030c020d02120a03110712081501030501050d0303020f16060b09070309050c041107060f020301090b1f03180210090504060b12060d021503010b 75
    0x6040343d4104016048202440468070380704c020402d600c001d81d00c0100310189504d5280868400360b88000102c0d5030398140400c03464050000302d91311002c900240c9840890740d51026074602c10f400e00d610805a0301c059028000000009898400e90044a507030100340d1400c4024190740c40640d5092036003040c111030b00b4034030f610a000302d5061740c2c009022031070781508940d002c0e4082e41001050b10b40080f001d104440210581800d43d101c684d0084c40c000c90b00e034004d2414010103020182180f8209410b0400c3d04001c03410018914420800603540011001d0540c1c006900c14041c0c158010f05441c10301c00118084a803d070051410b88e141d010003040300d0002c05081014909105002003610f04034401c45002440c000c5e84110b10001420640203c44140760b80001c480e04c005990710300100d8008401030110341818403034031024104c20303003a29141151654064005802c0242140d2140b0140ca500d20219201c0c0840100d12869a00015440e0758481c10a14607507000044a40c0103885641400003844039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 805057221 1250 805055971 805055983
    0x10602010b040204061e0203090915040b060906030711100e033004060b06120c030414160b07080705010509100c03090804060e030106080607050d0e0703080906070311100e0f 76
    0x117143c1c40380c43c05650904180d00540000e003440505601007441049440e403201744045106407035030340f8000d561402c010204800c49030003003042c0707000369070500014189460b400d040307036004001d0382015865180042c040910302029403110050460812060b4659400c000000c1c05441c884440040c12140301140351a04861078062100f8a0300c4c0314030301180100300c0c0c0e40d10242e640318010b00490701d44001c00c0b20500c0c0b01401a2118805103500000304424808102002c01203582d0000c046c0001e080d08450000440c450f6004901f11a20f001458204104200c0c040700c69480d4404000c4c000d61608840f00340e144d401d801c0c0320381070301d501708040040c02d2032292142c02174299004000c2c034109810700500300c3da101c0100c24800d42540d130b641004110f0103010001c99124490541d1015074030b103280e07440581551884a98030440e980100030500001305560195602080f06942598940c450740c2007c65000500462004950017041c61540704078949802254285c086071045900c44071050800da580d40c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 805058471 1250 805057221 805057229
    0x90418080a095003070f360f0b100207081014071110140703060905150402090120030712020f0a02040c0c0c090e06250302090a1d010602010b040204 65
    0x50703801c60040c080707500031503262022030100d43e003d603c1141481c000c6440c2c18040c0c2c2185000b0745014508225010b80c00288088040706d03030300315004c56a400100306c15900d2828501004142c0c1703038124201501c50a520841a12500401c41498260114000307512103400e406505900d0150b410034030600c0f2094040c03200c0c41e00200300c6a48080d5210740003100c913240031000201090142c0300120148261900540e80c407012803088011803810690806811600b49a1017242010704000801c2a00f60542c041c030016030700305075405a660850040103c481e50103600c1080700e256800243d201c42100004094444240304118142103c0300b40c1e84183d946101150800e1503e0388990083c5006013400e82124180613920300703010118500642e103142c0c0180d103640001603400d907240300d0704039054000c10503c1e400442d8041890500e03c04440740540c020702030380d0f0140030316030005803c0c80d050b19454800401008125640e01141c001950606c0141d00f013841403800542c05d010a440940c602803007107800f01c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 805059721 1250 805058471 805058549
    0xc020f06070c02010c290a1d060c070c0b1201060314061c0c15120c0e01051813020c03030601030605101b080c07080709060f0b090418080a09 62
    0x68050740e0044442d82184003080b1342d002092100c0078070308503045100810003604401ca62546117803c81089007112000c3c1c1d10f004e054a810123079031002d0745012600302c0e00507511064030340e920b202d1420140f00000c4e55520030807a05800181c680602581410740c0c5050b074070999401e000030441c644003103540c440d0949a103503001031901c01c42000411580c0c0300445941c400d21880d002e5a035907010600e104074501304100089039000c184042e6001c864850301805170454180b01e050010740c0c45c0020120b008420074905a804022846d01d0650b5030080254000790310840305641d110858201d041d1640c2050307582d503011900f0440302042078a003260030064010525540c1d207090351040c0503800f000c6d1070007403401d80c1c44400405c6841144c0c081404040094030300c0d40000c040c0c03240303040065000c0701e180f64803034020568804410b0080c190b02c0c60403070715580800c84000c145a02843c0d0403580f841c1044100800201d030018850691390380002ca02e0040b030b000c4e00c1c45000e046070421040b00340ea0380403031420581 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 805060971 1250 805059721 805059737
    0x5011802060906070203011116020102070506030705160c090501030602270f0d1109010e0403080a0e03030106110f0a110a0f0315021308030703050301140111070b030a1107060c020f0607 81
    0xb103003008000b40a60900080020407111000101000700d5400304000740e000344540c0b0b01160655804000710f00c010714045c0c0d403552444c940f0100c0200fa600990880440c0d10a0401c3d0340d500340206c01160a002e031072480e10410895940c0d2030300400a5201d0003080c0b011164651103000c5406013401c1c0010611000352160300c03042040d0b400c008407440b107501d044609840e00d0380e41c1c90441d1200154540030308020780248949040c9410040d080240040c10300c11010b0400c00b5019480002200b1783c0c1c11a8a0f40c20050410b5440801311400e02c58109840059440351a08803410f2010500041c60852801d030b4001c08142e496805049076288907000c040e00c51a04400d207460710880c164000d005510010843c2c50b9066121210300f41140d20000b400d40002c0c00c080010300c44040c070780c0c2c40b4204802090a2207011201c065800e83e40340d10b0603110b407c020f0000880044d01256141e00072040064410035142d65803485440c00300e0003413484028004c01031041d59101c40509000280d094001c41242c1c0360000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 805062221 1250 805060971 805060987
    0x15030307020d02130e010e061b210423011a060906030103152d05070f0c0b1503070315061e14180a0b0102060f010f092012040501180206 60
    0x444c040b6610603409681d40d18185003031100028841c0c42d1084141c8809441d8509054504290b550b004c4a80c4008a0904200904c0c81204003030019503910450140c51040d0b03a80e600b82480e6225007000000082411500e031319a00000c190300034040f090315945140c0340881c8a00602441d8010311114540150042006102043c40803282e0840c1c0003840c84086840d440d41c411201d9034200410850103c00c0f542140d049501400f8040c1552100980c640343c448440344100060241d01600c802800415a0401003140d10180c0b8101498501002d800c0b40c104c01d5980c54250790081c0099002e01c6030515084001c04c00c1c100700218910b40401e001011804d007400d1101900041050242c580d0340700e00f0703007412450360700d40882915100d40030300f880c001a4002900006805d0501c010290961031541e900140680303d10244440107540f0002300c005080301401c80c80101c403042e1400d03101d000030008144610421303106502e042c82588200001d110484607010722174103003820f5090007035000105003d805 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 805063471 1250 805062221 805062229
    0xb0a050618100509270303010609080312040b181b0307080c09041b150801051f0206070c0c0503030c061b0f490b060309030304060e2415030307020d02 66
    0x17500800c0c0c0214441d02888680c8004a040c3c125001c1c0340b80035000032004000040d00a400030000f041c080d4080d52a040c80204091035072840140002c12002c0b00c0700100706892040c20040150307601e0f41b0112180c03a00920707000103039840262072041c8a4403400001003940080482c070142d00d003901624a45031603c40d692000300a10540c03410151400e01c000700051028141818a070042800351039031406541400c041c408003000342c0c0412090520f10700c2c03005421541c00506140d00400b1481d004981c91100c3c585006c2d582c4c8a60300c02540b501c000705203a80d01c08400303d4030034082e645141c2c0b13140d00c24800407041030741c0e80200307400c0c1e250030441401200800182400807a00e60380c130440d1880e05011050703120b100c940c500004032962100c41404818140c540903c5000a441070842d0700038110701c0d00d400d803d90b07a40710040c1300130b0006445040d003600c046410481d184661801c1412841e001c405022074043c8001c0455402800418680b41c060007130802108070345d1700640280000b02d42b040039030240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 805064721 1250 805063471 805063489
    0x8122a071e031202031617040c0306050a020f040b0901090623030709320a05060d02090609060d0b01091d0403081810020924041a070b0a0506181005 65
    0x54040c0300b003040d6451501c9030383e0f1000b10b11416401c9106062606480c2c401081607105e0180d07103000e4110702041c0b10100340d002c0382c5001285d91242d000f1a460340c6208060019016141c48007100e42c10120300491b011204a018103150b05080e82c440c04080c0d40da8200300c3d00c8181440001c03072403000e12001d10386843c22110095500c0905401d00f140003555881102030f0140348001101c0e4400148151519503a9924422600d00350086032801d00f480c2c10000010705074032481005400260740062004102d0300c80c10280c42810034010b18a6449244540035a40078010200c40d0310b0008440d03400c080384181252003684118001080100c2e01c59880c0da4066411000180a01c2452248488860103040c81000902c02081d0408005a1030792586000d109601401451030070711182104414003148104409076012030750b101601280000340566044000d01c900c11001e4042c0618404104181442c0e411060081d00c066401041165410011316440402030390051004405008100807e103800024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 805065971 1250 805064721 805064723
    0x4050901140a0509070507051213180f02070c080105060603250c0203030a02030a0e120d0c060204031b2303030a030b06040905181605100c08122a071e 66
    0x45038040d240c42e00006136138204c0803a040340014100180c9541000428032405011110500800341000080108c0c06c1c0c0800e40c90081c4060030f00046401004000f10fa0080343d00404803180440d0380d003041e400d041140c042940152282d42d03003004040f6107641401c108403031243d40f208060303900316070705480400351000518000000b08031107010f10f000541e4052008080c1810103400940d960307144241301600f1060366600d0380d48207a81c0c940c80071503805408038081f0700244082c079001c1140d800d1841c01c1c40090103140c1007d012240403480d0814600c102d11010b109503214503069110001c5210a144684140d801d40244c0540091000e40c4006000e60040c1d0346095004240c46d081c00c2d1191102000c81388221030908540c0f030380c0c02c540d580140082c806402200c80c0700d0032007458141410003081c0790b50103040488003046150325801782400711084c26106100e0301c06240001c14285002c4611150451084503a4101c1c0883c503c0d07203032540d00303d0031a0321007035002010030340307004444800e40808060414 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 805067221 1250 805065971 805065979
    0x9170705030703140c1003020c070504060e04020603190906060e0906071d030a0203122503090b0a0311070302010507020d09051f0e030f1605061c1d07080718020405090114 75
    0x4905c101c0d80d403660f208076441030066400680703e02074802000e04d0300c80b1a520550069160240c207009041c61642c0b5075500c036405568040d40d1751102d030703140c0c01c0c2d2145039010440414540803045042151903003201048034901b030790102c40d07504d40581442e00c035001070301e480740030991403035841e10b4100000d00300f1401918020103945130411a40c001c68103281d16031000e100000300c000b90b00120f284441c100c0f0b480c10031000035a02c60304640c55402a1a0910a01032184510340c04109480600d12039048042d015254900048e1242c540c2d14020703010b401c05440e2080540240b80c0702c00c2155100d01580d004031b4500800603842a0b5000d40e140d03400d0103000c0c95800802c28501c04003844e41d141088034000c48000200146000d0960a806040205841e00880d100303100403c030f0807046183d414080544110041c0000440d032182041099907150500032101240c001c107400000c002d240030a07500201c40d540d203400e80c0001e00c0c0c20842c00c00c0384518080d030780e0f1015042006004100c681c040e08450036102070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 805068471 1250 805067221 805067233
    0x3060102031b0c18061c0b1302030c10030c031a151e0708130602010216140a060510170703082b050c030a0e07080c012601060917070503070314 63
    0x2000704000c01d1000042c1344814a86105209982c180804c0000100c0b0250804164211703050b43d8580000300c01516030080d41940508000540d070f0240013030003120400402c0700f41c1440900710060f0280c10125010340100340703004120401c0601d00c0444c00c4598000070048004002d55403c0000c0507081420300883c2100f41d03000d20f00305440782200500d903060282c0e0401e40c94040600c400556642207407c24400c59005100020314200181031802425038400021074202e1020301100349051120500078000600341414040c001404441c1441544d5007600700d400103164052040c0d0f6600703440c4c40000d00f801c1c0f0400c04100c0e50310601c00c165015480310201444803442400d28007007a220280c842c964890000414802e0f20300c4903106000b08013101d403001d4038400c0d2810103256100c00300301c204203044c400c000d018010040003045119003c40c002d85901070072541c43c2c400040c450055401036001c0e1455210303540384a030f2000600c403c00c440d0014004c04210b811541c0e4a1825009590041424481c1e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 805069721 1250 805068471 805068493
    0xf030e060112020a08151603020d150602160e01142206050108280c1119111504060309031e080708060f090c03070c1a10060503060102031b 61
    0xe100340340c020103000d09811000c204500411440080c664089501d03603000102c0704926400100c2c43e5544441040b01c98411719040441c20b501038031a500d2583c0100c0d240c20055000c9034803042c4c505007602c80c581c1c22100800d2103602c0350300c1a011580241c0307140f40e0100e001044a02c1c070780180b203c09520043c18580618004140010750318188083c400d24064a81c401071040e540d2040c40d00d40c0c00f0071140b008002031404030944080904410340d003502055107404c400d01c0c3d054010720300001e0400f07890007280d0510000c94050825082c0e8a407088586140c41c0032606075500d0422940e200089494000e14509807500e1815802005420401ca051180003030b40700c40311201c070007201d01d902c072655100d0440604c0d107450000c1031020020300c864800d12a0540401b262307158a41143c0c0c4c0211106d05196690719140000c2d030340d2255140000b0801d800c03050003090107010320040c040c0078501c0320074450341107910f550b403d4070f0601040b182c49005a2042c40700c1910720403100211a64010800b0075a0400880 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 805070971 1250 805069721 805069723
    0x603080f03040302060f0c120406060b0f03010f150f0e2e27060503060f0d05030703030c08061e010c0c1710050603030901080928020f0a0602030a0f030e 67
    0x155120240c03048040200401d040d0180203590b800000600f40403039034038100111800902410302c1034148000004009070400070700d40d2169015140b480611a12000c00e200e090803240d0003402141034010200308006440240d00340f009480e480c20351205103809102c20720403107071b428806692642c011003c0104408215a80c8090726426403030007500d51000c41e0500000d8040503d001860080454201c60300000084081c202d209643c994640a40e0302d40710180028210b24451400c04e44c441141e00302c42040000000061003d9407081d20284040c0807101d4081c0c0344140101c0c0c8440e00880c2d0029041c8411611340c0c0f10f01016101410001c01515250720f8151007a0019000b102480070840c00e04285c1000401c10301c82c800088480521240c030b440c2e00866101e000d20300c01d07a414060000b000c9421020f0900c074034914203d92007190800443d07104613a06500312034507010790061010741c0c1c0c01005410024a00010f55105070001c40c900000b64100300e410042c1a6042e40415a40301411440100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 805072221 1250 805070971 805070977
    0x170702090123090411030d080403090b090609040c0302071a09070303050c16091d030430060207050601030215030411011d1909050c0309120d020f12011e05130b04060308 74
    0x80550117004842d17181ca400c0c14502045842d640003441f0310310381003100090348904401c040d100360030b01c0780380c442a200c404248280180003120341d00508006040601c00d41c9075002e0641207000358140e050008480c6a01c0f0785100e0141c9400100790410001440400d011b80000c3c800c112802c0100c5003039154102207200740321404d0300800c3d6042d40354086954400410f501d01030103070030f959024518091602c101c248490413816510a040c1404204002c52040c02c0704003459000e8004c03405550307449091404940341c0d8800d0004134842d485540109e00c8902c0d50209407441550321002d684040c80f0103c0055400c0101e0820081402600c540f070704901d500c4006001101c070070b800035000d401c1410604404162400200030044e21001030040141c203a20014003c20030a00d040c5900d942c40500c644164080e124501da85090168009050741c40b045603620081c3c100d4900c9003894102d010121001e00c05c0300005d20515a00c042d4064002c00c07888002d900c06110140000c10005190381e1741d9444003c650 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 805073471 1250 805072221 805072223
    0x91a04021305090108011806051005063403051602120d03050414010c0c0f05030f0a05091002011104032003010c2601150503041103070807031707020901230904 70
    0x34070581c420001c03414108111409405e00d60020f12045d0080601c1220280100e4800307444140c5071401328806a0302155000301405010b4500390340c40006210070003204800131055020341c00b00503202003401060280303a001043c1e065407450f21f007a001c1120004120a04c84d000ea0340160020605203150b1070400c0309104410382c80d00d002c500c520b4181008041280030030010303981d90b4108184ea0709250380c031500d8024a150312046190101c0141d084c1145140a1500052001980001c5500c103079900070010340380d0036104452500744080b050000b01e00342c03140d50400c0b40851000b400f041c4006000c0e00007031a1a03081860382e01c018110400002030030b40c1e41c0c08416a000c1070304240303120382207480c0c0840c0c0c0b140c00c10350340e2113555194502a00f0141d8005008061010490044041410454194410401e450303000701101c5816465650164640c4d60600c4111000c20b00a030001d072000300100c09032080c2e643c000b041301203140e29001c41482c044091740b003000340460400f90304011030b5035008a104e02071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 805074721 1250 805073471 805073497
    0x1e01030311010f020d1401050d020307031e0602030a09051603030e0d110a03030305100e150d0f0b0106080a1d0c010c150c39021003060f032604030c091a0402 69
    0x603c201100701c4507030030746c180c21080c003908082e0207400140e02d0001d00c1030300b00c1c0d41c81095081d620354106003110201400e284000c110a00001c1445a003c440341c01c0300c050a4061000c0d030784648840d055080c1c44d000c0500c4000c000c908030180528052425649000d1494002d109524403000e00100141d8254007030740089022030b58032000e002c01d05040020f100041d080031510038025040990b00824490940124184a617a9810031041004003504c07460300400d51001c1e0025095846a601400c4041c00311072008485241c801c0324100c001040ea1201c05000c9641e01400308091f0310801119121500c03c01522442d410102c1412440c100e4440c20140700e03c25500d4000100151142d48031030070582842075a041039480c0c610504c5943c20b0580079460394100c4d00d500610a03054001d501810003a03005180c4a4602d40000091101c01b000c2d542d011840781d01c0c601c0c04038154180d900e1440c0038030f02025060340100744d000e002000a03a44219468941c1800c0e40c0152044100040e080e81d00c10540c0c0245 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 805075971 1250 805074721 805074731
    0x1031407120b1621020d0912111c0905090621010603030e0607050618120f09090f100314030912010c0f0f17060d020d03050a02061e01030311010f020d 66
    0xf0714002d81c0c03120720180c54103162184058611004c4000c00030110b00000307a403039a00151300c070060070719644071440456001c1821007614002c0007019008100441030001c81e8000e001500b00c088005440c0000e0304030454591207a442c2c1800e06000902c0d500420303450300802110b120803106810078440f5008102b641c00041012815071400070013015680300694000e003801c1c444d5400142c4081070144e4807108000c0f040c40d4040100050030302e0300c128001d007602269030000e202e002c640c89030402440c003864103a6140c1a162038910700c500c001841210364045d080d4680c40c0a00008030190580405030900380d04403401c1c110348200148118048248111003070390360791030303a25105803c2800c49003041882e040040c01d40c04450005040c11002d480a03089522284000170466950550009600c0340c0207028000808254070300a07102c1d82c80009070101610401c400602c802581d0b0b0114000080c2449503410503918513075003030381c0304040141e242c010383d500e40c01001011441071010b0505a0307a03082e40469 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 805077221 1250 805075971 805075981
    0xb090415030c060f0f05030a02071a0106090f051203091002160f05090f160c030c0b0109060e01090b0d060905010b090a02190e0319030513080d0905040c0801031407120b 74
    0x12940a0640130306100c0c149031034802e041e80002c1900c0c0d100e407208034003680d648481c0c504010f1611560740106000071035403001180850380801e29909580b8501103003650140c0740c604000903400b072000c40031429441005410220700f070100c01e40070b480e902801210760942d03c00c0c1400d296100380b5048232440100a25080015182070059160841d40c1103954600d142020b484000c1000d2441d80001e080c405000707204130070580b084a640c05d415820000c08182c550b1110003010103485c40c0d02c10480e900007164000f08950051b48280948c012008020300d060001c81e80da8440941058002502d05540e909403550241e00c510b11103e1090007080380c01030340c445a05500d03a08404858022508211200310480c14039180010300303c031442c0c480b0015002e5222341e40fa007100c003442042d24011440500d00d03070008804500080400c0d2412182d100c0b0b980840d156000d02040311714030107440e00042c400e1001000030078203026501812180410588500d6910740c0300ca15519940000b044070307003812220402c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 805078471 1250 805077221 805077227
    0x315081b090a050f0f090a08040f03060b0a0e0615040815101505041e0506070309090f051302091b1b1c08040b25180603020408070b090415030c06 64
    0x20b0703480301501c4410045810301c1200038a0b0090000c001d03500090081011078071842c0100508070740107620402c031940e0b842c3ca07070a4a05d94203080340b00071144603007004807664440c5400f420010545100d1102c8040a81d13441c0200010009000020202c40c0810440880d0502c01880b00002c09000c000551001d81440c10800110780c089134040540018000c0140b010164010121411503c0203a070201402d21b41815181c40042c01e83e002c0740c2e120400091080406070040c1800d0216811442c0c2000051218050303d42501c00c1240c05a000c43c20090000700145041c400c2140c10140380c0c1800b03035400c501c0d28400c2c0351950025081c0817075502600c980b2004280c081005568424111284c8182e0507010f540107000c00702c0140c4002d0013410040001801d40046619010030907100c0d0b0703084a8894400301c405805003441500d910103140b80c030080070921a009000301c0307080343e801d10014001c6030701e0001c00120313076042481d4050703215803a049030352841e07200c40300080301550142d04141c1005280c05805 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 805079721 1250 805078471 805078489
    0x50d120e030c061803032b06090b0105070f03020c090a0b0f03120f071a0a0c081014100507060f06060206090d0c030806190311040c020a080403030315081b 68
    0x4107100758070010b884081601d40c00181d581d4203415401c4d00f9100c180c4040020b0541c0a5069060904000d19040000391200004140302c2c40c646504204485070305c40e102503098036060f00030180425020002000014489014048294045d1054030807640030300000409000d000d60b940740b00c15031640d00a1100f03242405080c0b40d0300100701d00400c030340307000414480c24900455400c402008400324407001484000100d00c41c51003040b4600c510700740751100f480c0c0d00511410f030600f80000c030002c00041141309500c0b000000c3d44d030f118400c0d0016080c00b0080000d00c029680e03101040040600001e0002982c0d4007840703125032206e000c0407410900b4150020318018008100415036403040406107080e542000f0b407807114603010b18140c54290368403400300b500529603006d243d80213200124000240711184052140560007160240b0281c800c4400890366500018005003c2800420003080002e0181c1e2000f07903101541840700c00c4050ba42e90b0000c4c10a14440015000f06aa69100c0b04140c03030102e4032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 805080971 1250 805079721 805079747
    0xc060507150606030b010e0f0a12020604320103050f0f0a1409030a0201181110091701050f01050609010203030c0c01090c0b0706060b0414040905010f1503021215070810050d12 77
    0x4104407123800000075101110310702c03c465174450f50800d18025505d654040f00c0103805440d07181030340a03401e0039804080a803481b583d2034400d4074524060213150320a002d0240209240b0440401035100c00c0100b49180ea0007804007207031030340d948040c4c0c4400e000f20130070207118012801c003540d2980c11504000c2d00b928a298210941980039440800000300360070000c000c904402d81e020403050714080020349030010983c204a40070901c404182104040c1504a03c0c0704500c40110010a66070f20030030301003180a28460503003da0014800514201c000c0005031060207901000492200015103400b5400342c01900b02e1900b4440c0028180305100240c01010010b084401c0c0305403a01e0f02d003901c03071030804107400c003251701c41da031215541400c3c84003d410203160b01640388020030013000580d01c02c5401d50807a10049000305a00b410170050880003080d604403210800701080b179241da034600220380c81d60b0003c010b1700488031004004220760311440180d0a14522400110150851070900580301c1c43e00c07046 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 805082221 1250 805080971 805080979
    0x30106050406050703020a0606170c1c0b10050d1505160905040e250302010809010e07050d030c121110060503070b0a030222180501030c060507150606030b010e 70
    0x41101952003001c07a0119007452504540302c41c0d45103405c9041c55a5854041d01481c01c00001040800c0344002261088110008949030907e2000074403450450203081700320300411003c910008541240030881e4030041e00700d140c0c110700361240d0008041b100c0c100c0c81620324801a207003141c00020742d80b05168121400c0340198510f94030311030008009802c81d00271540141d8032442d002201380020806014030f0701a00191010500007a100382508010354482030b8001104680482d400a5041c45a0650585808054214107040205004200d50a80b50490412420440310320101d4071300071100702e004850303035101444016100d01c914035114001c1d04510700c041c0340140400c03490360000348520455a244a0300c0341c0350701c25020290001c4c066030121441031075002004804c0494841c1181e429514142c2e941411121282c40c52003c48109000c01403284840701e0b010302030fa5002d200030300340261065107030f00160b804201d048019501d1a40c00701010a498100c454107568000404c0364504106903 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 805083471 1250 805082221 805082227
    0x81012020d0201050d15080c032418030403080a02102307080903160b04030f0c0f030c080c0a0b06151315050c0f060103020f0a060815010e0a03080c0111 67
    0x2030001524525071841c0241800340002c0d10600c0e404440d008480c001d10718604000c80203659240c80d03038442e100714013410b10074003a88004441c0c40280c412440b9000c00e101b0804402e0760f8034050990481c40c40808003610601c8180000000510410b004040e00c4905134080e01c0030304034000c4640c0a640f014001815014038544080c0040140303011000e03401290351902458503182d0300a039a09600c22011442c42c00b41034480000148901045010302461080e80c0f0780c0d54041c10504210b03120200d00c10000c0101ca9064070400110740f0074911105218011400f45280040900720036150042c1c0090403600c0840800c01c00500d407400b030308000803220121150714135020035420381d0301c100070590103605090b8030a0b1210a0040d8810710503500903011384012582d403107104e000308682d00c10b070134481203120700d80d0750f5811402c0c0d01340044c5003403c03200315803580c101a4035408491010b2000c3c080c60141080620448183c10383e595281c0c2400444c003460809a40d100c20b503883c00d094031054030325112411020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 805084721 1250 805083471 805083473
    0x415061401020a02240406022409030d0504020a0902030103050a031101020c030a141608031005060a080c0d0e03040f1a0a140c07090507050a0e0d02011d0d02060a081012 74
    0x1083c50340943e94110380c61644a142c901c0000c0c02040700700d414070301e041c20100c2c01046560300014501500d0079055421680040c04034160203c1c400110f590f03240c0c0350010b10000d40861205d4124030340152000700781d0044a43c03100304200880c0c00c242e01c1600d09070320038084081031540101342c0c8110440204005d5181100c0b1302d801e19036911130800c0c4a0100304105002400d07680c1d0260940c0c203108030309035a010018010f410a4111500241e644000b10031001000158a160000450341c0031105911483c041c1c1c1d840039401001604114000c0c0e040d1a150301c0c2d00c0d03a881030244014006081c0c40003078103450b40e09000c2204400c005c4003410100c0d0f05002c000c40c00840d0303084458060b0403000544c070107949407250078050781040c18603031014030300794101014000c1441e040000b03032003104903541d1200b00702d0892004010510340200b40190100d1006540200c0b040000504403c81807409040c0d901100156400308440c0c0d4011503078140081d80140a11111159982600000b4040c03100003100f407030303c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 805085971 1250 805084721 805084723
    0x1407050913020a15020c09181203060607231501030804050f2e112406010c050a0f02092d040c030501051e0c0a0504140402040806041506140102 63
    0x40d01c9885840003104a000856030f4075a0280040c2c202080a040c00d4446280080d64400c0130f0600c0601c51140c140004044640707000e01802030b42d0561000301340d60f0111b01c031503000d1540050032203604481c00700100b1005c0f82c80381c410124500d80031820301d0001100250001c0c10f244100e501410743c185024010000b04030400d054600b614400c0381d4220010b01910002090700264024910280c0c00c1d5180400c080d481d0280c00d080c0c0000240c03a00d11222610800203134aa0120368007030b1000400f110224440740d408450501c0d030024060505015201260b01c03814580a000c080445420b4644240303c0114148407201e107401485010320301003a806880740365100d608090314410707294111100000c0511190480f541c00664100000700710a060a06841d0307a180c10380d50782080c89000032408901164403010840b00421401c0d43d4640c02c20b400d1011140b50265407001d41640541c092002027003860302444041c3c0035074880c0f1100c043c0803200c45120780c00c0c1c506540c0101c0304007003250b501d40d4459030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 805087221 1250 805085971 805085989
    0x60109050f090c1e04060e0f1807020c190807080f03041206021902100b091605160606270c050702131e0207140a020a05061e0313140705 60
    0x22102d50903030741d440509800d403d000b108a04002c40d9042130f40001c81c901c0000052040d500b01e507594400300c90545c0b041c8001c402900f8502a0041c104010100c100c0c201440144d4210526205444250780e681d03001a94508085c0068800740d80d078100c013000032a00800c0004003d013041070203171011a6402941640340c0c0070798414915100307690180c00f010400750b07a04840d0400a0407003010107800b1844070083d610b0b42040d0090500503d400c424800a1074103180b140d204809007400200301400160048070607401c0418146c2c00b0000d031000c1e6800180070360141034041c00360345010b1018071044006040d1040c921200c048501c03440c01c05000340465000b81107554080d015940c904080b03024086840c01041c002c49810140018011005542503040d00140f0170180140b0f2108409070005442c0dc0c0c4420041a000b98131280e822002c0226040400c090f01d1700c210341c030741c1d0000c0b00341000420000d02d900071507508140041c0481c8010402003010814640390701440c00910006082c0400b01344911 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 805088471 1250 805087221 805087249
    0x3031009051509070815032b0c1e03030b12010504120c0314030606090a0e060f040630051f0e0f060a0f0b04060308040509090613030f0e100903030806010905 69
    0x8241c00080c0f24014440c1744810300c0040601190160784146581382d0f4107084481e40d114050801c41012008c15100e48440c2d0400354001c0b800880601c14040e861000e05481c6008a05040c3c42d101303c21210b940e0600c050820b5405400003060078601850560030196941c10801d00f030011104100300840d03480010390000342c000903826560394a0b18000651240915140759a00c18030003540451951b56509900340117070416104020903000745420041626524080c0d01c001000c00f2a45044041c0b564411040c0c20000003040c046001c46503e030fa40c00c000002940111070110440c8801c0c005d00640314807124403800c0f00c09402c122080d6100350740c4506020300446002900c8101c155031141003a44810041c400060040001a0356460442000d800c1031051a10803045000014124040450f100348100c50038201080c862049036001c0d01d644210688410400c2187c0c02c2c2d1080c00d07103850b141d580c2c111f01c083c1c440a01441c80e40ca001003100100401080c10440e0404c41044a9222031564405e02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 805089721 1250 805088471 805088477
    0x30705010c0f0f0e010c061b030e1f02030a0e0a0c05030c040606023d0506040b0f010f030e07170a0c050f151c05100f060305060112050709080303100905150907 70
    0x1244c40d480101d0740401d240902030040c80c90180c0c0500b840f00380d075400e1902c2d0b0380b40c0e0700d051140d0001a003c041c0c69001c80c040519113403070000308080e5040c00a038003c40d1f00c040e24200c00104008807104440c6014180842107a880c1100103003070009240401800e002428112402e0182c0c6040000c025210590b10891003c280e001c01c2480e01c03040c481c500e196528118440805100200b8244610050003040c0c6105004510341000b1030f04a041041c000c00014406845940103443d51138800c0340100711a0124411901840501144549100000402038000e01000f4503d8050506001c2000f48555000d90322030100081e41103c0c9440d2401d84001c01004081d9250722580300100c8045822448000d400d149881c0c0420030403a01c0000c142c22040c2c901c03681e08984807984511096048490941d26180843d02d21801308084a1003a000541d10840601c5c00c50b1820f60341d401c02e6032070340d00150395600001c182c102c4144482c1302d540c422240d105c4106a0001d00d008080000301d080707800c01804502c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 805090971 1250 805089721 805089737
    0x918260d0e150a0c1205040c0e0c0f030c040504050a0923010207230d080603100b040207152f03040206300a0c0e0a0b2505030705010c0f0f 61
    0x600e04148100ca12441c41c0c180b590146240c9650f01c41c004010038000704000c90310140c000742d001007092086512642c1d004000d0a4624144504500280002041c400c1854010098118882021f07006076018118603c51a602c032404d045c10013080c0c5030020700701890f9518051504c000b19642c0d00c1c6101a00c0307802030481c6503411120752102e019118401d000780c460360048249c9210044034000c80e00500d070020040e680307025000c20040b80c0b94103060318220791690040c001a07200d50407903803001d0040c0c003004100518000182e590301da112007414210100c402d90704c0102216102000d99180d05484220041a00c2c1252440301c104490102a001034060000800d0380c8500910748061004942c81512500882e001c0c40407032800359103001c40b604207d083c1044070050406004102c1d09d05260802000d1b10402c9040c2041d2409a0300000350318486240038400d01c2c0c8000c14000d0001d15198000c401559a40c105424020309484401d0150b804000c441ea082210781035200454840ea03034442e2a060007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 805092221 1250 805090971 805090991
    0x230723030a150308030f0c07030e0f041415100e032d0f01091203050402030a0b2206020915030c04090c09230f010905030d12060918260d 60
    0x20040a00790004480d9020b04540482072007140c40c080c51003102c80e10070203407480da03591003048014090b50000602054180301481910310780740d2510040007202800000b942c024410021039140f50543c1c0041044100710002083c6042010502ca168006418141c040d0301ca074002082d80d80107804295501d0128080e00034000482001000c508030700c50508803080001c0340c807a05802000307001000c86009641880030b080c0a07010f4090300c3d1042d9001006019009410f450f0300b03108640080a50340c2c24420130b2500c50365070004480303140f202c50280380010f0303e500301003040c000c140f030300f014809001500600410002552050446d015501d1b201400306c7c02c01011501591000b84036000442002d4082590702206400c40300c808420b10b1080340d45d01d03030704541c150043d078100b030140c0200ca805400c01c50910b0074a900400d00440c481c3c4031748c2000602d0301e0b91074101c9011244094100140000741e83c80610038030415071074009a0a008503120b400c2070a05040d090314601c58020582810b03926080211 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 805093471 1250 805092221 805092241
    0x203180303040801060605030a060e150621010b0c07092711040603030e19030b0606070218070c200a051c02040504060c030c05090306040b061323072303 67
    0x5401005a000207008036506c03000c002c0d1458100300c0704403802070300e0540009001092015194054600000200541d500650a2002c41d620250840102c040e00c5e03050b000e20070302e12003038160085c0b4401c26019141d400324000300e400c00496030300144285003080401303071907805d0320b64404a070300b48510303086010b080d0700b4509501306840216009a120f454a0000000c7c1500f00b031021400b00c0e0102e60414144e0315169031102d0510040c08060030310040000081e8032818004024010140010008030b00d4007410000c50145810455650300003400007082e01c420040c42036644100006a803542101890f10348020840000329840741ca0305c1411800c2c00da841d80d1341d2004008007400e40203803007400703a442d003802c1040141c82e07030300524800246018007100c1400d01c0f6005503230060300001e0281c891910f6a460303016503480098025030380034407044c5c8086186001885007600c0181d0001140080d0120342e190f280d1a80303c020f107000244503003210501c0b0801d1010368420399081a1408803a02c1e51111070040d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 805094721 1250 805093471 805093477
    0xf04020118090203010311060a0e040218030f100507020a030c031206090f060f0b0403020d0b04051509010905160608070f11030a08010e0a15210b0115020c01030c0203180303 76
    0xd0001d9081004085818607641d002503068034001e00d541e200c90001d8606000761840ba407206080051255505c1000d035141076001000302010350f140366070b40310402c103000a09007011010102c0e0140c1c03000303510710526406409150b82c0a6240d001030160070f00c1c1134501804504401c5002010090761800110070700059900403800f80041007400c004036405a0031b02002030030076000340400350089200003c0d106000c0790445040e240d018140b0107040020b41d4078088200c0d805031044403540100084800003003a1200c0320340c46403145a00120300b43c541030500d40d041c00d415080541c03840c4d96040c018080960001d129541003011494884101c421650b002c558656103043c0200c45400b00041043c0959070000c59141650b035980072041d01c944484100034200e40c1c07896030055080d40704032800c11800d250141c401d003200c807481d003030203140026503509d1803c00d4070260090120085420303440311100b641048210402d0b0b00031700b010403080c40c00700300107540ca000e10300408414400038141c05450351014029 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 805095971 1250 805094721 805094747
    0x4060c080a1b050312010e1603020c030403050d0504090f050112020f0102010908041d150d0210031413030806030a05071412010c080916030b061513030c0602010c0206040b0f040201 79
    0x4590100b50451610301e0b1a54001c641000812101100103e0754000300c81507280a2560801c002003680500b0702c0c254060740082c0d00c401c0c0f96000900000011071018030084e80c050301203689a0303075100c2c28200884216000c0c001c045c5440d07444c040040c4002c110301c61019441e030742c0480e541c085d03281a00d00103c2c00750500586c020030f88900410f0001c0c503450320f48002c0001850391101280e207992804180301b0314200f03400a081d8001c05450051000d401e02c401000c807101c0540c50045140b042010400304101400d94030342a00034003031048a824583c0c440ca40701d030041d0f4110042c00207682d1644070790f640da6115008100980340120109181c603074400d01c1003803070814007900a010421107402c6c081e24165080b5183d2046014031600c801c034046042486c5416a540320030400741a03100c4074107114070b03800c0083c0784038040340c01000b030494141c8800c1c0040e0000d5100d0040301c0101418104002d00355418084504107540c03041c410710000407842141103901101810811301d09a6072030004a408000c2801c3d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 805097221 1250 805095971 805096007
    0x30a12020f0c1507020c0301110a11100203040809120c01090314010b181506030c04060818010f24030c09241211120c011202040f08011401080304060c080a 68
    0x102c5402200240c40c3e50b120741c00c1e54083d10b030b11071401400c1c142a658020120612608100304180255000e5090960782c2030940c41113032048203045640c0f10480c0c1c000d40d4283d072380c0340001c0346456052070460380040d2540c1156015181003201100060300360385160100800340c0c00325400c0e410b090381095200301d8512030014880903640303501852180c0020401e44040000c0c6402c000300154500307107002103d00400c84091040d1600307203040401ca400031030241ca44610092544040c2000140074020000d8000403100c0c000798030324250700c0d003034144c3c1c40c03034400040c041070550070410201d48100c1005c012190306000100302c150b20805820000110403909040750020b50801042c410601d80240c0e040d0751003030800c6114110800104201c5540c5040041c8a60740312100002c855440f607001c05e40f80340c40000000d81000e80b01c0e0310000704046690002d4074039a5590094074040d22070009014010140c000c095803602e820315500405038001d0300d0b4054520000080c2c40303110240f0030b44041e210414246 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 805098471 1250 805097221 805097233
    0x20904020a090306050705040528030c15080115020c04020c0a06050f2409040f0c030b240d051203070504030605040804150306061b05120a03060611030a12020f0c 71
    0x100340030b4501c8900e400243c0c0e141d842c10000030080c0e4011811581666401031401081c140310014000e0652000100d60f2500c00c10b64100000090540301031001030601d000e004501c007105110010003851050f440b034800900d4103807601225070340204ccc1d0141000b030140c1e00503070b4403005904503502c2d0000d0f0f110002c0003d80780030708000902c0700420001d8040c8000c07503d821468110100007903840d44d201c010150340070038408080f8001400c0c41c20300e13905440c0b00e4104451019603984a901c3c202070119010042c0d00e406212004c02c0140d2864807908214044403400c81100c46500c40b0390780c45c02201c02c162014107001010500c21070094081c0c3d001913910420901040c900b92405010503001842070003d0003540c142110344a038028060300041c0c0d4030640e140c0048840e00380400740c2d039842c840d0381502e51307010f41200c088143e01c4060041098458940740425031a140a00003072003440c020105a000b50428000c40700002c0d40b120540720501c202000140c1c8a6106050150309445102c240d03030094411a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 805099721 1250 805098471 805098487
    0xf0c18060f0a08010906060917100c03051008070803190c05030403050a060f05090d030c0c06020c06010509070c03300f051f060203070215070b010f05040c0f2102090402 74
    0x79038000c08940109549441199a0718540f1101355581401f5801c08135168000c2845004103103480341483d005c24200312a03c40c660140e45600b2a071031140703207000107516041001007440e40f80050030020001500241046444c044030039031240100d220b08940300d2180d40c560420244078458050003103810005807607945079245001c075230b50210440c081320a64280454032502071064410a485443c0c18001740800000c0c60390304500820021001d0b000384400c140b1440302089103072018000fa0742c3d1500040000c0e50502d002c12940d82002407110702005201404080041e038410700d080450710355504042c0d0545048005100c81d0300d40080c205071601d02d0b12550592102d05600114010a01a134500f01e04000c0849648000092401140007682c003c004000044c2450704140c0f4203010320030115402e180f402c3e600d000041001707a00c842d034090107454041c01140781074842e4280d0781241d4207119000f80d140300c42c060807145002c4c014546050381c5814001e513111850b0115030a00b000100110768403054 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 805100971 1250 805099721 805099747
    0xf100e0a0e01110705100c030204091a0a0b0304020607120e060c0115082811030109080c1c1d0d0606060c06180803130c031a07080a050f0c1806 63
    0x1640c00151442d03081c14a01500c01c504041103403d40d40e04100a01469480103080801800d06200d0803810182d082000150b0400320b44100014075074a0117150050980210821401008a0300070342400c000410501c801652100112401a80e22404070002000504003c0c2d0f0700d00b94150541344c01c0030000138042c100c2a010352040c191058200c0700c50803a117850709440d942d0344601410904134850b54500c01c0b04008041214049a5481250383e081d440e00d50502003400d44000340705c03c58a14102050228180701c0a000f86003e0003050300e0310002002c4c0603c00201071015036080e6a540c0601c040c14071005031a00b4a2480e00190804410b01a8aa540b00000c080c02080c203001c0e5562490140d918507111030250b25510361540011100e030840e02c945c0c6070106140300e0044101c0d40130310100c80000000d09003058280600103140c0d01001c1620386500040c0482d400104405030980c5800c00b00140841304c000d445402030315219441e900c940402303500e43e00c0c0940400e102507103e00045000586482 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 805102221 1250 805100971 805100981
    0x121103030c0d0c0c0507090e010204030c080609070603140f07171f0b030c1801020708060718050306040b160905041103180708060103030e060706092f090f100e0a 71
    0x20720702e034208142d00c4501821a41e403180010010403d4002035010059641c9907003041519442d43e00c0014a055501c1d036602540403610b0b403001c3d00d0b90704008104012080148200b1000305140c1c02c0074003641d10030301000a58608000c0407841008141e2020030701681c402d4940184d09810400d0000d41410102c52050700344501800d40700b81d1003508000070607101c11100c150fa004a120307034a06424514140c601068584407040614114481c2c9000041c4840040000e00d006001c50741b11485040340864802030800d40c035803c6207009074442c405000022701c501c00038951000c07040d030800d000c01080c40011901002580e100a80c41414182c2030710811041c84000c500440000b15409440031902192503151112407103079031310603003060b00100b000c00d005140c800c0b180c40300100b000d840c2854503650b081c00c03905006800d9900180000e001c0d001101c1d10400c695a40c9230241d02008201c0100c00007407840c030740003015060001816808114885030f20b500c02400391901401040280ca448803c0c000140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 805103471 1250 805102221 805102237
    0x114250f05070521060105040504050c060a030b04051311090612010c020106050906011b080309070b0d09260405060c07030b0103210801050a05010f110708010b03010e0d0507121103030c 81
    0xa040c03003d104c10059002c0e5401c442c0f8a0a2001030300260303181100f040020980100261020300803080e5055107540e176007000700300740314041e180080e407140e000d801d003c1141d4000701060441c6c03055040c0c0c64003080c03900d1070f40c40d83d143c400c64031172104d5176a800104440c1c4601c42004400382d801d00180f40495074041d0003807015500d080d1005151030303680100440c0c1c012501604405402c00d02e0214002003603003d001507a2010300300c01100d5045945058040656015042e030b018410b680b4104441003020308440041c810907000e01c5d21041d8400c103004100d8501c110300c9401d01c615000207086890300414012000203517007051f808542582c0d64188991b02c0c120703062800f0140b0a0300070b0b9542440307000d044d585041e03901c0035040712480c4d400d0000556030603108000c0f0100348060040c2d50540301e101000450040d00340c180021030010b06000505080d5040c03038070f0380c40c02604000c954901c03565000b000d580c0300035004103140c01e00ca0501441a1480e44021b0009045800000108440e0f954100010a144 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 805104721 1250 805103471 805103479
    0x130b1303120e0618150f070f030302071203060e0f0f06060c0f1603020901080102040810050414070303112a0f010c0605100e0c18041d071509050114250f050705 70
    0x40490154080c240c071a120400c106d0740c40500c95070000c23a83d50700700e07170071107034841d050062810805440707000202100300044800a61640790912400800450003500004e003090100e01d40e04200344480c1581c080241040d0183c04042980481144200b0aa02c6400107040c00d035031000751a06501003400c0b009010030303406850b1000000800c0740f414400c403000c440039900580301d007007030b030f0f0541030041c04000d003043d00c61203a40056950034103810b0020740c1c01107102e904d5501c0385440c910101c0b41040000d903481000301c58442120445103898003015198090b04840200b005000c890068a040c0b281c100c02034201c034035201c20416183c0744070340460165030146400404c1682d50380d0341c2c46018801c0c49004a030960070410070171100c1c20107401c400b50010030030303221104841d250800d1034a0310710715a000c0c0c0007020404040242054101005030094802032801c858144600c414030030003442640d240d00e80544c0c49008021884440c408180d41c1d49a0029070007000d0340c1d50b41070255550815000c0d403449 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 805105971 1250 805104721 805104739
    0x7170303090d0908100209041e0903030b0105040f0b070c1707050a0506090d02090408090607080904060503150117010b10030c020d08011d0c0408010c05130b1303120e0618 75
    0x9000b0490390f0101d85401c00104804019524118080c0d0441c801064000f5101d041081040040c40c9000030f800024003000074042610742401404c5d50030024025061240411040c49480e20f4400e0003001e03100102c070220768900e03c1d407030000215017044d4405605a6a2903145e0001600c0102e20201101c6044812010040d1a6002c00900c0d116401f0f496a02128007041a00141400002103500c40d000e00710007410048030b08041600344e882288110340340000042c2d40c01084c50180300d450090207068004018269a203040c14904038010701594806440d400e140d000001c4c000d400120344c290001e03040d000380207072420028026040d40a100000741c0982d1801009551082140c1812280105110242040d1012849510400140c481002c0c0030b02008041400c030024003030392211082c5680c500741d640600e552880c03a5018143c010704816441045002c059000e400c1c0c9400c203aa400241c0700c040094141c400390f4030303880b0707015005030800c0d40130500f13010060710300d48100c402400507103840c09 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 805107221 1250 805105971 805105993
    0x303160302070b2104020f04060902091f050703111015090509011b0e13020a1e0c030c140a0b09012004080703060c140309031e03070807110717030309 66
    0x400f84c01200742528034102c69918516980320302c0300e03403550401d00141090714000151004241a00d5450b0007107031542d86c00041500c0c032420a000c00194a0342d08001c0014803081000b00205507100b42d00c4043c0c1004503103c0756004400742400864045640c00100700b10080703e8040103c0410700502c9605440c600e40170000c0d007411010301807c0c610030200c8420328000800c0100642c0c1582a44c0b0329690440c0000130080641100b41c4010811300305145c554000c850001c40704031001036190740940f070420840540060029400c03140b050303400c90f44107010310380d01d00b0400f07141494408080c00c0030f0302940042c014060b0f000d00641c007401e48000320784010009040900307241c046a10980c841c00c407695000072010404102d19034050130105100b8600300c82d407048119200c90791901301380c60b80a20b641001410b42d2403400c036011000b030402c004a01c000e08501d0903141c09400c1c044020302d2401031103c040d504040081d0144034040c0600003510301400c0440058021980d40c2c0c004407103c1201c0c0c0701da000c6507c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 805108471 1250 805107221 805107239
    0x20a081b040f0207120f050c0105090c0a0f0e01090504020612160e041107020607110306010b0a020705090c22050409060e010501060903150b01140705160b03010f050111030702030316030207 83
    0x1071002600405c225403903904680c0c044480303072215403010301049800e0050203201c40081c01041d00031001c0f01c004009200006042010450195208509034850944200071080300e2810250442c0d601290001703c07941e403800407969501c00c299201404040d0342c020041c81c0100b50b003010f42c09552640d5036644000c0e4003c00d000446514260014482c54244082001442c1000051081600c0b40c406112000e8112010a10b000c0c02a00b060700198004102c2d541c040c1c1e41040140003c200403540ea030124140b20482e02083d204500c2e10f03c01c0d8030060b100545058280b201d59200a18001d030042061071241e0410900502e130318201c0813040d50a041c000503003180300721032020590707030072000c1c450141904414201c020005200300e04d040c001c00405031440145080c001d07040486c003038000740c00071000440d11441e02544981208100da2410b00061221550080c01c0c0003c0c0e660a0900c00c1c0035080c429a140e00c1d50107032900096140c800080c440003842d141e17910704240b591094085603201902c4410390 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 805109721 1250 805108471 805108477
    0xf0501090c020c120106170a030210020306150a030b032a31180b0a15080d140403020a0801091505040b043f0e01021b0d020a081b040f02 60
    0x701005038011202001c0d41e10300b001580440d01d0b801000000c550350345440c0410095200c18a82409400c807043c01800d141e01884032210030b150138a011407031440d203100040c003580d6980803500406071000c2100d40c0101d000b0740c0034440a0800404071003800d100d200c030303291812420f15001840d05101c00c50029507818107900050041c0c5506410408408540d01034141010801443e104103585a1020030941028501e40c981c1e120f014800c0c003980e61916100003016034500c00030303003501501281002c100e1000f0104217503030300041034986000c10180d28402e030207144c0038a4002030b5012000340f00002e180c0d901544459501e42c881d105240c0f9501100e01824200c94007110040c1c109164100090009201d00400b07800280304e4045a131400c15100e000d4200c00c1c1311911102010b9206000d888400c01c0c0c000c0e5121a002c4030910080c0b40d030a0300d04070a1410242c8400e24240161000414402150b5800c4061005007406a00700c1c0d074a9080140028101240304013124012858004060003080541c022 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 805110971 1250 805109721 805109741
    0x12010e3a050310170a12081501140d1a190b04051512070206041403040303050706021b25330509060406030603170c060f0603070b0307030f050109 64
    0xe080000c00440e00560300c0382d20007030507072803600c20485002c10b034030303480a40440b4500c07620030062042012030711301076213200d508403030740020700032031100304801503400201180e8108000c0c13a00e010010441c1513103402d94064200113065042c02e0a2020700f40680a038520191404115504600c004000111140c441031501904c034520204010910550411811000d0402c1031801c3d82c0340340220840300e0021030702080d244540140c020341e00744400d10491548200400340007201561801d440d580c1c006e400c80c410380c90014100358010950030800f9900003429100141801e09039100440840c0c170308451404c69058241c0f143c0d16160000c0380110041e00584001d200048940e13a1025400000f01a06942c8410982c10043e08016a07a0706440d164003a0009022944000c87c209095203031020442c1c1c038000e405101c6180070f00c41844100000076441d50420340d8030310429180d488200200341040200c1d08900210076000051080b00c691581c050141891030000c2008a17903220007165055074a04d0f11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 805112221 1250 805110971 805111063
    0x2160b0c0106090e0d0c0804050907030504060c031b030b040e0a050d0825030209030c12010b0102060a0203090606091308070305040e06030718150509010303031b2303040212010e 78
    0x5e500c40c0e05800b451034112154010130104e07051075515000108180d400b2241ca000083c1c81c0d809000c20002c0c240210021482142800c1c440b803000c100302a1940c44001d00b503201015142c1000e07500e5504c0700c1d03011460f1022190280e41c40c1d51514244035980d0300c00c0015610001e80c60318001341d0b00b000c030300440c01d0000904140b881480c45800404802a410144816a06010740d01040c207056031940404d04062042000202e4220300440000e41000d01c0203000c00041c500410810010720400f05400f688000201c1c1c03910f00a45660b6148040d4220424000389180c200151703c4007450f8204025100300d032034001811900e0b0b9034003410f058071544944a42c414898019910720104595600b1041090f00f510005000c0a660765002401e1084280d0096010a40e1078205d40c844420f00d8206404402450828944801c440c120140400e140307061544507070800032001c2011592506071007031100d01104002d0141c036621800403910340f20800052b0400d0280012105142680c8482c0d802d881c51100b0703 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 805113471 1250 805112221 805112233
    0xb0405060f0718093306181a0a260610050901080a0b240c010b120304060528020d0e040e06060603071403040c1a0c03160302160b0c0106090e 62
    0x400080040c0503090451480d2255850402030558102c00d00d800c402c04c0c180401107016443c01d240a460800c03907841040700140030303c1c82401030880c8c0c0050001110070b01b40d046591a01507050442e00496007080303480d90f85012180201180341040380860003001e0444000c1c2400d0800b00c0162342034800c41660754081036202c0009841d803c050350228202d00c102402e00701c030600d01440c002400c03100100d102d08540c50003080360b0104201c24031562100250564100482c05014042035a1340d0083d84154000c0000000d4030f500307200e0040c00350621200c400301c4d545020207140782010b034036821000341d03410009000c1804083c1c00d25090240d00480807562001e0240c0b900d030342003840595070000340b00b401070103400740e050b01080c55580000c600c01e60140040c43c0307115060146c01d21082848020702c0410f280140424160b442020040b44c4008020313003a5103240141d513240c107030b04040c40300349007514403001803200040028032030000b071541c061800000c2082c1c41d115008035040740c120400e2030b07015070720007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 805114721 1250 805113471 805113479
    0x40b0105120601080402010219030201050a180807170706020d0e0d02030a17060f0d2118061826010b19181b050405010e04060605030a0f090b0405060f0718 68
    0x135944d4940190062040d144045502100c10800001c1c40000300d0050303549508001003034074144160100d0041c428074212132401540c440c018140030340c00c005050018242d0050f0201031361402124011540501d043d5111903155000d40000c041208512202380152070155032043d2022045980110b201e4a5200c00034803201000703d0f070f002005120b59003144100d00e94241695458481c500941d02c605d015a4040042d0140007401d684052003002c00d00c02520804400900800c0c084026200a4601500307641c901010a41c403ca05990041c08900070205250858550714002c032102100c85078001d004402d00f110034000c03032040d01380340c001054884000522009420343d0300720009611101000c90700c805140003048540c4100e180c400003084000408004d0703940c00807200044146c04807401c1080d6450300c14045d000d81f1000700400001c030b50342c440c003968000850b0f00006540f0340040c0d142e00c1c01e142510b0003030395a0380309454040c00d00c07100717400041c546071041142c850800c3c04003120003038252074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 805115971 1250 805114721 805114727
    0xb0901210212030f07050d0809061504091b06020c0a0b03040201030507020a05010609060e0a200309031b01050a1d1f020c06130b0907060e1203130308040302040b0105120601 76
    0x24000080360b01070b00c6200c8100d14184100068a100e1025203901540c450f030901d0721074581035010800c0e505000044d8108101100c0214107294170001651a103440e4402c0f080014009000c86a4028179451b9010f02d80001c10065440c0304c41a51038503002c6413000c05440d41040042c1d26a40324001c80080d003000094015442034000c40d030454040c0c0126145201c0c2030b07036440e00b510f946410098403240c4c1c4040801c20807a02c0b181442d0411b0640008001d64160341d000c80c5c00081107940310301c0c2809000004181c00100400450312001c80144101151000344240c0c1400b81c0b1007551007218060500daa00d60130346071900824a0500c54074001040c081042c8144c0b03d603880181210304000d954280192a5178903401c0c03040520030f00c042c0361011a0120a403809042142c000f90261409a011520500c0211340158040025520884034090424054034642d4503511a080140340b001c02552000410801040080c0c001d0f01e2084506000000015004490b18000c04020304a600403a0000c80c1941d40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 805117221 1250 805115971 805116029
    0x50a0306020a030204050d1b0e060d06050c040b0a02060604200712030b10020f060c03090703080d0e03040602070609080303310c0b12060a030201080c03071715040b0901 74
    0x702e8240903060070780e11030004807403180460003601c00e4100701000c0b4807032511400c103040140190f601c91111506080020641001014000074030007030b0b4480120744070300340d030500351001018500d41090740d80d15890b0000303480d80710a44450340900c0c10461001c200c0c08040034000003510b0269a02414a50107484d80d400001502003642d080c156191540382175034840c150b5400300103010340c00510b4101d1007061101c0c50010010328844001c903050003404003c26010038150f00b2039804c00c280a03104d110982c1c15600030031041541e031007144030000740064200d0300480c24404580c0c0c544c40d01d0312207a039148032154482c070003155100c1a00403040f00d0002c841074511015038410070400034004840d0426641d940c840103a0380c2003003040074070106207003071400b07000400140d00410030307180405a81c1c50350380041c0031401d002d4004102d6003800300024400504c01c145040c5a41c810094603002402c1040364030100c509005846400b42d030030480100f400c2e040c5528040d04072031803410614110800c92540d40031101c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 805118471 1250 805117221 805117237
    0x408070524130b0d1a090108060c0702030c030d03050f010f060f0c030c050109060204090e0f0a0303020a02150411012d36050a150c0b101e140406050a030602 69
    0xc8081c800100f04001003801074000d494082c1d00005601295000310344850102c0100140310301032900044c414504040780b4690850042e071705031500d0355154070000b0308010032044a2601881000c1025148943c190002070044644084003119641c84400002c900b198900924000c5080203440401e1680310720005020b41d8000e1500c020340c0c80d02a41d8940c20356000303c0054810702d40203d010701590010748610005201e01600400415840d200801d454003010b09015051540c04502d6500c1d4500030b000c03410700c200a11080401902c1c3c40c0c0b502c1d14034014a01d08240c000b80d688005490300200510480c0780001c004200008440c80b044012110848080c040708000140000c0604001507074100941132130050340a1908194203003814088611429802030303440200c40e10349061280c2d04140b0040b034003a003004524180e5034401e11440c01140483c4c1c4a481c003441507a5580454180c21310350386050b0380f8070308040300003550000104016a1118010f00358072410000d41000059102d0f80100049 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 805119721 1250 805118471 805118497
    0xa0f14030f06210c040f1a040f02091503071707080f070302040b2a06010b0f07080f0c010207021009050102120d0612120318030503011710050a020408070524 69
    0x1000b00031040f030741c14041c48000b802040d404420200e20301d1801e4054202c2c042c445150421118120f25510a810040540b6580c003a039691070b1110b880080540484440034005091240451a442100001c41e80308852240002d0010b0401920010b0554011402545140e0300c03100c0f81c1d206c5280c8864140e20290199040c15400c210014401d0100f2000d041484000a48580009084031040c20080340b00311403403882d0340141c0700500c40030001174143d07501191401c030456141ca8071850082d400340700d082c0840101d03c1c0d02090080749920305400800303015109440d810002c00c030451080c0c500440c2401344a01580089800f4105651024042d04104034008004111665918040300c00e00d180e0705005d9815460b8685080d43c81901405907005081e100f101d890401500c070b807401031090006001d4070124182c8041440800c0a0070082c91000e0202d0340c40c1003009090411080b0000d5005110b04e019034069800001010314000741310400c2480b400c084884d4900307943e65030f40c0490780b042c011001c034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 805120971 1250 805119721 805119739
    0x4080309100f1a0d0b01060f1838040b070204090c03050d02060c0415120f060e060f040e060c1b1903120c090e091905030a0f14030f06 59
    0x4404040c0155003410b90203480c002507185105101c140c0380e94421943c03a0165065103042d0700050300000d902da045500c6032401c41010b011010b0101e0314502d81e00304a0540c80d190901c00300d6050944100c216100940c00442c1007081d000d0743c0020300082602c20410b18000b400d11081250403400c80050000c684001d0000940c109503941d07882916a181e0410340303480c0e1008582d10022901001041e4105540e508041e052a01c0c0c0007101e0000528101550100440f1040340948454650000e8481d60010203040c008641c5450300c803020504210703003141c455103690310400d4050520b032182482102801019054035501d99100308110b84c020580702c0f85101a0b904041e40c0b054050003041d000c840c0950150510785041e050040280c00321415030302c551854041e0030a800ca0f0001c9a03102103581d141600412503075101489800c0c401000310946114032158407607410824040010078610246495403d001c82408104803500e000404070070203296810400716426903030303654196038801d100602400d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 805122221 1250 805120971 805120993
    0xc21020603041211030322140318030d1b0f0203150412030b0f090f0c0c0d111c09090504230309041b140c0111040e01060e010302070b04080309 63
    0x2920350040b2000d40719401da9084201c8500e50140510401150f020000e608504000c958036400e6411940000c00300388030843c1000411986020000c0512000030960b601c0d5012400c24181c646007000b071580c0f2a0180790000012103001d030120160f0715000c0600d4250309115643c0d41ca5010142440c00d0b40d161054401c200760b118080e840c5244914400c8a140007061002c0c040079040d9044020308070700c10400d480609002c0d07254604095031010940000342540c0e250020344142d944074000303240c00c072409544500140340e80c0001000c11421750400481b04081c01056150401c00702082c0d2910000e02559001c101949461b0003068200d4018015424418500c14910100041034500040c0940010884a005140038800c4006c1d840342c09110107042e41c014900182000f0703007003001e0750b1442000b00c0d0b2680140400d500c011408185d603d5096512501c4021203002150244038110000304920b0000419510a000f45c0e1841640310107101c40325100d0303a03194000e582005001061174890041c40907 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 805123471 1250 805122221 805122229
    0x30702071a0d0504120306090218010c1a131506080303070f020c030102120a0f06030506160207150305010f09110f160b150411030606042105030c0c0f0d0c2102 70
    0x14044c51068441701e003c4d0080480290aa4206911402c031881c030501031680002203580c4a004c0d8003901746401c4804024900d4034642c03402c400f03e000702494000c44100300c1d0080c8518050401d80c1d0003502c980b4520100c800403041950054041c1c600d8541050010403500e0303025030300305500100035005460758040c26001090880c0c004144d40c98070340d103400b001e03c440d02c5041c1c4100030621a10702c005001890440c1c40d81a518000078081601c03504110320711014140c4207000e900050802685102c02103505080c00074040c01f000c0c050603501c040e1403140003d00e800300741300e0111902c0c142110a030814009104442883e0802c44800d001800c07800c8201c4000780078030710200e00c0b680510041007034480d080c40603c422541c4280014116041c10424803520383d0301ca800781c800301c03450006141c4040302e103401181d0390140301e410b00802c10320002c29a1f000c56200451060034010095620341005031218042040f01c090198003d0400e014025040c07040d8507142c0951041e60400d9003103d440111035038082 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 805124721 1250 805123471 805123481
    0x30e0a09020c030702010306150206010605090a09110702030d1803030c03031116060506042306030109020925050405090412090f0905060a06050708040909111e0a0506030702071a0d 79
    0xb4000315080002c07081c00319a0140b00b020080c109501c00a0301114007460b0107941c1d41d1060040d00c0078000085611040303666051504800b81022080038010084041e1460b1071540040c40308030b110f40203569143c040140300301c0804c1081340603c550071400e18038648007a140e2031050316042c0c04147e125490307034488a44503002411100c10381c035200e075115682e50070160300302c44014180c11b12a505010a41e00d0701810b10385a10141e401038601031202d911500002030042407500c00c002d400c0b041c00410801c04010b1200c51034142c00c480d11240d135007072082d248116024429400340720307440700704440844c0c0407035090000d03980b4000940c140315008980f036451941c201001503100d0f40005032120100201810044403100041617541411380c113201c1a603031916000d010390300502d000c1a5070380580c0e10600c80e071000a0300d0b1103a0060a80c107100b040c401c0c078440d4460282407030580902496040000c55041c0101124400c130080c0d40506101ea051001c4240024110040445a8441032100c0003a00c40d080c422 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 805125971 1250 805124721 805124737
    0x3060608030921190b090d020c0d031d1c0b160c1b1e0f050307030c12050a06020d0212150f010e060f0a050912010c050f0901051317150112030e0a0902 66
    0x145d4506160048039503180820200c102400c41d0041c41400140352110807508018643c0760505024003196004912414010009007a0303001e00301c400d10b43d10744801109140489401040c1c40350300ca68400170040004100d045070340001078000146070300403035001007a4070461104110075003040c5940d4108110a084800c100118110b4801d4040080e1804201c84000801090700504400392071501c8480750300000f80704030607001c0e101114190410009001d1181704590141045448001100540009400c03030b150f13044800e01c480d80840c501c1800d0007250005154001e128a200ba00d51900440e0f854500d0070380301e43c225409112058020301504d018106014280d0346190302c41c00640108078201034102c461000c1e5914000c8001e24a640c4142180c0aa2000880050307036201c0c0e000040310725104202c800000214615404188410348183c980f40e449103110494101d00c814a0a09802c54405e10400c81114641044200024040d40041d000b81d4001010406020342d200940000d88e882445 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 805127221 1250 805125971 805125983
    0x6070201051006080103110118090e0d03050a0b130b0402040e09010203160503070c08130b1b01050a15031e0b1e0f01080d0e040b06040305070306060803092119 70
    0xc0007403241c00003410b040180070600c3c0a080c154555200e108400f0011a1350138108216225402c0c0d00d20b0340340004000600300010104042020300c48616101d64170990318000003814400031540f141c2c80c40c09007180303000d002031445170740c4110804940014607890f080140c0040d028400014000d880c800600c5c4107203200e000244c1c0e030749000481c98039403c123100c0c0d80701c1c184030092007400002c0e540041140c014690040c1c0b026a105245000c49000f004142d12400c14042c0c0001d240c64404440e100c0150354034030010007800581c54010f015015101403040030540c0701003620702080840e087d034401c030b2001e00c1e20703180c07000f4071401035141c181140e1411100005030324a120b0300e901c002d420002902d0fa0041444522900c0b550402100c161a0140c030700404c0e0820040f140c142e013003a13840350321a00a0b1070000703000903912642c0345007031611350090b0300c0300765105d42c41c1c5840002d8044c000320448881040052841903144000c04510b405100a03640090282c401c110794110800c4800b6990540180140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 805128471 1250 805127221 805127231
    0xd11150c061003030507060b0409020904060e0c100f03050606070b0c03090c030c0a03060c140d140105060a0206010515040e010902190c051b01021203250f020601030204090f0506070201 81
    0x21007072030610050281c42260503840b00c1000070030313480000e542080d94000c0e80030441c03299141c0050094800b408000c1e500051650a00c010024103a00480180c40440c0035242d03284c25400c2001030700150703281d98102007150243e050410500c2035000f41c1c0e209800800321130a100540e1100528031000700d0300c07040c15100000600c243d0040400408030002c504800414400b007407400824209000c5100c028590b941f18440440058005c076039025483e01a030000b141ca4030307030045502c000b03070295514041500320780c04000f20340780c2040da084030410151a0003d1400c0c0e407809052204030403054280d049800410312001c9203101e800c000d07060003062908400b41e103030107800c12048042240c80c4031390300c01c4c00106004000002d401040c040d068000c4000460580c00728080142d0916541101d102c4003507100000300581c600d4906641400d104210242251440b01c004040d00c0600d030b520a030801590043c00100014a0a034200744440b40c40f07219000075000c20780da2901e103015070590300310015075116 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 805129721 1250 805128471 805128487
    0x3140703050a023306041b02061014030717030408030d05061804050c060901020c090f040b090d090b091c060504030e0a030f060f0b0a03030f080703050f060d1115 71
    0x401a28016000e07510420304c0304080e49240c8074007078440042080040d10f010b00000e40d0b80d62103030300154811201e0003000403410000b800094490f0740c00c40301815114480803020601018189181e0b05000002d4000c080081c00c0c1045445e0030719014144c00800c2c88104404503004105001900e06003820240105040c10300c002004060800520341c0c800000360b01d8100030205000042d002d5141314103890450b9103102200040f0b0801180354071207600509101300340060310001180703951290380540c10320242a210320b00102d88803010780304c46a0005000718814001d007103c02e002407014034401450311011012942c2440c2c90f402855074240c54242e510300800c001d1503040f94424031000b8049403485a11821a0f6802c15080c100d04405401595104003900c50000182d001c074444600c01056034410540d2850002d010300502d082040c000b50000000c40e6440d40240038481c040d4800036180c130030b141d0350701c3e0501c40a00c040180039201080d40c104003aa007903c0b101d040505001c42c1d121156036074410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 805130971 1250 805129721 805129723
    0xe040308070e0d0f06060f03050f010e030309060708070905090c0904050109021603050f0d29010309020901050f1f270308030f0901020403230c030615040903140703050a02 75
    0x5048500307110b241050080030741d644000c000b40d038540c4148541c40141160519100514041d041a100c0b0284105c01105104000a080c907040c900c400090200c103200c0310084d1b482e40001d40305102c80e584044007103926035000b210280c1e840f620034a080c1101503030701d40010310480c00a440d070264141000441d805107013800d0140e50301401c00c62005514000d680c0141a00600455901900300100415185580c1822400f103d2100342144024030114410f440c5204541c200840c03401e40001078140c5010f0154002d000d81001e1640040c041401d40e0f10740750600c90416170034090b065102e1902c00031401406003203802480120460b54410702da8900700521000e40d42c2c0c0030380c1584010005030004000003845442200d503c04003800000000c1e46843d403000e030290085803c018503400c442510542c40400602240801c490814200d44e001c07107a160525031600419145a002d601c3c541a00d202e45007400c1d085180744510a213451080b41d4401c82c00980b031500004422000100005401c01d038a50b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 805132221 1250 805130971 805130987
    0xd17070f05010b0d0302120a020a1a0906070806090c071b0f0f0506070c060e030a0609050d090e07090911130e100605030c070f1a0a060503070b04081b030106050303040e0403 76
    0xf109403485099004503850295031182caa1124040007100062005c16076482400305000e5250310242c44c00c00104080c1500e9000d00c421958403801d8400d06001605483c850071140d4012003000d040140b454540c1031382e880c4c3c5036101030801d82e01b410b400e00010101d00c1001e8003800c000d01c001c1590450441c200754140708120107603403005102c3c03c400d104001c00710700d0400000044a0160074500e0b1202401e0010038102900100c01802c000c1c90065038805020700400e200503080c2c040da4550503101d0301c54001c800b940c4010359190300010203d0b142405107250b940d1040350103500012030b06084c81c0301601e221952150302c2d0081069502d0b102c003800500b03d00c1610302c0b03002c5d10b00f904010b410b43c6000c41c07002075213010342c29001e03003400341441190043c0045564902044509100364600d00c2c54003082190191149202c0c1174000c0c400d5190006003003c808080c0d0701a102840080c20b1001810300c00310f4503600c0e80c02c4d8150303419544d81400140e0f65404000900c020f0020b448480100d00c0c0505020f0007442c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 805133471 1250 805132221 805132241
    0x201030506040e1902030f07080136030305040c180b0f030102281202030a151e030602070203030c07080f0c031c0c170f070209010b04050d020d17070f0501 68
    0x14104403003c11501d80c04225000c1d03402d68014a0000418103000107482d040403600c2c010401e004000300811601810b401071038500300c1d0b078801489110b04c0c2e6200c42e550500c615a1020221018003444000070780300340c222540041c05103603072403d40c0c0d445140c5441710038403070001251425501c42400081d4144032500180325141100218105140c078000b420091190b540b00c14846d03c01708000d0030086000c0c0c202c07144000c1c15440c003151281f0b00210110000d04400c042c1100300411910300251400356000c1060280301e444240c00e03e028950b41c0e4aa019400c0b403c403c90307150005000b5000c800750204140c0005100c5400140595042c00b0000c134181107440c0c2e021800f940185008209000754160087c8942c9400e180c941d0980080b42481d600c81c10540318241a0004c000a65101e041241c0010380701c1a4003c85400041c1c0c0d80c1d0722038020311407081d40305031130704800d44520703800141c904105070426041c040c1d0309200c402e1041e891807200c250301048003254114822006070003070040c00d1087d0042c1f1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 805134721 1250 805133471 805133479
    0x807020a0c0602210c0c060703030e0601270903090911090301020d050103020112020c0c01050f07020409030504090e0705090a110f2a19020402090102150901020c0c09040c06080402180906040201030506 88
    0x514910303115a02c0f00e040d61b8065020b14000138144080500c070341e01110008c620748059901d41e586441c1030f10321480e030140308141c1086503142c114502d4141340c03054001d4250305848034800b0500e410001005482c43d80315030754004105101070013440c0c50a000400c8494a46c5900140c02d6041d4400504481c60b2514000d00c0c0c50b10601022050f9040043c41c880340d000c00742040b41d11801e280d5040c982500c241c100080d0080d0030000002d0806030844041c7c0b05403405030f142880800d007010743e2a5503418092081c1940141c258000c82c0310a4100d070b001e10700e21500d0348820783c600b10640180f8040d950100090300d4401419480b0301c0c4880020720951002c0000d200054802003045100810aa05070004c1c0a403041d50700080c12000c60703008002c102080c840e40394041c00586070003845603001b500044d49401043c0101207000c0d1003440c009501d180b24a512402240040d030030460b048a80c01c0700207008a030030250852500001e40007682e441c600c101c0c1003c004000e039180501c0014161340020301402c0c02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 805135971 1250 805134721 805134727
    0x10b030709080d05031513020c0105010e06030307030207030f0503070507060905041109010203090f06091305190b0901060503090102040f080c130515060706060b030f010905060d020d030807020a0c060221 89
    0x104551000450360880c80b106c1124030003055440018590542c0001c02d00c54407440010440000b141c1900700c01c0c1240d0304d031440c42c0c840365a903405060300d80c804c5420080041e081034005100040c1704406d10417542c1c0c0a80120303400c1c000113503100c900c2e001d0540c210501050034454100305c5480d050180b4030014950202d094209500c500010750b590040c0d080240c45058080c107040811b8955109903400014000c1084650403000d10b40c08000300000d5800b4081059030022140303100295000381ca20005024000b00d0680c1e1a0103002c85a030b80000d0050703511035400700000035001d402412002c0c01b42008101401e10110360703500300300005043c901c1c1482c210f41003408201800919003801a4141419941d2550f0340d078580c50410010102e80d001490101004014807280914115489060f90381e00750b4100000d0b205e582c20400503456000009611240c0380e0030b0700b00041e01c6031880340d070812002e00484010340410780e50201d00c4a1036800a000582c002c00141c1122805034080c0d85c4800200500c241ca = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 805137221 1250 805135971 805135993
    0x121b03010212220210050904321905150301050f0c0a0c060209090f010806090312070f03090203071502120315091e0108070f170606040507050c0105010b03070908 71
    0x20341c918001c1c162699154910f69150f04010241c800c80600ca40c01070070581c00f180385600c0600190401d80c5e84a0040e40740c49000300500503600705106401e0351346034001c0742c8034508100461152800400306404110800c9110365256154003030303503000d401c3c205035100444490209060844034010201c0c0c8200000301e05018440d803504086a2603010035241132064075050342800d001a04c584000350750414044d40130450441c44400d4801d06072401801500c490f80c40d811f160b44c0d9203000d41140750340301c0100740020482950156000c0e00140c1795609010031840c1c03403600043e003010707115807101c03002c00350b50081c40700143da05201a400a481d540c20150450800c800050050840c80c1c0d0b0682c040d000d2200400c1021024009a55120601d540c4c20f524541c1c41d03c2203252564094895141080c0c030640c000303d25040d00340c2007003801c5c800f05030082c0f40d584d8540c0104406054060046410311104000c80011a2400c1c09010301a05000301c1c015642c1c1440440103102071041c0d4041d07a615000303801605 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 805138471 1250 805137221 805137247
    0x705040510030b0f09181608120406052709041a01050d030c1203110406090602010c0f05090904170a081005060703140c01021b0a03080f010f1211121b030102 69
    0x340090f43c050340d440703485e40d41d0060480c0401001e00940380651041c0860041003203004211102a1403001c0c041d504200b510803107611181c06140a480302144050004070300001080080e5a003400000c10940f90345442003000c01c01050082da41a41e01492001e4088001059407002500404083d00ca04040001c04c0d04c0040201c0d56409005119003212502681000d00c2504142075194010500756601c0f0364a07040079044141a00c2054055402c00341c140c001c1c240034130100303445200aa180c252030302591808100040704001d208866150044400040c0b05109034040c0c0920b112a481d2000305007445410004c0848007580001d100c1d05081007190002644804c100ca094034403e070b079031900c038a94104680c0c003a010b41c4403008904240c40150f10103074440055030034401c2d0700a8883d90459251010100001c0e442401100944480c242c4100150000390720760380724070f901801406c1055501d003000180d01c010001040034079075201d8079154200983c461b00f07034030103003070124004c501e000d001031101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 805139721 1250 805138471 805138489
    0xd0806060c1b0607020411210601050d200a0c0209060a0b0708131212030e0105090c130902090c27090601111e0708070f140f0a0b030705040510030b 65
    0x10b0008106000902d0007540b0703a0700581d000194002c00501c0f0841220300c0c0e001c02500008920895400103a08641d0000155540203000d520107039206460302c0c01e010340000c0030f0034204a1031030100307810740b090300500503208005d004140c00c507554082c0340b00168010007044a03006002d951003003001001c200664401081102c0400d030303211030840e0f168400001c1c24401000d40340d0207440380b00314914000e0300f009101d1414560500144d00e0400c41c45088020060803030b1412a00e00d4040c2d806880c00002c00e00d40000520440e081c0d6060210f002d00311130380803074403006c0e0580c1d9401c55990045a0a401c54940c04408021039000c0b25034041e0b00ea0071030000410102c40941072505014180620b514130784018441c9500d06181003000039400003440800f10703070b290307010f22407805580a05a00400d8140100c0c0d10700b03048841c00b00c582441c04017108108000c40d5002c803003940c0e10484160001805440c104061807060f01c80d42c540c1620b0340d10340001c1c070850100c045007070030405281c660105107903500c10f400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 805140971 1250 805139721 805139743
    0x21e0a1502181203041a040b0a0507060e060702070611010b030f1024031203062d0b0f030c0a0509130c080105010c0803270a2405011508040503040b03090d0806060c 72
    0x1b142110243d0b146030409144a29042040e03440e00004600b00d1403031f0400002c00586100300402c1090300001108141c0742c440540d000d000507004800d0401c5628403820b0403505402c038071000000c403c1310b5003002a150a10f0700e1a00405504540307181c01e00305503d407082a12850034844042d00d40c12050001c0c1446c02d1302800000d100d81540440f01106512a40c807041c0500450007840500f0400e25040c2818039070320b0602ea10041000b000d01040e113401840039680c000c03104528850441e16031400d469500d0b045540040c040110034440c03065980c2e12026018441d40f1031a40025403003042c80030003812250140c00040c10700c40c01000c060001072a030000c40382c1c844020410030011102c5180f801101c8400d540d511811032180758039610500c400d80c00e0042c0c21710b24040d80c201c0421900b015403410b98200340b180c89580e48400c10442c2c101c034000c0d0b01495000c1d110384c041d00d14068413510030b2849a0029103841149902c1000020030a982100c24660440e100b10360641c10042c4003010035a0302c40041007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 805142221 1250 805140971 805140989
    0x3150a1d250503031905131e06050406050706240b04090e0712140705041e1a0f2b0c05030d0e0a0b0a030209030d0e030d0c03021e0a150218120304 64
    0x36045d40074800c10030786050000c9500c1031364040c0d564200744030716049001c590001d84101807200090881c0030300111403c513020f644400e8201402902c48030000c01094036100c0c43c0b040c980204004684880d003000d0050048540350ba40c0721420a00440c045580a00080f0003550210005200c1c21305810a48202b0b01d920150008400300c0d40500c0c141001d1a0754001e80e0001e0820714130300008c4640d44011a001d2009200c104104009034552401c0c0c0321070450099004185505003404034102100121038114404848143c0c038610030f00d0b0542240c165000541d40c07258029814840ca20f81441100c440c9c1c040f500c0c004580b001d1050000d060b620003441009010380000410800403402601612740d02100241502d44000c605240a4640c02d1021203891182c021024006aa2805082110300d40c40e0194001d00c006c500c240c7c802078030400c080180b00e00b20b11807101d9010001d140b80e41150410003000e880541c03a020110710f02c00c8002469110907205071a084010810441c002060f60102c0726140c07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 805143471 1250 805142221 805142257
    0x304090e190602041707050f15071703010608060303131e050a1d070915141204050a0b060d111507080a021f0b03150a1d25050303 57
    0x100500d00d022030800d4451201c0000051003010701c402035010b00100c40c0740000c0c1408030240e8604c0c29032aa00c403401800e40c0422a110011902d051804000751040c10320b5240501c0e0644c1038495222600d440c410240401000000503c0400e500c042550b4000505030015420800c4000b4401141e402a010728100414003026140c0325075100040800100009004030341e019407a254500103501e118070b92107040040c0c01e404684454850415082120a030b840420b02202408000325000f440700d0b003000e41d505500b4407206000c090130780c2c840e41c0102c1c40b40d0000e01902e02507144c000b11a1800410007841400b0540c2d0354404031358190041c2407450012039005140341e90340106041a4040e282c005071502078081614010107400081181008403e05450086405603a40c000280e030340e84100160076170040c140784a4001c65243c2d00c03a8104480e56408a0740c1019011001004051064900503940c0003558a990410090340205e812900c0c811410300510300f0b01e00403035580e10445004044000c404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 805144721 1250 805143471 805143491
    0x8011404200a05060c0307060c05090130021210090507171008010e0f01050a02071703040606091a01110c181b03070918090b2e0b0a02160305030409 65
    0x404000b00160a0003001a5103401c81a040b6583e40d0b0040907044590703524207101c440354640035038242c841c83c0034160f40352500c400c118400808404c0701c0705c560f1145442e0340c90075a0003082c0b507070000c0d050301941080380d400580b50000e0250904055030f4403070501c482c07038081801250765008800500e030200e4a0000070103138032420b40a901444e030692001e200c80d480c002d466031292201080441d444180c0d91300900c025102c001c1080120b110302d4000508002500641201c9500c5d210080c5074050b004920014009603a2060a0191803401c003507060010340a4646400b25a00320440c40c3e0803140302c0004110b500700f40c1c404224000c0903038103648407428500380010f00041c5440061154680041111510383c00e01c0e5101510328030150003000f03003042e540c400a2085070281d200f0100b00070f0300403000004a441e40104160b40d5204180c04128a0300d14545030402040e00040a400422401d002c0c41d47ea00c2c1007100007420461a40c00308220a620b65804001142000059078103444c018240007480c07084d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 805145971 1250 805144721 805144729
    0x914060c030d020307030207121803110d02031204090c0e1305180a030e090a0507090509100b04080d110a0c23041404050f030f190c08030c03010801140420 68
    0xe0b4004407482d8600020402034140d6064014001041c401c1402400c204014101980c155482158501c0081035a070000c1001c42c04a0132000300c850b0000c1c1a0f40b41504c0c16401090510380c0d0003500c0c1002000001c0c0810010209105102d1030f040766103030164048455a0000310090b0701210f071300301c100740c07500b0204010b500140c84c0c450081851000b10380d009800c6140203040350045400d400e00c01d0200100150301001c80e4003603a0b128400c2c41c1e507401c4100303003424100700c00359801030a050b0441586d444046440d08540004002510902c001043c11168021008001e07900070500d0100795005010b6040010340c21401c00c40595256406040c152084802c068808001e4025190341c464104030b01c00d0303240d20006081500450044068502008011040d941c0d60310551145644801c0200140000540f1010b403601040740603241ca0802c4080c691514401900709461960a08a00100400120310b003480381c2c0034056038081142c0303900c0c03819403034441411012404241c0002c0d49159a41c84a0344e03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 805147221 1250 805145971 805145977
    0xc03040f03060903080c19080910020a080906060117190207020406060c06050619030b06041d030c010b010206070507110a050907030903080901111605010225030e010914060c03 77
    0x16800149000d180d50324100340b4050b212803081500460541008171310043d004404540e001c40c1c914501030252a101705080726030300001800c5a406008452420340384400a0004140311422a5030f04440c608083e400c41d400c1560160845050004406440d4414038281648541c0039064920420140c4042c0810201078407a08038000d520924024011507216040607118032554003d91040080d0b940c1e0909200c1503080c00c100c8202c494148010410020300795410940e4800c01c00b500114590412850400c1403282c6145641400c1d00302103800d000c000001d20844244104c00d00c02010305040943c0c002c0c016101300b400c0641400e100110308400780e1251483c0400412000d09821001d28100500038014405a1811000608140301107400741105024405c1314001c01340703900d8075100c1ca1005480c607101c3c102c1c5040720555004d203c1e5a03e451080c0c0b000b01c0402019401e4962544298030700145045050002107061001903002800070881c0351070b070000001002d4900550b00d208200749d4501d140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 805148471 1250 805147221 805147229
    0x3080106080a091704180501080615030c030f2104030803370c1403010b04350c1002150c0c070806040f1211101a0d0606060f030b0102120c0304 63
    0x9041c91031030b00088081e0802042103409480710202006d01001c10103090b10000e00c00c10269503c441c022411034111080d004001a5005080f6a1040280c0e404641086c400628160540c0c0080244240c001c45000da100000d07481a036141d850181183c1c0c1e00241c0d8000500030000050754005400d1a840341c0d00d00d030640e440c0c00002e010100701c0d2200c2041004d0b00800301c0384c80c0010070000172035500514103010740341030707981d849182810682030160118406604405c2c40f507001000b90040620242c00b007809515040c181d0340a468419908001d000c0d180c7c2c0364440000440d4080b442068030800c001300c40940000d912000e590f035039400a164680741c924640c1000a80d030080009000c104499240c18030021842800e40600003842000c0c1664503036610f00f00000c49411403207050300458021361003110031011000310742032609404c40c0031a40f0903800701c908aa030a40e840000380300d1180c200c0340d0302d100083c06140c1842480d1704880005d40b01d0765621003100e0075a002003000c3c5281c440c1401614058 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 805149721 1250 805148471 805148483
    0x20d12090c050d0b0a180c05090705120103030206041b06020c090712020a0815010504060804151b050306090f0c04170f011e0b040c0c0f020f03030d06091803080106080a09 75
    0x181060f041c182060300d015206005c1243c5002d28024107113131500070305c404058102102140c15881c103414405c403084000d110900300481003001c19000600042880d000e58007907802040a480d09240851113011181d8000042500040f402c018269001a1040301c804040d94161142d8807016003d46004001c0322036807400340d0001c202c440c100c07580308480301c0c8924500c0c800b104000883e00010344052045000382c1c8005000000040c000c140412003003002200f0480000500b070700070002d140090170a074034092002520000a000d01032070150480e41c3c2000c0c0c441c290813101e007801248810b4610407407140990290410b00c88118200c1700384200c81412940c00d00a00240900160088204040a02080e403403858040030840b82c0c1040d02c030345880e070311841e224903a0386110fa0715003080c940d40b9114100e902009400325008607440510250200c0c1d501020301107002c60403c2d0440044d10b02c425680c3c14413801c0c0c203d1500c007083d480000a8119002c0303051229480d103550960f00d000c0d10300c901020f80b007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 805150971 1250 805149721 805149739
    0x804560435060708090c0607111f09150201020d06030506040b15030705010324091d060f04030507031806090f0e0702100b13150510020d12090c05 64
    0x380e81a200010704440d0a00d0050000c20450340500320345140c030140c00166a07038000c00000d0f45a500804929402c07507400002c90b85e088015100244455201240890305102014101c241d07034203100c904c540816240010541c0c110b0a100802070980f07559200300d022404041c3c03030b41d0366294000c1d41192450000c000c4248003c0382c69090a03a9250700959080765078200d1503001404144132030000040d120740c000d014101051810b1b0046020b46214140900d201d00f00c0000310019400c0300881400a01d4200f20100e4401d80900300b25070316603411300714082190002800c100d40403119546240d030040d85800e0a9444207050f040482d4041010300d40d400c00d04d030301c90001207110f40d001507200c001ca600000700a442e0130780b40d1441041502c4141d80800c050b0344005500018086181c00c008105d0b032000c4c00c20140c0e188008080390582d402250150301e00500039800380700e14140100204041399250005280205807100000c0c0801120641080941d541d18180b40070044141281802041c0040c10810 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 805152221 1250 805150971 805150979
    0x60f0409050c03090c0307140118150e120102211803071b0909080703030e0c06040915050102030403020d06090f0213140906270c060708045604 63
    0x2e050351007580c1c0d4424510841d0145042c0380390000c0c0f28003c2e103030b0340a000c44001c010070006440082c8040300000d40d10000c1507011a911407412454081a465596031042c00c0d908001405500012280206c0040e401007040010300b00c402114140180d2031622003500076600c000c41c44400b5454100506140d000c002002d41c00c2c00580450701c0e01841c00c485091880c15541d25403601200d0301304034020840c41d0180588004a4001c3e03200024012001041d1004040c1d0b4400003591030f8841e4111198940c0d603101801c2d2482d10418904010340001e0004618050954002600c02c403a0008020041601c0d080004100700242500700c05040e40904184209400b018409000d0094280615507140d0705000151a00c100096041c0c0203070054070b840401040303002c00e10700b002500c10307540c0c0d600d5104001d04d51100d901c904c002040913a004807591070f10f40f810b162406041503007031110004c0c81c00d07110011012002d00001e218254044c42003420001c40c0541a513a40d1106260f04100704160780818005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 805153471 1250 805152221 805152241
    0xd050d12050c040614030a15180609021e0a0207030b010303050c06060d120c03141209100903050f0a0e09090606030106060302030f151206041506060e0f060f040905 72
    0x51004080003034140301a503140386050b841400b45115940001c1c0301d808290030f50348080d2004641066001d40040758034059520b00280f2213040d58002c004400d05607040c06050320480c4039410140266100039880c0412448980c18043c0005c5440301403141c00007090b45000b8020003181006580c480442c1110750303580e0030003818640040d1003a0100d0b00609000130070500d0185601088144e0007000c82e1404001d40c10129040341640004506000e0403420304402451040302403c060502641100240c0c035144d01c2090405d0b04002c0c1084c0700c1400c114052000036080400d4800703002d200b2100648500152000312240c40f070b42c280d40c5400ca5440814428280320101e00d280c8248020b900a01c050341c0d0301c0c0000c408901c03003103410503c0c009162010510300c20344290500030720700c4001c00f40003d10003003140650418074240c42c1220150600400c170400b112440c001d1200400c1c20381890109074821402140d01c40a403002d4083c4030358400034580e000d80412006841c06050004420404c52030031059072 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 805154721 1250 805153471 805153487
    0xc12051c060b19021915020f0412052109040c090e100806090a02010c0b04080405030f070303140a1d0310060f08151e0405011112070e2407020d050d 65
    0x42c040403d000e82e41c800d2090000409605c1c828018480f190083c100b40c1760803203040e22031a00003000a400f00700f0349880009610140015041e4080c4401e684280351810b03d2030420b941c504e83c580e24030860454078016070044242d645401b8107490106012040e100300722036011141d000070f50502806030500c80c1324400d1588400a40740c51008840d21600c540400035034411910030024002140c15840900203195050b40b0340e0003501c03410402d401c098a07800000e0410f488001c1c2d00035194840c050030000e040c3d1241d001d00b00801802280e501c2c100c60307403d008052242c1c5508050000d50b50b24903c0700301c0d4404104407c0000c0c0005409c122842c0c036a400304800359464480c00720340348075032203101e00354050701c0400d20300071f17001100c1d0380643d0007445c803500009103030040094030b136550b0f00c0c2a4200001c203010000c060201202403185040d1a08450103400300700300035940c030700508a41c03050003074400a82101181c41300c4030541c00d40d262481c0d0310015082a1010400800c02e01915004003822038215000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 805155971 1250 805154721 805154737
    0x20a02010f02030f07020402071103010501030b041704050609040e1606020717060106170403021f0c030c031a0415031401060f060c020a140409021503160c12051c060b 73
    0x1d08885411061040381d03240100e00345054034242c10814000140740a500900c6520700c0f4800d0b905900450380c0c00642140d4090b0702c10384490740c0f0341c0d08110400038200090009200743e0b111040c101810304021690764012000da00c6e001da83d84144540e1032900c01c1240f4181e80c0c0013690810304c0c140d1a48002501c5002c2c41c4948101400400000507803050041070060507100d165030f80039182245000350007414100a4029410350248200411a619a01111011581140c00086a02c0f02e130207500604030703080c944100042500e48580e01d40f8a219803031032142181411a40440d82100390b00a071000050150300c000c2c80380300c0141c1d00d03d2840304190003801c1110607101c441240e4943d1004151003819030034100a6000d22040303428450350550500e88262010b02410004103220036a000c100c0000c841e0030640c04524000c010081c51800c1007814103503400462410031096840342e664003000300784002240d401e001011409015690500005445001c82d454050201d03e9a50803c420780d540407041e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 805157221 1250 805155971 805155977
    0xb030f0c1614071d070c081210030212030a1727151605040b0a110a03092c0f0a0e07030309030c09050103050303070c02120f070905090a0c14130507020a0201 69
    0x4000151107542c041114101110b441131072520790303186074089a0701112910b04680548080c4202c220384007813582a02d10400000807044400703070a40c01040300c0007048070200003003039108000c1d10b0340442c1d0004100b500e030348923006252400d417241c5030602007503402c00809405403078200055000c074080000308401d0040d840b900081c80c036220014031000860b0b0b4481d029000c55070030441007003100c0b00c0328002c1c000b2120030b1500045c010400c00d43c01c0d0600000707544c01e0740000c130100c17004c0c400d0890b0910050010709c01c5d0602065000c9106880c9204844c00a10042500c508500007505405894100001c01070a680503159019101d00d0f02802c0c5d5001800203407494007048101103a041c2d1036202c0e25040e00d400500460843d0340c0c141084400381039110040342c000c0580440c91040342c0701003160000b02114000070b00116810006110708498000b042c50000750701a00e0300d8000304858800c0d103010f540072100030310260a8424042201c040340000e443c20268034100c02c0140700c60740031481641040c0700741d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 805158471 1250 805157221 805157233
    0x100305010512010b0d080a2a1406070918060e01031208090604020f0418060518161208070c15090302100e010801050d021807020d02070f0b030f0c1614 66
    0x4403140c04c880405034802c1c1c2056818a03040007060042000d00b400101d2407900c00c4269500c030318010442044a105841107040202096042201505c070107181e4020240c0248000c1c500050001d290249078401c1941588460f131a90065a02c5a041000a0301111045a0003569a407409998001c070750140200054004004140203680201e08540250380003000b200c0e03801505420000249201002101013105480340100001c400d03020700ca110380100041104a540f00c42d8041d41840001800c0c01042e89549005014030584103070881001074120285d40d071140341d140b07010b07006c103c0c1d5604102c90041c8448121500a5130250070078007540e101365803900000000b0001036032800b1800448034041440c4000511003810b00c50502c84038a40000c09020a92901510a000125059550000680050030a199403540404c0040002d00e0b421020440061030444816000e00000d02040e80c40229040449c0042990801f030340ca2003280504080b5440741c0c5441c160810582c1005590720130300406d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 805159721 1250 805158471 805158499
    0x5120303010b0f030a0902040e100b03161401140d0b1c0c0612020f04080708060c120703020a05040803191b0302060a0902010c0c12032a0f0507051003050105 69
    0x8425681260020890070342000c00c090590031064100400740c640d11a9601103e6000d40d03598010070141010b00c0c40a4511107411070010790541c3e040030b5019000758042d0030f05030740700310400001d0801c95284140d5255021543c03401200c0f043c072011124480800081840c103640c1045901032081c800c0f046681114290700310b00c84907004d0185000151400001c1482003213480d018822080c800c2c00c8120b001490200302c0c3c1d10884503601706802441c916805488140654a0308202d00c58000e401f0745002800c014902c04035005000008180703070101500410503591981c0901c0554000d030925205494031030320b034003042000e41c101c4000700314002000200c000d89000b0780c009090305030302c3d00740c2c2c0900f03515500c180007a800b40c200160103d0400c029019000040f56901207490060f280401051940d55110b040007007a860701410404c3c0e5140d82d1a000c3e500381c0c601e1070104540907034010480451041d00d810000d007001d030294420358004008012250009506500c018107035801100c21000300705003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 805160971 1250 805159721 805159723
    0xb0d06021809220507170c090603060f040303090206090d0302010b03011b0c17090a0b030405010c02012a110105102303120c0118060209030d1805040c11010c05040512 73
    0x986020074465a03103d0305041d40c0c106481000062405071046400461b90b400c1d0720030390b903141124404107030b40082e09000305030b181c200070454021104500074060f608018145c0040228003500c010185640c0380b48510440d200c0b0000d484000030000c0071420044140d0501030b020b00b075044d090920a5180000c4c0c0c0300c86002c200301c50a485034255488400c140e034640d8460151500d03104024408010a1146e40c0701c0342c7c0d41d514a6005003800c064601d482c0d0405142c95801d581004251f0390542e4180f03807203188000d00030701c85d03000001d50418a030241e980c070800f07007910601140c4030b80f050f142d4245010854550119100c0c042124000040d80460660f482c001800340b56103000f8295050b0001410302c180c9840d48005058400245400003d5402c250300000c3c180c106000c004480303247e000724980895103401d00c907121030000e290400310707118805060300702c0c000da41c0c5d400380703602c5141d6501d14070342014400c3c4402d0300f0804c900d0008111320511442c000e0902d42085c85801c2c490000100003d0b62448 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 805162221 1250 805160971 805160989
    0xb07020f03041502010f0f090b130b060d03050d0504050c011202030c030106080603071203020706142a010e01090c0503061f03020d03120903080912090906040504060b0d060218 77
    0xa1814041e50415090180c0e1542c2810030744942c400319900e03000780901c001e20704d110300c4103120301c4003c0c0010034140c6c901d05809038850007020050aa42a49014000f007204690100d07071002c001c0303030026450300301c1e480c086e14103014101541c403405107000100010404000b94525200400362581d0050b110b0309240d00e001c3e4030003140d4002a5040a1004203e690700030a910780d0885801015036a50035112681c240400d05030007010340050b0f2011004010854018924072031242144a0305440e201103452042d1810345a00c01074541229000c0070308441384001c2d48615001141d01000340000701c4281018130a40034103003d4540f0a02401002c13501c03032401e0f0300c4050150030108400c003810500d940c00b0005540340c0901301341c043c0300c8807400d0310035a03441030b00c01c0480c800d110340c13070b9203101e4100760480615008880101c1c3d0349054042004459641d05c6a044943c444403c90300480c9a5032a03140c190042c1c03034440c48058010703034280c440d5000c20515070080c1440700c0305d0510008005601e401045410300c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 805163471 1250 805162221 805162243
    0x11413020604050d02010c08210a02090f0112060b0c030909090309280f06110d08061503130803010303021b1c021003383a0204020a03090b0702 63
    0x8074042008100c0350600001c09011103005050480c00609251151005648104030510000101e0302c902c0d45203141c0700e01f82c2034108450a00450034a00000041481030b4400060035040c0000700310301a120003901e400982c06000f2425100d920b8040304140159260016980184909031100024207094400810784099400c0100903000c4004140c00944040d10022185005041c0e41040031a510392100401e8000b00090343da051454941018107030f0030314021000c0c44d400c008481d803d1040e25900c8102541c1408031070696a9a6922107003900e251030780d107503d8010a104408000041495004101040e030949030000711419000c0c45410400d130f0340c14600032030302c0070440300c80c84001505008620013248145c6060002c2e0215468010b02c855203e40f0189261164920090140d03601e411305441c0302c0e15000351a10103900c680380b44045c090421010003d40442204012000400c441c08074414a00d50041d000310b503030352b802c19401009071035251001c0c3c41d1101c0400110b400e0030300c0015981401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 805164721 1250 805163471 805163479
    0x1e06090e01140f04021002030d06030309030b130c38131706010b0a2304051005042313050c070605061f080a201812030a0804020406031401141302 64
    0x40c3d5617642080510070702c0404441c110300c010300020b211008144544005140a610b03500700f02440d61505c100d400000034100140640e401d0f1350300c030020b41e106600d5403d440d05150310442c1c2c03600b24500901c0f41e654001316034502c00c1200d10044461005c4078020108121850031042000b501c641242c42c01e0b9803040d8005102c2c1d40a00010041912020080c00050b202480c1000d180d00b88186984064174400b011040c140c00d00060410843c50400380039007518030241421400e0500c0e200c44001c0031a4000d812145241711040941c145680f078040180600702d104008000070704101174854602e4001c00c40840d486494038010880c1e600d050140c116210310104c0014080883c8090100c0b03100c54060304003c0704a48452085030000a4009403002d201800c104c0951525585d4403503101d0741c40d644034098041e941c5103100e0820481e0200444406544508003200f05032150b1000c030b40204455840681194001a030203511010103400c40e101c680c0203500c001d2413581300c204600c154400601030003580 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 805165971 1250 805164721 805164751
    0x30c020105070204060506030a24061e0c081204110603060906120709090f020a06030506030601330e010e0102010b0d060b1302030408030405012d1e06090e0114 70
    0x150700c950001d003000351000e0404100d4035a00c0e1301090144e007080c1c5d4030440841d12420103400c00500003400803040409201c004030510714110020744030000140c0500b0300c20b0f400101c2040310034080c1c000d2110041c1c0c0f102d00d0365907510980e182100c003a20181c0d41108d00001480d4565003a140000c01c2e02e009420050960300291201e0040051981d200c00c280705030703809207400c0003440b03585501c600700c0700500030160021004201c0c81000020f0041350040300a051505c014000e5644001601710705560101d840405500c1c05038100c04c1c0c1d00341501c00407150000000800d22002c2d50300400300b12051000380c0300c1405000c1504016030985100d482441e800c0907580e0781600c04070700690012007030071030054688811200d490703004105903813044409030784c0c081000080c40100324091013a280d08503801d9203003004111880e08180c0104800d03031006190f03030362510388050303040944004032040309803188400c0061942c1d50140d8070181c0405110492b6035480c2c42c00701e4164414840718070744500b2042c454104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 805167221 1250 805165971 805165973
    0x170f060108070306080d0203130902070b0103020904030210051518150f0409171308060f04080d0e100e0c0901180203100f03050703061a2b0f061a010507030c 69
    0x4100c81e0062014040544a420005202a05010850150182c0c1c1d0145076581c210f80e000300d445246690020407c14410080000032540c05414141542d60490707e40410341c4503828104d29082100c0115040b05181c201480800600185d181d09001c0303080c2c1704140000016108000d850f58100c907050440301c490034048000d46802c0c00c03a2081514002d10000b0030281c1d50b256112480b0840a0b848005131002900801d0f80311104426002050b200d4010300720381c03510000c0d090b000103000e40010903412001c41d4403030510410742c10006240d158001129503684a80040390094528000c1c04181801284044103d40c100b440d0602d040e40d611013074000c415a100c103400320080d8401400050520300405000c130ba045503a5540c0350056002d600144101d40c21130504408071020001218410107a481c1100d4503600c8000c0d8240710360703814544400b0074030000c00440d014a12100c60090540140ea5039010410503142d00103900c1e46665151a121503a441d0010342c1d040c410304101501180390181090 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 805168471 1250 805167221 805167227
    0xa090201020c0f06040f080d0306080d0c0f060905030d0c08100b09060c0718021903020a0c061e11030f070207080703060e030d0f090203011a060406080604090f030807170f0601 77
    0xa44058068421352419583e1100404058416046540540c21020640c07201982c5400f8030b00c0074200342c1c0c01a1491200481e4044c00100a03a2001400c0050034010340061101652100907040c0c0c00409072a600d8144494441c01081881820000b08280f0000320b10216501070081741a038041e10300d000d00c0c2000c200300f004600c2d04030f407c00d00b165115403034000c1040d0025002c2074142400312040542c882901e41b960b03652038070280d900007040610601a1142295000000c54500c5401c2600000c43e001d0015120410880101044550a092103441d01c0c140522400031882198854021007058a81520032078a5401920640c011355111400500c0440c4007a4046401038804001b100e11b4003040000e00300070394003111350381c008413603407800e4a00135400d007801076030301d01c2c0340821000c42c2d4904040c00059650141d80901d00c2000001000191991111b5015212054000e07910281400f65440c000704469002c80700c2c0c90000b1403460b00f21010031200c40d21507014000740b020045850ba5600c1c011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 805169721 1250 805168471 805168489
    0x309090522022103031009110f130b0a09030c09050903221509260d0e0105070215040501480b100906080f0318150a0302120a090201020c 60
    0x1641d100059003003070703041c40800c1c28000d186000500c000e1501d80c0b51401c80200c40000c0d55000030201c0341040e0148c00c2401c0a07004032034444401c102e000c0d8940c0103403400302d102c80f0072507006a441244002580b445064001c41d50104a030301c1391110240841e120800c00050780c0f0250390021640d44280807615500300341000a1829000091201e03020070b070380741c89980921030b030b140684011403081a4180803003a880d924a002e61034040d003009001c4005520459960302d4100e00c0001004412401203140d68422000c4860f00c17a001002c020701c0c400b408100c0c903101c0c0c2c0710303114080c0450b43d01511728920703190500114410841c0d20441c01400e00f032480c916031400c0780c1d00740d0341c0f10780d16154481080000d0000c051240a026a101a4400d0a0410341d4420480d10303183c2220380540d1001d04440c1c214900041210b18500300e0b4070b0901c1b0050071a202042e560040d0000212003010045026404c95525502402c01800304c8144030035140c64080a1200b11500c501000e40140c110703100b15825402e246800b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 805170971 1250 805169721 805169723
    0x1b1803020f190603140106110607050c150a060509060907140d180b0619080a08091f03050403031409031602130903020a1b0b0a030f270309090522 64
    0x411503403114220400403002d00c041d0402004a6680d03100244411031014246001d0801030030a0000f500c41c00041581d5444020703d00001c100c030001d16800024004e008165601504030700201050034040d59107809400c16000e80ba00903000f0800141d81403400480c024060000b607114410215a4240c03200d2007640b049020380402502c40f0b801e42c0c28404881508041e83e4001c4403505620b040c42c1c2d01b000020080c012155140f6081c07a03509204801d03000c1011030a840d442611180e5034031035500130641585035103110380000724902001c0d210325905504041e11441c4650703820480b451a40c10414280c050a94807001d1580c001e0108040e000134000c4c0014007680001d01c00d00c615951800100e0a550340000200d0058000544902c10080800703082c001010721451210342c0d66082084c5d07102207000e544204010986c650409180c6c0c001e2680c000c07a610b0001c51207500d91401f180003004078004451a088001802c011800a400000e44c414180254001c906045003003840306249402040c0240f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 805172221 1250 805170971 805170979
    0x2090a080a05061b0f160b1503010c0905061209071212020f070f090b040902041a030f0303070503062404063204061d031c14070308012c0702011b1803020f 68
    0x41e0f46c2e0100350640345445c0324003068041101070201c0941030502b51038010044c5818080542e1040c0a55524941170315101d0713011483c04c51641e660b20006a03c0d0a02d158848034900110900140512000c1c081900c5601b00315000c0340e4180010707a840590390421403048401c0d220042d61b05000308451600049000c840040c00843c40440a4000608a4a5201c141c4850740400c0d0712000d21824203002d8a00350002540c013940c25841d00d214094981e20005200350b2040209180c80e801100035840840700000f441e480c92a12161140e04c05401c01502075540c401000d00540c4500c5040800740d0414801d01208d01e1a606151030032805440b802d012400c0030581d444401d50052058404201d1105d0fa111541d400c0224240841c0024090407442030441960344020860400400d4102a240e03046500c18580c3d05656041003102a28070a00d2008024820a0a00502240681c150044040001c0b114840ca14890191100340c0310283c00781c00090508002000030405840c0070100300d00c007408042c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 805173471 1250 805172221 805172257
    0x109120209070c061b0203190503010302090a0203071b231606030c0201090510020d051803030f1806040c0302010e030f0c2b1a0a051e0a02090a080a05061b0f 69
    0x820030005c8588000560043e0b2001c03a0400203503900340441001c0140030300341a0f00d03550464000c503240b00350080c40e04924540000100da03281d846294840d01c0c1d042c0c00913482800d08002d203001d6440f808003103a00c0c030540c55a19500052080c021901404c800c0148040e441805c0ca0840185c0283c8030200380c2d901555a5001c0e42c801282c400d00c41d40340e616102c0900107a4850b444c1882c08100d40f0090305030300e200c409604036401300c0c0000200b101c0c0c0040710891042c1c10766541440400300000307549440c1c84980517038000d000800c2070440b14072050300d20036202d03601c00e280705900b030641d202d80c02000000c142c0d100d00c800c00c2c1342e0f04045d41d800050940000700102c02110081d01a440b14034400c0d412908205111600e444010740b2040194010300900001d03c207904110199560000400e05000303d084184000f240a10780e29070304540c0900030141c08101050381d180002511a110b114098481d03005400c0090b0303c00e40c4a5003510306040c507401c0b04a051002020340b00406400010700c02d409a0761032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 805174721 1250 805173471 805173491
    0x71a0601081f21050d02012003060301020f04080303090c03010c020309041107050f070e06040903050f16050708070e0c03010f0b0d0e03300613150909050102090109120209070c06 78
    0x203e40074000b200c00c41c0c405001e0f0841c075490218500314070301003002c046914080100e04280d030040a603529034041038210740d4a03031f201c04002038028880c2d1803400351103010014000401c070700040003139441707542d102003994002c01d489410715081e10902040741d00145c100b0070803400d55103842d6101c51050249124050b061142c10b030f49052800401c0a03401d00c055025980c10856004007242c050340c040d070191410300c0095015a000b800e14064102c043d16a84030104105c2241603100d401c03208000e0b0800100d41e106540c40750b00c20384421b403501030921890340a03000590080b010a04030b074100d626610b401d0354110320707150410307086070071425000064a844000ba089240c0d81040030305003400f0620b844c59103103201c090f820004031841c5000c1c100d89980000801103507540c0c1013051060180c402c1b5011811202d095047d08406880b5000380c13980502e054101d5040c00815409005040320030b81f02c0c1c00031141c43d803240110840c01a08002d40c821910300028650504c110380c0c1024040c89204041500d00308 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 805175971 1250 805174721 805174739
    0xb0102150a09030519021c05070b0103240c0f120e1e1204032108091e0c04050108070504060e15060a09080a0308090115080601150c0209010b071a0601081f 68
    0x8007403030240069001128003070110080b09204500701f03049040c81440c2080c42c0c0c2c1c17410461001407102910920740d01403540c40342015140d2540740c0b0312452104024440d56401e0150149030400d01c20000911205c9404d108102c40c0d10401d15601444402007444120000340c030000c3c100400d0a0749002e0040717030f09048030000300c0300c0070700080c6115108a216044121070900e04a00c00d100702502001600781c18400f403028003045091807440440d00c244510001d00c040b2514104120751401d0b005031406000292140d80400c803501942d1303044a0910045648410701000d214090300c8800d1000700f2058521507902d8170a009144044c000e08003c0c0015540d22240350034150500016004254a0802c01c401c5100a10420214188e000100d49400341011107455440c101400b400d00e014440080c8900c004c1d0040305080030090740140703005019a151a2044010b070041e400450710050920b070031204030514520440e101e40c00c180d5840f41c055403240c5003807134030352001c00074800145141240824100c00e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 805177221 1250 805175971 805176007
    0x80c01050a0b18070c0c050d2109060f0513050a030b07030b040e190507081e07150c03030f090503340c180209030613060b0102150a090305 61
    0x4104400000d0501d8808500e2040d116140d241612030b01c0000d0055210b948401e449903003200d02490030328002c40325450504007030070890300b10b1544841d201c803c01003004031500e210503004402c84404120031070740000680303c5103038a02034000400d68020b0b07511070a503c198003805020b14900709107140c0e41c1d920004108244d0050300203691300c11a0383d00700701c06a501030041303a000c117030160740c00c100401210351400e071250403980c071040c03e10180c00f00c045c1c2800000c0007400d000d02020341c140c0300b003075040c40c4040403500c0c1304840200150140b40c3c03000071200c03150a00384040e4401902d0b40304060700581d030102d008000d40b83d032960455030b803004401d01050040000d04856021a66081081c840f40301c0321301501c80c50030520f0311003581b5122102000400d5014440c0c00c07210301c00c004442000718515040045d00880600329018411041000b82d030600310003040ba0f080d402401d0406c01d0320400c6004a8842440f41c004c1d02c03044203c6000304030044020b42c0300c10070050082c40e01ca07040103000641d140e0103070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 805178471 1250 805177221 805177237
    0xb040b16150e0606090603280819020d14090f03030c01110a110f0a060b031c09050a1d01050f03070506031e01060503040b040209040309120b0709090603080d020d02040308 75
    0x95660030000500b804200708803500120221102e0080e442e11000007656800c0d80d120f01464402240ea0a10080300c1c007a060903895a0300c5041030b6100c80b18055500c5d0320301505000da1006106680c14504000c1c080e5084030060010400c0c0140382602400074058040840910180c040c4000c00030050a01070a00c210300d9100103248078207561b03035001c503070013440000c414542c1c003a03075005030091440d00a000511030381119408680403c10805103000641414a4195200c044034030010130040b8060b8451008400c1e580c0c103e429044580d01d41d40040c2c4101001f032500311209031131000600c0107240c94a03880c03501c40e5009045034486500c580c04920181c00c117440600c885105440624a0581c85000050241c945440e016003589450740300c10701480c0c400f8001034000c40c0000081001c0c1031040081c10b02420300c940000070600f40524140007500b0080f5015000100c03086c078007080f8020310f40141ca0032650031442c45400d0010180c1c011000f948502035401929908101c00070004003400302030903203a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 805179721 1250 805178471 805178513
    0x8071407050f0c120601140a030203070609080105070519080a0f060e0a1419050a020417030702100e0f01200105010807030506060901060507060903200307060b0603010b040b16 77
    0x81068682d2038140c15000840c130440745006000706004000441d50704660038903a08062046084001c610712250f50740010b505400741140c0443ca0b29046450302040f80c080c080200280d0b910440d088459009501111613140074038607c0f0345046100b4000e071a0400f500c1d080008030402b41a00387d408590349940700178455024001009981809882503a040700d0140e00c000c55146071082c40710510124851310490001d6a03903001c9002820254181e41c050011442e41c0030340164110b8209030780c2e07040302c14102d03c40c0101170540c25003217104286080301c0e80c030003610046100c0528401591545100c1a0703041013440f002c181c00e04449000d010b914020712154000c0d02c4001d065080290902034001e01d4180511401c0300104071056119045401d82070304881d00041130051845d08507900003403a501d1700b1451140345a02036401da000301c0108442c600c6007104010308015501031200c54082403050090301c007403d00c8108001b03a107202c000e219071815480140504500c2d0f590390284c030400c5140030418 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 805180971 1250 805179721 805179733
    0x6080f070b21073e120f031b040308042102030d03020d0f241406070609080c0709020318010b0d03050a021e060f01061817012706060e0c0a0807140705 66
    0x1000514500f5011184401020306010070b101640503405200d4051100c246d06c00000014555181181c1056402401c2048460395103540f030400824582260040e003002d24074a041c0c0350440d07010000c181100d20341c0900030300b00740b00c8000025002500300062083c0c49645841c1401c02c030840c1c034400d40c4400c1d8038040310b03080300b0b01002c4008c5580c0e800c19009210003104004401e0030f02da4540058400082e401800400c0a501c43d00c0c01401c00d01a0502e46890b510611402042521494010318880c00d000848000304101191006080c0d4007110382d020b4100c60380c0400000403900c108010b0035a2169401250700b0035001c1c2c486203c500c5100f00c00551240c1003030060200c0009151040343c0107042a151a82c0d0490902c2010011070b070b0799200390304081f60850302c000f00342e43e0207400101d010450f06541900400d01c0f0001450043c5041004a41a0b80b0342134001c94102c9061380018000e94400c15840c0c2403508400c025100b0103400b9010380207002e03401100381c5401498a005045140c841d03006858 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 805182221 1250 805180971 805181057
    0x200f180a0b0a17011803021902011e080103060c05180f220b0109050a0605030601030f06080d0201060315090b0112050109062f030106021513050106080f070b2107 71
    0x42140c880c90581c404501765041c00070701003680007070911504840b50006d1800d901d05840140c0c1d0f00994406214406c5e040302507a4000d080d00801d41a048034050f0740b0038002c0c200ca100d0300300d51034801c0805800442404400c03000850a01c1c0e01c800050f0800948180c03122008408102010a1042c203a07001c401e4403038400d2100755a10000400007010141e8005020758141407025003e0300004001e103042580d11495181d2400094000c80010034420b81a20601ca000550003800ba00b200d01068070f00c0742990a03d42104141d9202d03140e82d203030700403090a40316402d02078218002c102111054130650b4903030b200d80010540d00d10031100c904c0d540d07980d1401c074030903100404000025600000c1c1c0c0f4011060004009164010a0314101e0b40030101c2401d08580d2140701010702d21048601c064015860a8404204060001080030025441d07d085400b4140c0d0380d038000107a0701c5001115244128941c098035412582c01e1b4a603600040300382020758490581d640d840c200710b099212201d030b40100d9446001c1d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 805183471 1250 805182221 805182223
    0xe010f052802030c03010501110a02040e0a06060b0a090b1b06100305100905030a0509010c170a110f030f211f05030f0d0c0519200f180a0b0a17 63
    0x110103101d04002582035241c2410704030510f00052041e5414480d203202c0d44c40140c0d409105117061075600500030803a080070502a59601c15a001007103603000c0c508a00400c03003600c640181c40f1079140b561365501c045418482c80c25011b800050461000c0c46c1890844a0002010b001c3d49125070101800c0040d65423460921915001c0e917450219401440c1144540205801004450fa00080c03402c244d6550f401803001250a402d20403800703081d609540c1c00c0e03000d5a6100743d00901e00395103990b27a8800313212000d031806074452041424061065000300844c00a080300c40c000303052412800303405c2c59041004400c0c0201d0f0308070100e401120421211004d1007002c6a106030540141c9010b400402c41580203440460b641c0c88001140300a11003254002001c003d0100070003203c011005564107400c0b503052400c1e404030602000520031201001100e41680d007081e0b0706103070740000c2c000c0010b2081620310700100200c03400503109000782610741110750f04580720443c2e00001019400040d084801f8600b50321 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 805184721 1250 805183471 805183531
    0xf032102090a0e041718030601090903081605030a110405090a1e060303051b0304030f0b010320011706010e12061b030402090115030b0907020a0308091204090e010f05 73
    0xc5180d143c0388400c1c00b02007120301c4600c1c441c4260982519580d280005648501c80c030b45240e51941c1485042c00200310502039400a250140c0709403070f03030742c0951030750119440c109000941d2a40010020b0000940c184140d4001c0d9010154007001c503403400d512503011558189045030f0100b25182c0b10484240c0e0070403244104680d52511000800a1a045a41c0149030f0300c42c5049101102540112482102e035062003100c00941e0321030526502c0d9811450500740640003403000351109019460011100000140054103000050751400343d01d040000c4582890075015100728100010310711131850306c2c4c503141200404107010b2001000030b4074100f000901998601421404045018014080180c99411810303055458a00290409001d9a134007100105404100c044d03003d02002c081c4110300e40c02080d102d1405001c0e50303410807141e5404440b5a030340c03118480d802c0100720b0200001c00c5103104561101009803035080000c0340503003040c0c0f103044c2910001e444e1151161404007616241101d40105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 805185971 1250 805184721 805184729
    0x1507031107060c021306270e060c0904020309150a2c032508040b0c010506121e0f030c0304150201230606070501090606050f011b0f032102090a 63
    0x2001c506080200041035081c00000003070091400a64414982d02c2c141c114002900c620b00030b8445201c584541030102100c00c400c6044050325120a1442e48200408d100e845100c5505070949000302c032000380b0000790b000031b2400c0c04900503480388a80e000095405207000d441e074900007150005001902c0760003812516661900d0200c41c41d40448805408015035034141c8000b0501d102d000c49a80c00200610044c4d10028545500020b000c51034018540181002c0c140e504000c010650b01e40091200c2c6d40b454246c03044443e44049040307083d0841003040c03440c9204104050365904110710340c4161441d000007960300d03600c1e08041828001d0402080e075956481701c1c18802808a040c10b03c805c100302582104000c50202c0701000000c240d47c685000b11280140e01c035008114202c030508040c002085180515403080c1d09070814110b00b0f43c452441a2121591280c0809210040342c0d20f00048014184e000c805006805050701d1440b46503265030803080192000260b928611a401c01402d0065130700 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 805187221 1250 805185971 805185973
    0x9020901181823030c0a1a0601051206040203130b180606010f0f0e0105040513090507060309210c050a030309021c03050a0f091205330c07030e15070311 67
    0x8510042d224040030f41810441c241c0c803080410940d4158450329080c84d040c2d06c20401d0900404c04032090b4000c82c6c0340070785c0301e800040d1155001114584a000c001020103030b4800049200ba20b05030303000b141c1108812134007a07291100f0359981d18075400704441c80111004185a40142400140a866807016091a04480b003032000b503400780c4400340110f440e10800540700e20742d18507079004100711070107000010121041000c40c601c2c92006014011012901401105400920b4030f009000301a42c0960018211100104152901442c605a040303041c00308052008240003140c41440a404218040d03900825009014010b12082e00c0702c2d2005007800f02d20401450010950103400d0300d0f4442101d1400c0b860088100d401203800e03002c1500182c4000174540300c44001c01c6400a46041800341c01e01c0000f2030150707103450505010314945032844c24090745800040f640001c82c0010300415209052968075032140740042082000100d01d01500f001001030030006150f003180c540080d40000344 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 805188471 1250 805187221 805187261
    0xe060906060a0e011b0b07021501050102070e1b120a1a01121e0e100b03070506120712060f051c022b0519030f020304030506060d060902090118 63
    0x2000c50941e10410540c10104000d00b404000907a00c1034000c00f01c84071000c1441d4105817a40e040c42c43c003181040e01d0a6000d80703c2c40400d2220320000a0000d4100c5070705802501c0321526142d408030102d14003c2040c03040c0c1408071102c0000d800642c02411543c00d26000c41c549900d002d03a1048111504c2c11032142136910810b14951250ba80000c80c061100101071012a00300c408201070100401110041042241050400720306460002003035003407040e054034240a50325800c0c0602d511020030340500d07a0018420495400d486900c03c1c0a59041245803900d01c18980e000805403044940b5a0403405d4070a0780d0341010051450600340c0d00034668544508800e56480580c0026106012020195100c442200c060b003116031614006a001c10341010607512840300c1d010783c0037850003502904901181000340700c040440c0c80002640c0550b0781c4080103000580b210f1007040620301101030101c8000780c07540c00240c016203440d52458004d08204940c5940e03d455803042c00c095942404032414504821 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 805189721 1250 805188471 805188481
    0x605041202060a210e0c150301030b1003050d0203070b390904060e01051207031e0c090f3c0c090f060806011205060f130e010f02040e0609 61
    0x30022a1403980c102c40082c0d03a42d507003050a0b911640091081429404104d030141074141142e00310b043c4545100c0b00351400840d40784c040102c0c4000c130450f01c1617008005d000500000f01c5a042d032640000c4c20440821035036076a0b0b91140d2400266900c9400180c10200d6082c0070098070384038864001d10710414801809200042c401c080c0c1b0350031403943c420041600703141880c400b10a002c99142d50300c054010f2104984403120300c0d0110307400f8407400e4006c3c03c15088030108800b001c105030055a5120303082d44070710026481c0c411a1301d0b01046040e01e00820b82240000d44440c60301c2944c0d00003000745408502c01070510b480c0b010b0140d5070b4a0441d4209448000c5040d10700c1a0850702080d039000c8400052840c88601c4100d0300601140c110620f410705803080841d0310794101645c0351041009036105c0e8000f44075003480c0425540c00b0b854054101440400300240c61074580c0321405d502c001c2e0f1200007005001e42d0302c050300b5a03200702d000b242d580703500041c00c1c40101304030002c01c0e40c05602620049058100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 805190971 1250 805189721 805189739
    0x30906050c03190504051809070504180303050403210b0f040608030f1305040204030c080f0304051e0d150903110c030604020120030a1205060901032f040c03060807060504 75
    0x1843d4852840d2041424410030024080c0056501500d009422441e041c0c0084009509102064a5800d00f610500c1e000140618041c0a801c080c1c2880310800c200322000769500b0b9000e060080c0c0103c05004003102800c00035404c0c004070000074105a180400c0c0c950011040c80740c0c0801c1700880074050390a220702800310b4400001120104aa441c00955031803004404c4820010b545030031071a8010f000080000030321034844c24180948001c04192159108018070f080d9403403041d4860603400915035800001c451102c000351440b500f1014041c40703400070343c6540b050700d1040c03940b4240c0f030081c0d940d8020100b496070112802440d0008400100b03203c90021002940e9040300400090402c04541e1360880000403400503d401c050820b421a0b03200ca8218502811000007662a0100325142500040c21880c022503054102d0b40c0200c01c1000007189a041e43c6042e0300300c1c0200d175884180c080b091842d59180c5114800300304845a0300010100e090a82c3c9d14180a4264408020000c00780801c1c040e03019 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 805192221 1250 805190971 805190977
    0x29160809122b090f05070603060e0a05042301152c060102150a0203220b0c1b0a08210c04051e030d0806100f080414010b09090109030906050c03 63
    0x20080030100b40304905030741003a281055000d0094001d0400008204101c00c0d0341e0500e020300c0c4504242ea5203d0b0715454100c2c11a17100b4443c0001000c01c07400403d41422095009030307000782c0134222040c84020100c1e4205211105159001c0080e0b54a9445407683c0740c42c903034910080c156007200c040140c2069452150034480c00b401c00c880200c09100400d00d20ba008202031031014900031441381540c03070800340850003508212988055526502406041c0109008031a2100380c0d21800071449502c54100d50315940c0c0048a07201944280d110380406a2441000125140c91040103615580d06019074002c0c03150300300d042190b001401c0300081c840110745e0701041e5010380b0b406449001c00038608c1040c03012400c4070741d40ca6642501801e03402043c2c441d4800c0080e1710484090300d002c00d50040664088804a620754207000000e003030180410009241c00c820900201c42905c00481d0074091940010301d00441070b5801021a03645682110405030400c18410081c852170034800d00f1700352804c440d5a01c0384 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 805193471 1250 805192221 805192237
    0x5090102071403070e0103030906080606250204020f2a010c08040b100902040605030403020c03030408030d0515090c0c010e061017010f0c0f090b090109032916080912 73
    0x41c003a0b076840b85180c5080110000034125450152100d5a40e420050411596030041ca00050200400100035080100071a00800413100401220f6482c070b00608144140c4224201c1e40706408100700845007540d00080c045c55020038207401070f80c01e48103500000d0400d448031042c00e40d90600c0d035900d440c40d8000c07004076401a081480010184e030346540c0221440c0245d08100e602520104001c01c034070f513215010718890b61098003200d14498110381003680e20b024034801e283d00e0b0f80c400c200041c040c4030650085078022403071910700d41d403031660880061140306044030a207080c0702001c42c1c2d410a0788401d000381c11a600790700c0042c00c007030b0030003144408000c59a4007407e502070141c032801ca0b84400d0258043d01d151182040c0401440051001c000c001511a5101900181901d000402c90300c01820489081e150140c480300d040c90300d9540ca05440540c205c000b101444c101300e0500391905a81c04445200d208910501d85241d4101403003d8000c00010f04140c0480e8841000c90074000d280da02117403140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 805194721 1250 805193471 805193489
    0x50109170307120c02130c1116050f06070b09012403020a031101021e0c040c08090a061139060f072a05100b060c120a0314041a01060509010207 63
    0xb2014100064031418010b40c0001e40206c5008600c5412404640c0145c0b100401580d038114124001b0104c5a80d5500c1e54044000c40d078060319040080d45410301c040c005084014003100d060542c01e4603501440c0d8000c44540f0516510f403800800b920030058407082e082d0031001c81c011400350035500415482c45c200c1c04010100d048040c9071107030303aa000b004443c0d4002c00c800741c4d595040d007000101e0f80d1214440a06107014500303220b400b82d02d083c003078060113119046a0004200703082023516800003410740c400d20401004d100b0000409004c43c0080d0608061000d1810540e481c019103008c280c0718000800c812440f0b400c040700f1f00480c1e815107004290010403901d0190404051200036640c5040a0469170801111041b2558100200840c43c060078203804042082440e0b40c203010700c5031500c54882d6002e016003003150310785801c030700f00d2014105c411103074a4001100980e1002c540650801500c050310b1248850b1a150701c0001100c0c1c1c03650241c041ca1038907500b1b00d10b1850010795221018007440e404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 805195971 1250 805194721 805194743
    0xd050f04090c033602060307050c0706020319030903020c01110304080318090106023f0f09040501141305181204030501060f051809011b09050109170307 67
    0x1208098805440c094128a001000000c0304800050700a02110707158403940c4104800c4e040c810305101d0702030740486511038140c000012242e400c100703071036100800310313401d11400380000301c00e4000403c41d1401030200c6030011640e07220744c5500d82840b4142090000c0c20541000000740000350301080b004034240b02802d2155000c405001080d0441c0100d070000801c9100c00b05881c41050000300c0c5180110005541003442c503621124101d84030340b6081a8042501d4008040005207800035150151150038000700b410750b0a01604500300c00c1d884034075005010800422229850b1509216032801010a4158862a4004000407035001e0300071010340c0200c142c4c1e510000e29042c440720f881d441d20050440655030602001303400210b507030b00140801c1e60b5940c81c1001c042507040c904442070041c1c4000030600351b84455407001c28503449a0050501303086548456140d0300110071940f40400b400350f1511038020880c1004001000c0c100e641c0d1082007520f0150120080c1440044206d840c820380014082c91 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 805197221 1250 805195971 805195987
    0x3070e09040f02150901080108010b010e0603040c15080402090711061605070b04080c0f060708180f0d120f05040c1406041a03070f0c02030c010806130504060f1d0d05 73
    0x440d5682c4480c029421059440b13020644c81d0030800104030900090b00c60b22810303600da541d62803c071880400d600c2d001c201104102150b40c50f00b200a10b501900ca034007000840d81c1c0321000d0120304a9148499008101410300b4002181745c14180d140e4006402e2500358a1000d010008581d00d240140c01602c08401241c2d071070b800d041c46581241c10207904030f01c40c001d10781044c0c40d017455640d10120001d81d4500030101030b64800c44000c607010340140c500b981c800405032540070304e08564408501103110503216001c082c01426109101c900c40494103510b6440100285248042c156846038420b5651a0719160401000070300207251501a240d2034010302c8030100b00000442c0452099401940803003043e20003040646c43c01d000150310580300780d83c4219542800d040d003036401291900c0d0003075068100c11841441c9500c25620345603c000c0080941e151100072a14010031240c0680d01520348035203c1d0000e04518040e802507a2104044211201f200806480d03a9500c42213902941d50400100060402c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 805198471 1250 805197221 805197233
    0xb0106180305060108030903010e0f031c06080a1a070212270a090204030302160303081504110a0504032d0809040902040c0216060809030d020f1213140303070e0904 72
    0x10003940d400b2040b51110b5031144203181d41c1e900b111144034071179800d10554841c50400401c04501c40b6940f40015418440a140f810760983c4010295001d420703952080010070701c4081101c2c99809000d400342d031180d080c9100000c00080402003034407040d90b112400070005800c0800440f1515074101042d1800c003c0b6550390034024288864640f54061071000380807070303d014030364000c1c07084912035000ca0b6142c01c800c10300040580240e100240201d00001e002172a031010f00f07034521004e02c0f80180300142065090050400751f82188039404000ac4002c40e003401048000b4030034024000140000d03072800e400039401e00c07001c030380b02510040001c440819110400d441d40d03080b4680003903005005000010301603800940d1810b55405010300d03c00c0c80c00f00019040d004005050049034510059490201c5540002029500c0812110300000d000c100e425102d03100b80f07a800d4003890784032010300001c2400e81440c090144060481420f80e8200b0001e0000c0350350000c1106100b2030b02030342d11846c1780c1d403141068 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 805199721 1250 805198471 805198517
    0x15090b0303040e070801080d0215074505040911121f05041e02060d0c0c020d0c05010809060c1602010c051b0307060311030a05190c0203031b03040b0106 67
    0x86a1041c070b0240944c003600401c00c80e043c0ca002004880400d803081e081286e9480904040b0041e0082000c0422001441464040c03032550704099081d04202e104004501c598240c03941c84072800a1423400c044c090341e0995000f034003c0c142220140300c04280e98407000c17116030100503042e118100085102c0d0509a046c00298641c1754100d25003040c00e000225400b000c0c00c02203c045a100c0c03c02c9050541c140307a0095000d4019801504641c100710020040781c1c01040c2d15558602404110301150700103036601c418003004070307100e6021000a1071508001502501c0054202080e0741c005070100542021400141d843da84043c11110408c0d814500041c0c8111204800183c800c2c0105011340c03511007411649070b410004240d007210203441e641e41e800c80403039104041c8203d03e0340d800c0003c1094400705c0c0c1c0000f82c110100000104000e1308140034481164201c0d810140582c02c00300401c0240aa000050b10002601c02041440c502d02555044c000c00d00c14000c0c0c02c144100d500c003040e481c10501c818 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 805200971 1250 805199721 805199729
    0x30418021b0601031a090f070b1c1d060c07150218040c02060930031807030c05151207110c0a0f080c0307080d030b0d1a06010e030115090b030304 64
    0xa80b02e455849080c00b2001d00104030081c1d559a003848081400e50034001003030649442c00d103004e0890141044030000b00c07580300c0300784c842c03a01064505a00070080310b072091800708601d264610001e50040d0441e641440c00080070504140c034140513140100e1034080001000340024840140e40d011000c009100b104034807103001350810f00d04000c02314000e0300056200d0041d0819801c86140302455946080080c5000c15440e070a68a8503407800c003d601502c000c1c50700070140204440038024040d0440745000ca17503500075115000b2680d002c020328240703006001600401089014a8502c2035010341151440240000d02001202411328410403003d021410200c3d00c001c1c80c010314103980d02008001c2e2061030142d1036160240da902c0c0060340c5070005070401100d800f40050003048102060540c0101b00b080d0030341c1d41000c4516090000240080002c00d80b4409514602c4805c2c2001c4000414450b800e00402d03000707130315018003080e403140c28828607001c03505080008503102454a0119007140642d0744 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 805202221 1250 805200971 805200973
    0x504090b0a0e2d07050f130b0f12010e0112031b0c080d030b09090601150c02090a020c010c090513270b011802090d110102032a010c02030418021b 64
    0x2d21880c9400f40b482e14a580010503940302c000030711044000d0000030305035110804143c00300008801480600090038500b9000040035070404d95420a00720350b40d20203006540312080000340030310942c41c2da0340f20030b002d40b041d40ea2405140d8104540003110080d102c102030140031080d40c244c50a007a07400d4180f400c056000030502a02d41e40c0e901442d40e00c0c0c014200d01d50101b801c00501c400300341400f802d42c5101c2c00071391380101490392810070707040940880340b6507980030040c0110700d54026031144518a801294210001a6180040000d00782168907070720300340e41040000d800400c590382d200f200045c0000703550540028036024101004a100344041c9440c207024058880d0070301031010310711b02c25040314803014044c076200315804180c2c001c1f846061040f6a101a22840303500100340c0ea40c0e0600903064045c01203034500b41d0185641c01000e40d10904d6040000c0612151940c4001c00380650703405403110b400210f041c00c0c10034070104c2800e40d500380d415103056400718070741c0c0011500094540c60320f41808 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 805203471 1250 805202221 805202249
    0x51b010c020309032116022805011103070f03030f021e04210c0e0a020705010f0e0c0d0818011b08131706061306170a150c0504090b0a 59
    0x20340203900ca8018450041c0700b40201e045440140c0203148041c0b0b4008120410f003440d210903141c6070b10303c141b403805090ba0008520110b0041c42c41c034081c020b0080700e000c1c07801550700c50729090005001c92042013071502a0340051210500140c00d0000e45161280d050401007510314002c59564024018206810380348000321016012551100c001030007681e0441d00703041140758040b164080e0200c6040c00040583c912900101f0a224141c0200343e003001000c2805490801c0380d0700c942c2d0179210460f411007036641c5d64012024007a1010820740740a000203943c40400d0110369100c2d0301040c01410b00700c20020340024503440c0e1680c443c2040380204a8280b80c240c1d145403081c103240c101038120b2441c0081ca0032030344001140c1205652403004030602e0890082609a441c0006d02410170075a24001880a4075084e020a00c90318540055150a10003402008140c0300ea04248003501c0100804505c15890494290030940d8040202c0c4d0070345885406c0410201007540201e140a00b41d0b0784024001c80c411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 805204721 1250 805203471 805203491
    0x7030b1c08040f090c0f0513050d05060604140c07020d08040f1502070f0312050d0b031b0103050618010501050a17010902031f050901230a06020a02091303080403051b01 74
    0x1071400392040e00c005202514841c0d8460600c40304640350318604c41d0114580d1920444a948100010715014010300b11220a02c0e0761400400c10090407540704603035680094007000740d14209841030070000c100c02c0740c419403e41080742d032980c114420003030080c4c02010280760308010701480c041142c0040031003e01d00d0482540d610b1001c680314250017030760320050194800000302c0448114044080c1d907088919104a100e100c14265403a07804402c0a05c2c005413a6030320800183d0742404007892002d0024180c100d410340020006048a01c020b181c0ca00c00c0c2c114036034a01000104850081c195542030030803555131180030105440e402a421001d40341071507410004140040300340c0145024641010301d100c020103100908a802c8021402400c1d000f02d07941e00104101364a0301c2488400000381440b00c2d00d0300d5140d401182823503409420000150b882540b102085003080c1c2c0b5095484a04810058015011030b84c0051020001410181c2000350215035005030a56034800800c074400904000c125001c16 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 805205971 1250 805204721 805204733
    0xd020d0b0403080f091218040c08071205100603021b010c2f0d0f09031421041215020903150907080c1f14030a051006030b0907030b1c 59
    0x1c4604034002400c2c103000c02c0c82809940540760280b1000c4019081514811300c003100355070020610281e05074421524000d00f510785100d03000400440740d540c4071308c51411140c050144000701c0541e0080c18944010046854403002c0303030005448251402580d24035504034032420b42002d04403d501c0c6540303000344503603d41d904159450408141c008441c210180e0300d000c1c8031220781e00004c2c1c6002c85e4001d01d040f020303207520070598210f80030f403603003070a0b4030340d680f240c03200140010054070380c40055102680c0503564000840b03030035400040172482680f0303090030311400c010000140702e002004482c01400e1050500519016510034185c040d044407030383e551951401c1c00c142c1d019604521317680951400440c06c0c2c080440e440c030000101030030303514001078015141070751922800248000c104007403070300c528110002d80045026901c07840003c90b840c10700301c0340c00400e182154403074002e051070036400c4c10103503c030f680340e803a40043c05040014031120030101080041c0040322103645d03103200c852000010821 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 805207221 1250 805205971 805205993
    0x12010302090106050304030e120304180501080c06040b120a2d0506040b0d080d06170303070f02011b110106050a0914010e060109181407030c0206150108150d020d 71
    0x10089904840999a070f00301a900e6100030b035000342c00030b001100f0034901820038100c001080003501085904d0180c0d6034100d13a8040714000c10b0300b42034985440042080440c200600304910b01c003114507a1900341341c040c24540034451340031048654010400001c2042070f82d40e001341d40350070160020140d004034801070340303441d007483d500a40d14107031510000c202c203400e041c415181e107403078040d00301c91a00d07050352510815074028440820410781c0300d0101240c043c840c5207039510103400039001991a070414100c060000102001c0840440e031500100c0d140e04c18080c03400e460140201c0c201111420320361381045025040a4220030340201f4100c9002420400650000c4103034407503d00d584805980b281d0107103140480641d1107900082c1145014403000c1c9081c3c1400d0700800e011080098400c0380d0365800340b11000c04640f41c40c04a96210050480c041d01400445c1c3c0c081610329520042008074800a0120b490107083c5501c83d8012446903030540e112041c0c0c51420b1a0014080102c0d2004c40c60502d4801c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 805208471 1250 805207221 805207223
    0x9030318211a0615070204020f18010906050309070e0a0902120610090b030d2d210c0f0e04060b280f0e0d06090f031d270615120103 58
    0x18201103107a0a40c581c0d5900e45900650b00140288800c410002401030685c005a0045e0780c025400c025050103002600c000b0440741d4076281ca218540b41030a40098001c0440391b2140003400020010802a004049425801e85900c0841c80002d6291660960700420300b07401c00941002d0f62202c2e4444111001503110701c80d403c84030b5001c2c01507441e055150300f50f98190703001c0ca4040d0311200c4012201c83c003610982c0140b40c000c040303a08007160866402c08400c11194011800b0032420302054072110b500c25180c2181d0089040184010071100c10020b2448031448425420130082e640e49403142c0d0b5560700000c0003081c04007541034442110301d6401c80d9044002082e10750060f1112048411603014501c800846000c5403205181c40c6009410b1010038070040030201c0714180e48900c0040010815019182c18900030b0b55005550b800361156001c45441d500b054500c10703404c040c0c541c00c17280542007040380403043c0f40c0400402a102d00010a58400c0885501c55071150045000800c1c040c011a11038126 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 805209721 1250 805208471 805208483
    0xd031e020c03070b04060503060915100804051911090402062a07050d03081b09100e01020105090105090d03091e080a0306090209150901090503010e03040806160903031821 75
    0xf81d41e407205404040e128611a01d008a81c042c00001c041d0302d030009980ea07006c191280d011010380c103c20001401035800300c49103400314000b10140b2081c03103001c01001c0351034041c120780c00d248801a0b0301e030f158014440a40582c4100915000101103464102c141c45c0143e80310300d0700e00c50014000c1d4180e5802d0340b00701c103440c2882c882d040d000100b628180381d480c440143c1546501020b61903070107042c00d040c01e15500445a0030f80400200c0407540344c400c103030300344500c080d6504140b40300c17454002800d440003d81000300c113038104000d2000d035450100d211004107283c0c2c1400140f1070303e5883c04c001f0f001030b000104642c80008040c14400d100f40c40c002010001c0c0590380070041c06032180034250482c05030750301c0190003902c2d00403070b2009213900000414030b075907050505503003a540e40c100080c29260000c43c1c841c2c081d0004201048444400c1141a4100c0040c004403081c414a10781d00401c10010740c0300240821414950585911610b49544030141100410303200b06040f6400e0074900c040d440708021220 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 805210971 1250 805209721 805209733
    0x4090b090603012c070f06030b121506040c02150124091208180d230327010c081216030911090915041505070f0504050d031e020c03 58
    0x80c501031049030044d0344075015049445a030107903e0300218150340718452042c4a2403074003207200000c4444180c0100302d0703960082003080c040740c18040e20004818419400303a0050300c8030a800c20308161980c3d404541070303800088050001038100d160040c400032010942011342e0020685a41c00499458501c0e590b140300302148600030350483e241c80c600d10904100841c900a4580002c0c0340a0081c0386070940b541c10401c0506216000511510b008607088429260314560b20a540e20523411600701446140040d6050080307400d11030200c051000300d0040750192203464100380340e000390301c4496655042203056480b08144090000c07000d001b40c8102d5015004580250001d92007405004c0400b0b51080459030030400003000c1c444030990150806407240038040c40c81d0008141d02e205c031803080c0e009036418091098031540c00b8080b9400907004504024402400b800740035005000c84003151400d44410440c1269410200d804c02041c84006019220000304590140d81c000743c12081c10400f01c2c15100c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 805212221 1250 805210971 805210981
    0x5120c1c060509100e0604110d15050f04030917030301050f061905070c0e01180e010204050d050c090f100e10030204020a050c07140109030308370b09130605090a0804090b09 76
    0x4e5165411074004181c8a610f14108d2854102494003003000391158000550f61a9800d64034416034204a90705802464014108414075034060100401880c1d09207081c90f4030000b84400649030311050248601843e000070004680b926002c00b01c800c4d2640100c1c8a1400c039449840042965000f03030320550f200100c03801c1c0421800b00c5944460304840c0e0105092803030200c50400400600503070050390724255400e02c00000c50392162000103105910903005031203292109010400340200c0684035601d4401712030f0030811001220207022041c0d030918100d40a085c1d8641034921190406500000e400c0307030000c50800c1215800001801d107003440401030301d040c00c3d19840501c46820b0140381c2c860019900420400100c2d02400302c40d504804082080c0c40740e140d0303e2511351103105040c080c96074580320f000190b6404443e1031181c0b403940001100e102480d0b080c80d412a0300445030b0a03c005c1c0c00b80350b4480210b940480c0c10441078846c2e03684442440e4480c0d9440300d41d103006020b070040c0140a040ca41d00081c0b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 805213471 1250 805212221 805212223
    0xc12031d0a140d030c050d050406080f06030604080c01150b090301050708070806130b06190f09062a0b041b051c060b030312010b040501030605120c1c060509100e 71
    0x5065074004030b054880c402c160400c1209980c1800b000341d051000400748403010890500240000781d5042e08e6072513071245003010050482d0001454100e00380c0b030040500c5255030703010a000c1d40040d041035040f9181c000c2201c2c2103006080920501c0040080b40b10001a0f07a01000301600c09040205c000f0400d6545400080d60350640485000c00052120380000b00e40b40380070075a0040031505142c001801c044028080380c280c0d44810700d0802080e54044030400003035442031803044082902d2401f80c004619120015207170401d0034807902c00843c04c2e841980b1120340b4840c40c801d612038009114002500306818004000c1e200c80010220380b40202c0804206800c1503038018140400b210343c40c210030800e40e2075000041c82c100301c002d42d0602040150303a4101c0301201203a03020700001440703da07881c0c1c6080005012181e0075845032340121600c0101d01e5140c0b00c080b486201980c0240d032800345000e40742404102100c0100c8004200c145800280401c4007000580828181c081010410070056981e02007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 805214721 1250 805213471 805213489
    0x20a2c090c043c110309010203040501061e0b0a05090402070c08060603160312020c10091e080619110a02061f0509010b0a02011103040302011b090617040c12031d 71
    0x40c3d00805a25103510700100c460184484859410000101126501080803803644162034000450b034000c03042c80705028080c41050024040a00f90307131981c00c05d00b000c0300e03001c80d114840d40400d40b00208103806406e008000311280c40310002c00842d50380010b0f180100500855000e440001d100f850000f55581c20002815086244048406103034a0703d140e6400d000d40700380e81205003c6002e000b03100111030321442c420702c100e00307607070b80704c04100500b8811103401d420480130100ba0200d0b0204820400960041500790f0440c08191003a034103042c0d41120440a4150186003000340702001401c21036203030b03011030200d0107510342d41c107854000d0549401004050f0b01d00c0c01303034036408060b1500401500703117254001e00c20304034240008106900403404460f9103804c215400da002d41d44961002c0c0c180c0b241e03404400060b02c614145045001c4c01c00c0320003003207120303201141c2d00d00c18010404039040c04420410900100342aa400921254041c900100002c64400d11400310364440f001c4000545040c00300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 805215827 1106 805214721 805214771
    0x7050d0204020c0d0c1e0b04030e0a0302030f011a06071106031905040f020103140919020f1207061407050c130e0a111903020a2c090c04 60
    0x805c081c6200c0451b816004c00142e00070138009060040d9a40c2c00541524001414800c6a000f0904c014180c0d000658140b2508604804600c015044008070601061440c110914004180842805202001485600b00307001c0800c540c00c0401c0a140d100b440110400c103642443d01c21032048890035a000d80346114200885415035800d80581c1c1d4400807100007419151400045c40ea0300c5102e46621001c4105a940101040d5070300d20004106c407200042c0b654a06900d0f03c21050f07990601c510459022940c0742c007803100e00a45940a4540c10f54006000e000d05805410070000c03240e078071102101e0700d10740d2070140a01d03c1c60104900d0040c80c0c4503515480e15074002c42c1c2040a41c0140e80c5014044660320320301480141c40348011002195444404a11088112a141c2d000303050142038000c412080c08041045031400040c1e104c51466040c0c60030012184010420703411003850800d = true := by decide +kernel

theorem cover : BRFrame.Cov 805035971 805215827 := by
  have h0 := BRFrame.cov_init 805035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 805035971 ≤ n) (h2 : n < 805215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
