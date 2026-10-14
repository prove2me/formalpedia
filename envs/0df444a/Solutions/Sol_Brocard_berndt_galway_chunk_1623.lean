-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1623
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:54:58.713607+00:00
-- url     : https://prove2.me/submissions/351ce370-73fc-4ef4-8c80-830e6c9a87aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 291726618 ≤ n < 291906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 291727868 1250 291726618 291726623
    0x4141201270c08101a1504060c0305070c171b0f0f03150a0605030714030c040207021503010b03100e070c11030109170304060c05070c1a04050d2105040311040513 71
    0xc0d00c00d09800031a410382104140f020071070307200c0c0089280315042c41a0400c44904d03075849121b04000400c401d510402c0014801c41c040c0c6011030900b24603607100d18941b0029070103c05000482200d09640007001d101407840d2180c04441c4a0a034040c0d00c0216078091104149103110307080090070088503440500021801c024580c007402d0141c5000e181541c001c2c107081c01442c0c000d00c2200c3d4080b40a903000310324150725000080080040d5811b0000304406988040710490f00f02c085102001c040c41c404d480514003a12088029640b40e203000c0001c6a0031a040d80d000180007a010ba00748018190007120118006800422180c00700944002103800761448580c018140e1610144a1401c1c11142000c0c0d03006522403082400080c40c0310000703c841d401450000703064110030120400107404509003001441d01c0a0445506040c2c1d11400542c00c501c03014001c0c0c40d4480c1600000042c0311603019000025880c0d0306109003041d0440c1c4407000d44031640351006004070f42d42c1c008a40c40d0411840d89070445507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 291729118 1250 291727868 291727873
    0x21060a050103050f01060528030203060c0a080601090506070f14070902040f05090c041205011b02030a0f0801150806030715110c0d08120406090804141201270c08 71
    0x10208064801004248025540b5024104a010441e10306000d14002c40c0c500400b01b2210400c880d1940540d8044074060b120002c102d004c00000584003802454421340e0f0042c040e82c3ca0f451004009044080018016810005485014000d540d07940302a07585454005e180400300e6042c51501042d00c4411461554462250680000c1d00710440c0d00184182c031030700e8400d204c0480c0d40c0c1080c0603040b403054413000001c103002c2c001800082c110392000840310380a03500101e09020129036030310100c0d441054410041e0400200c40ca42035411000310814400c00e803520905e01d601d005040b4440c1540306401100300042c540200e0a40e0350100030407805040c000c0d620007945240250040d1083c00001d48003429401040140841e503e001d480100b402070f000690f82d0302e0114502d03142d40400348000e10844800daa103450b28808030303804501030806401481d1040c4450000c507010403001d4090480c0010071a81815100e140da00303000101c20884c60340020b801c066405041c030303151456160071780291901c0d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 291730368 1250 291729118 291729121
    0x11040909050f070b04060210051302010c0812071d10080a022107020d020601090908040b070303090b090f150405150405030403080c01060e07020a0b010b0d06090f090210090f052106 79
    0x440c4d80c20010f008a45040d002c890290701e0b19012034058079422507480d04441d0a20050344055406141045240e510400450740303002103a8411030600341c0c0c180c0c0c8440c00681090a602c1c940c400c20000c0c007076142011288040014120b41004008404c01444010265008a02071550344012034001d4100c40b0100c1480042c1d1504c100002d5681c410032030140d0051081c0f100000d5905428031681003200e403c03842603031915040080c11004d0707600240e411820150b541c03c0c2c090102e081d030924140500c25502c080d00b11aa4210303c3d182ca03003040d9203481e01000a550301884005100000d1200140c4550300500345165a079040c82c900350b00440d070010b061180c00040d07940340e2005c1940070760181c0b82d000c581c82c249034460071030403aa24007041000030309290803500148050044580a0058081c501c0c130049a05519044544250344c401c02c10714103100d494100034005c6103401300c03980001e04441e20709041c01920307129591100d08a40c1c13090901600c180d9002140000c0b50003101071150360001e00b1500c00c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 291731618 1250 291730368 291730379
    0x114090a3602120f090d03022104110405070212120c0403081207030606090b1206060c2b170a0c0c021008040201022e1e060605120a11040909050f07 65
    0x19600400140019014800008440402040c41c4c40d0090107100f0051104404489058009511540c0f5001020f44078034404c032651460b280920344540d03c510840e03042c541000c3d0034070090380c6000d4500300554105e04550400d42c10100143c900400d003000025202c2d03102d814502e10103116540000d80b0340103000842c3d10701c1c0c20403c19002d01400c030940d01041040d5071040708480c0807540d401104050340c1c1c00c2200103819481d00d150f03980c0000009100c103103801400040075180110340e140c29002842014088804d456903141d80982c628154280150300012040c1d01041c400002000701c1c048541d02c100400e00103214000c8441f2555002e84070702d410962282d00a000241d04031812801072050003101501250b0700f582903c021100c003100d00c580c2042000b1040040d0940032010a02d800c0c4403030404200032840d00035840248402e071034855981b0f00c190480082440c00a1035a4039080c1480648038824440c03100b110100c0b10034140c0001c030031080c0c0c0383c460b0810b481c0028640851040d0b860100b00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 291732868 1250 291731618 291731621
    0x20a0b031f030312050601090803040f06021c0504060f020a0605040c0806070f0e040b12011a100e0d060f0b121b030c0306150112020a0305060114090a36 67
    0x15507811078440681c0440700c0601030105014000100003801400900c0c00c9099a0303046541c100700f05050110b5001e03250040c4a1640d001984402d00b016006441004020f806015005070802c04007010840d141e000300010700301e44164410b400c20000c5018200804c1403090155421030740d4001c60a2010703040900780005404c4030350064031040d002d410081107201d8000c4549042c0302c8450349a906c3c0c980801002c10005003150a000e54001900001a000c50701007031080e254910340555101603410910f0080c003401ca80c503c00d441080c0070082c4e128001035900d03240181e01c0958800d002161248005510f00040e0818440403030b0804804144000401404101d0300150b02030a0184d044d8664600c0c10180d41c2d13220080071640503080700e0040341882003900700e0395100c100107041ca4808040c0c9040e05a00300d030311180b80e460010780d4503014031005680c0b195102c05d24116940c0c03100e04086200c00040c0d02c04810340306154808104000301c032a0641451902505441c0e4180c800c0c8050303503101c0300f920 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 291734118 1250 291732868 291732871
    0x351213050a0503030a081f0512010203040b07140334030504110d20011b06050603060a050103051504290105090109020313060e100921080903071b03020a0b03 69
    0x600c2000700860220b840e050000a40380882e1141d03850154903102c0403080c281c00744070031320014082003a210010405071240c800c4a540380380180d0005a883ca403604201c66800002b4110404120b95103522120740c8a10303d0560ba0003002500c410072114130708017511042880da02c1e501c026002c509908211000744c255000c83d10840c001c410981c020481d603030070000400f1280400038034080d03004074200000582d40305500b200c8101814428070294a041d503903215210100401c46055403aa800c001041c01c00f40440c0e0307045007040c072051145504590340c81c0c5c0c40f041c0c8007035600113024048000605004050041844810543d002c02000c10301c1a603010311554024000c0030b0107440000c0000450b11424401c9a21900f028990007080b00c18642c2c4d402c000c2c0041c130403050890301c5401e01d6000c0c0408944030340b0381c0382442030092102c0c21840803000c050940d1a400c1c02828000104108a0641070101c02c80380c07078541c00303040c81e0b0381c0d1003120603100b4406a00784c101a4000404031000f040c091440002103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 291735368 1250 291734118 291734129
    0x16020118050319030213031e08030124050901050a182c0603240709180912030506100f0203040b04260c010e0402030a0b15090109351213 60
    0x1101d2043c6480b4154141c1c854030341c2100d991070203254104041801c80540c400040003034440c0e902c4409081c0c070391500640080e04034800702d00c02130b120002c82d5940849550550400340c1020f03800c0004400000c0c10700d00a040c901014002c2c800044c02494601002c540041e191640303a0080141d042c80300c640710088440500100c505c15030300800c00c0c91400180110561190312810070000160481c6d0a0010801078101024080b5200c0045455000100c118505407040000019001e28506020148480d811900814589000e05101503901c6034807103c0d000c078580d41842c4440c00e444030740481c0356200301d80c001c3c5803080002c2008603001505000e00708094010507408050300440c4d0b00c4140c0c50f8074080c0e2205020800b24501c200c150b003015009180d01070403c040020f40e403264640420205401c00e410485040d000095128072581c0042c0c18001500c2203000c0c406450f86000c0e082e00944000c1c4003600258503402030a42c042c20420030001c1040c0103400100e40d11060032041030703010244640102c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 291736618 1250 291735368 291735397
    0x70210020f120405090c0a090801020a050d0518060604180b040c1502120d09060b181902120609220804030209070503190c090914090115080303160201180503 69
    0x3100d20320304154260f500360f880c002e00c1c1038195100c20b5000070969020711100c50610000c070074005200c40088c4082c0005941540311203a0341c01408122404580e0010202e00e0740841400a5903012000050600c1d44510f041d10300088811040310004294801488000c04078010710082004001c4000c00800850380c070131a00c0b4121180e459004e0307888030020801428880c9d801c1c00902141b801c10742003d80514054180025290b9200e00400c0050115550b0300325402c080100f4801c000001a440401d00f02901d1b0307045080c461030290a404517034020300380d54441c140700c0002c00c8452003c8415402141a18800380b00e4030034051400a5142d0898403059208520010020300341d24011001c991080d40160340f031204200c1505420b0300180304002c421010042951004030700540103210b8541c18240b0121040164601402c0040c01d44000c000300710b8800406d50010802a0000400d0302d41242c1b074100d0240000702c030380200700c0c0100380354848003600d6981d1050903418080007100404009036034241 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 291737868 1250 291736618 291736633
    0x109030e0a06020c010f0212041d0f0606070f0c0302040c08070e01020d1704021318050f0303100b0d1104080304090e03090a03020112020c0a03030c02060a090201140a09080106030507150c020f060f070210020f 91
    0x101cbe04641c803088400319041102000040006403094005081f0544150482e951064480e00401d0440b80a1030024002ca01d6034005d00070447d41029013540041800d04c0180585144880014214880c180c00c4000500141002c0340c2155038068240300b54400c00310080002c16500800d18011340c594190a4030180a03040c204042001d02104480c8110242d40e111000c0074504000203500380c2c880c1d01001a00c5a445080d0064040084000c00041c0003840003140c485080c64407070001c40e02e00601241d29640200002d139003d450b02d03100c40307046070b8090a104c2c007420566841300300680b248661102090203003651031010103406034006c10880715075508840032680e5501500003100c004d0007000e0f010402038809116002107040042c003809070350b0f01d8104502039032000760b10b00b074a002d5042214070342c03ca035801307000014802c6500800021b462500304c03048903080d008604103084509015019503400200384e11a014503400311002306901034003108201919440080d1900c250a02040c40340c0100c54 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 291739118 1250 291737868 291737881
    0x90f150e06030312070c020301090c14030318010c020a0806040501090b06100c0b0618040f0b07050a09060e04020c03160203011508150912030403020109030e0a06020c010f0212041d 79
    0xa5031031042401070000c620306070704440ca801c00c540d0300610100c01c0141050f21040103071020301a200100d8801c0b000074212a00744950480141590a61180a80c0c03080c1300c11101c801c0d0203404204180000c0c2098801e4450074000300307081c15010741200100d44070385014402001815401180010700920a40c0b240b034844c6001c100207400e40c00c1c10b020004030034101c2100032030314640402d60441c1f4020301180142003080c01500000c203040300c040d26040540c040540903c8005c01803c2c1d4019400d18015290284d812009455030040c0e010700070070015041c2000e44292220350481c0c01040580040f0391f1030340d040c1040c8204005206100303d01039401e0034040d0545002e00440001500c00c1c01d00507094081e40307281110051030004000460714411040360325001560800114084d60281d80040380100c0103090203040031700400362842c002c01c0070700800c000441d40800c00e40460402442d000f199214071140c00c92816000480360741109a00080001d00b1081c1c4568202d14101050428101a0781d4503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 291740368 1250 291739118 291739139
    0x7050f010804060b0406080a03230a09120221031c0e1b040b09040b040309060807050307030e1606020a0201030b0604061e030f0912081503030a0e0a090f15 68
    0x404609001c5903401c00850b00048a50300018001c100180c400200d4682e12281546030281d041030560102e04600a40421410100c10114680408106031403803e803000c04c00902280c2d0b24802c0c40426066940c8580856644507480c00f001c3d007a404d4890b504482901200e41c5946c0103c0c000d16081d00800d400e4005040301d4083c40701e4172450302014100b0300351816041d00441e9582e8a000b5801640c94400c5070301555001c400b01e0046003d03c400f140c25250901d4040d16051060704079800b44140d150030000c4855210f811264080c0304c41c50b001c40c0701c0c1f144c6c0e002d40340b803c01d640c1c448112908140c1c2d000309035181e0001e00b003075455000366014048940c0388401c0c040c403403203035004403c0002d110382141c000610b0f00440c1e00c0d44100e01e070f02e00000c000700c003410a4021191034100858240724001c2e091842c40c0c2d8030140c2103400c912484140c41c40080b4040010766a4420a4020014845008401011030365004106402090b91b00070134403250758410410700040c181145000c8018000e0900803440340300c41d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 291741618 1250 291740368 291740389
    0x40906080d0c150f021e070209010803041406090118030308100f080309040209010915031a03061302040506041401090c020d110c0103020310031401050117010b060409050411150c0705 80
    0x4040c1d940f41c003405a007464400b800c1c8050a4140d210313004c108100740c03030003580d43e4155920701c806242601c0383e100e0310400c00403c030182e01c0a525984140410b1041200d001c03046c0d032040744100d03074107aa41c1d0500c4005851303581c2c0c1d40941c1c034055440180000285600704812900c078550b03103507912544988440b09030b4040140350140710400d5005000b240c4180c00d165005110010050406c6c000b09030741e43e4410011045080700bc1d00010f91183e141400700d5004141d00c00a00b03804030040e0415241ca50001003010320f240b54040c0c4580d071900c0c0822400c0d20366034400220650a500040607075a19480ea0002500c0c20700f641400510076000d81c10741c0c103882841102e100623100d001805480c0702041c011400b81d000078250504a640300340340000042e80000900000700100400403400d58501022001c28028002c070a1030310341d060540d0710000b40c1e0f8000c1200c00380e07600550001a10344950a10054201ca2821016044400504407080119510f805000b8200410701122103040d210341c14090322800d03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 291742868 1250 291741618 291741623
    0x2010608060c070606081c090909082d0a020102031008070e0f0405030f07060905070f050d0611160506041e1208090c100f020106140604151202040906080d0c 69
    0x8607101180d01080b0328070003040314901400003c281140c840d0b031384030b09007000500e00f072041e10031601014600940201741d4900070410104104143d9403241c03246925441080c18001d010111010209800c142903621010601031012203543c440f800080003074000c1d402134500b941c003000e51003000640d052001030070106580c1041402c0342a0b80300c00801900c10303800a001290303540020b01644c0080300c80c000180c588540252008501509103040c0749050481c5034200c0e6601a400c04001d020b00d450340c081402800e80d00c0000014008955031004101e801090b0040010703544a200a02c03d100000035628060340c000c1039604c4006400b000100983c025691004108428000c9441d0026016101c0e05a1108000b415038404100200000b80c04d600e00c14610004902d101d862207918a80c248a03503400b23044094081c0103c1040ca04c006007440c0194411801c0d5000340e280440a4680300700d818002c1e00303a041e0800d640b101c0d2100034243c01340c10640504083c0d4442e0442c01103182d841014140b85554 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 291744118 1250 291742868 291742873
    0x14030109020604030212010b030d120c030e19110402040b0318070303020604080c0a020a08010e100e030904020715050112030f0c0c061b080705150c0c0d0309111201060302010e0102010608 82
    0x10b1443d801d2102092001840007459523a401e08240d8540f0f06000400080c4915900c0c010300440c01a60780c01260701c0301e41071004061401013a843c0d40a400920a5032181c0c2400d100c500311561441d11101d03103141c5c510715070380160020800044e42c880e9080a1400784a07000d00080c00320340a0042c0c195201c2040c8000341c0141e016502280c042440341008010007000081034801540158000c80c0701200c00758859000341c0c1d035440001080b44000d00c00c2007801c600d0b80300709010048548440d140c3d039000d1302000c14031541d03000403a001080022003401c1c5c400d8002003001d2080b9a52a11051a0220b45944c00d801103000244004c034420b104040825400d6400324044404904040c17007252103600280340070360301d01a11304443e030110700d00030050702c40144500c0040040951a149235155290b01810002d103034041170168441c08900400c1080c45c10340e051500198074100c508040c08a2410501102d0b004400116407100000041d080030085e24001e07215039811138a0b0030012801c8403a81d108540494 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 291745368 1250 291744118 291744127
    0x60a0903020f060d05040302060907141305220c0305060c040501080a0b060409020c01091101050c101802100f020d051c05090a02091608010b04030309050910090213140301090206 78
    0x500e44000d80b01c400b44005465141000c18030007002044403030644059025034440c0c010490220005c1044002403c0344858280703281800c6000309144070305a20100660580710400100442c40f0741c0c0e80c00510401c00c50384400024100d05000342050000e010540d10741c00352000088140a0b4a0105c0301141e5040c4e50f1143d0903074981c00c02c0701c01403010135442c0d581302d1804c010000300c00b0034034009000c1c600d10070703000010019542c0c45c0060824552200c858103000d800c0c08161040100440d418241940508010a0880300070040d01e00030707002840000e501000d03002040383c0c00341e4840259480c2003419021640d0301118100c0946041c001e801201c0d50011380841c07084075000d055000650003030306500889441200c81d60001714007074030885044c0b011580a411851041e5448003d050041900d81c46c91490903095480003403094246000c0c0342c2c010b60380ca4000c14007140b026203010b4001c0c071701810708640360005800204888035103071094a00c50300f0026500001ca24062046000150f4018003142c0b03013 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 291746618 1250 291745368 291745373
    0x2c04030804062a030e1002180a1409040807050c0a0b0a0e0103151a071502030601080f0f01061419030204090c050c03030106031d06130b24010516060218030c060a0903 73
    0x2900045c4485807250082c11290701c0354070b013507001070800007242d811030b1407442e07112a09201100e08241e1091002451382d0b14035148688402403840c1d0410b4010760310b141c0c1c0c1e200d01e052841c038058910400c55005001c003400000c04505c0305020f401d6030300703035503886e12810a0b6110044040c1e2361015103c80340c40304460000c0000030219150198134003061108582400007030f4a440c0d807104215090302000c0364000080202940c1d220305a41c0d40814250700c0f41a882c01c064090170100030301402174105000009103010a0152000c1c251089035800d850040200040305000030080e4100d40328042013107040545085000d405001500c03071100d400310086086a18021044002d80500c04115516038180000000c5a0009001c21417081c1c180340304079002c80c82c2030300e41412059402440c50b081c06540d100ca006000402c2008142c0e000005d00e4442e032200d4040d03103c25001903441c04010b0400c1c1c4005414003421286e103210524241c012416107101010350400e0040a105070320f841000100641400d200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 291747868 1250 291746618 291746621
    0x21501060f02120708090a060f0507060203060f09070e040b0d02060304110f0d060204150e0f1011030d05091002132106060909150b03072c04030804062a03 68
    0x40c0c080740c0344110f41a01c0512070183d6015030010350b0507245400700007001c4001d4181450744a00414182ca0b0201041d46603040c014964003800d0b05c0140b40e40e4000010503184d03540d160741c00a514000030000046400c0007200038020090140240c0c3c010740c1408005603d518000c0300c81242c190700a84298a0b42e99640d45031106240d100204561012006810b060603890720f00e45050f20605c503060040e5920f04003003a85020090a0302d0140c1006900d8070010160380320707180d90714003a0000356124910200988026aa28480c0c110295018400400c10a11300900ca4000324002e04241d0b003666001c41c0380d440d0b820107900c1200c00c116445904001c04001c0e00018208031110082400e44088860f1000e50300e110030b4803a03903480780000c03039250100c0718284100e001c0d2810403420a030400700110000d40c0c0200303440ea006441100c03095500c80d0341c0b20f001103003920448001c01412604101c41c3d854181b8005d801c0c070701c0c00c0d070301955020f252513100c08035500071107040c040c040e8640b0310051840740c94034001c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 291749118 1250 291747868 291747887
    0x70f020c060d241404050c0706091119031403030f01120f15021c0618090f1425120f020d061b030e030f071407120510050702150106 58
    0xd1002c2d945110000d00e801c0d500b24101e00f804804100480c445250283c40816140f000380c4040c480c620300f50520902d64100320071942203d502900200d40b0b00e03010f0802c00041304007544115001640803240040c80c00d6079001c00d0701608c0c400e004103a201841800da55589000869400000f40714010040c84241d003c140483c040f24400c04a0a5581f401a80ea04401c540c9686014a1160700800d0542c00400107c140e4441845416030400c2031510300020400058007984510700010ba44141c080e0a201e81c1102d5889140c1d00a86400e2058074101e4005a030303038800607400c04810000200f10b40c692065100b0b648100c035148000c0d21b4102c41c0c0b030b49500c070400c030b10880100e910241001c0504e0000d1158020024180c03808500411040300b440340103001d13904400302403c1960001c1019102c401c0501c400d031100244c1000b1a507040701c8518280307514040698000c0008072844c1010002045000200c480f4600301c2081c0a000e01e0b1900c0509a9035905002500140008860300500c0428422107910 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 291750368 1250 291749118 291749137
    0x8090910090207080414030f100c110a0803060a050109080a02010302300114030304031e0f02150301050a1205060612031b03040801060b0c060103030507031806030b09070f020c06 78
    0x39050503668540181281e01c1508200c0743c0403804241080146010030041c20302c01d1080c0c014088904200e421242c03a040140741022100d03550b002d00e84c0b002031061000001c03080c41042101c94081c21405c080f0110f8004603403c500c40d84402c0000f240c254820589082120b0142000f04118031480e40190081d410001d14850307100da4800c1e110f01e003c2046801a181c400c034080b102c8803154141019443c001c0c040c0700280e0300a500400017080011a01010780408458040761200304098601d450502c01d130031154080e60203100d0740e451803002c20090000f94100c0e00c08888031398209a843d44401c5500c81c142e80e014003213070000800900141001d5840c00c4440005000750707450214841c403172050070703035100c0000310f07440d8004a41880100824412980540b9020966905090401e01426600c60b01408000d0401038041104400c01d40a075101000682002900810903610380c04010f0040c440c2c500120300c164644004103032181e010780d040c006406540d5014040c0303460350005016085e4010f440c003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 291751618 1250 291750368 291750391
    0x2030a0b0c0d0204030f1502090102030403030e060c120307020606011d0103020a0e04060603090209252003030c0307020115030b131a011401080a140604051f030627080909 75
    0x15032140b807515200800c01365108000c11041243d090a03d4505010001c1c00614140e20403c0b240c0c946a80001c180d400322030b031500e03011505489020210741107000301c0b034006c0902d200d0080d0707600e5200c0d041006581b10302916402c8414943d158401103411200d10800307030404080009080e40c00c0c2d44240c00820302070440c2d0034000644024200070a04485180c0d1002c1d0000f99145450300840c43c080700b040d60000c56580c0760b0341141494070903a014038001c000c0d200c1c1c02d0009003511440703480d44909000c041913401c2415240c582c5442d001c0724000c0e40c000c807501c038015440c00ca0111291000800c0b50001c0d00c0c1c010580d41c80540d0344151181d40342031041d0f07040e0f8400c800c141e96130541704da904140d00e004e0705120301c045601c0815100050141d0801500d449240c0e4284500d0108d100a400c400c50340c403140440d00403c007601c4100d0b0040094000c403201e6004d00c1c0c0010380120078001283c20051280701050244841c04800300c01441d21010001001401c0e2601001201c10520304000c0c03981d0040d100e1f501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 291752868 1250 291751618 291751627
    0x905060105130602010e010c140d090215181f020705090a0612060204050411161518030f091a04141f0908060a090b07110f0a03090305100902030a0b0c 66
    0x4840c0a03482c280c0c3c40000180e4690400034801002800f400824042d1400c1ca95000c0014601740e650b80c0c0103d007916a0800d0b03440421106546c0d404c080495850501d009450b5590031a1051100502401c03a58a0040041d407984803e003400039083c8607200d04590b4040c1c9495410030040140045000e4204800b80752644004200f008001e2000300c402442501c00580d91460a0180000d540c2c40c207902e80604201440f90442042c8101407050045510070099402c42c0511401c41c0c2c01844120f5284460003801c8004808154004034001a41c00c2039864004405170740391001c064019425400500b440000e003c00c2160350001c21040044100081c4490000c1c0304001001c1c244080c40c50340030380002c1a0002c100110f01c000c0c48030a8109107401401d20018541392a5031081c4040a898541082000440e62010721020b0182031f00c05001e28040d915018068203000b44501110301040d50726019044241c402c4840520030300b00720a5011f07001e00f1594515072201a608080100300c00344e115410803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 291754118 1250 291752868 291752887
    0x1707120e01060f06091512060b031608060a1208070501090b1f050406060c0f02030109120f110105010e0610020f01090f060b030a080d020d0f2c0607090905060105 71
    0x1030a02803000e0340000100c1d1031401c03580101d600c5950780008280010100107124034500111640300d000c4a50034042c2c6603a5082500100400540e408140048000310500940c1042c229100c9080150750303956a40a40300c440404c01131104910511040f40142c105450000e8092405800000e01400001805040302e40700c45585110403101250850001072140c2e8040000036225070190005480811065041c00000350002c0140c90000d0030b590210f81c00181103680c00d400c112803607680900f182c90f80c500110009024860038111850101c0c40311010000d4198051284a04072007991090a22070f488610a2248a5040355410000c5014803c4c034400c00103c00d00864000030f1054140300440007150400604661002c40000c1c480e03000501c00c900803481d017000b941d03503084400c040141d50781a5000350340300800c0e21a080800f10743c140421140000d1000c003e4603401d0340c8240180250034011b480c1341d40c951034221040b602040c2c81950912945101d684210350081041c10024540351050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 291755368 1250 291754118 291754121
    0xe01120504111011061306022b061a0d020306010c0c0806060108090d140a05040302130e0c01080708270616120b0604210209180616170712 61
    0x44506440800301c0c1507042ca035508102001040080091030a601d007240340001c0940c56030006006440400c46110601003406601d5040f200e242040c0f40c0b0101100054408042074602c120078040049407400314005841a494080d5100c0c01003a000f02030f00c2c1101408521000f504040d0003141040000c042110001d58403821110107405000003c1ca25485c10100050403032a00500c0807040b900408010038004c1d4200a00e412010601e45125888041d01801241e05018a44c00030758048001d0a801c1c003804102d034410648100d044064070061400035005403028107040e51640005140040020000040954500e60014240003140c0840206151103460098248c0354600340d15040c1118040d0580c2090700182c01c890000c0c0c05111071009540020228000d40c841e20103104900742c1d140c0400460320175100d4035140c0c02022880642000c1c070f41d01d030070320f01d00302046000c605c100b8000c28803031600d1480ca80070006450b6103864000c00c509544105411010340550244040e1541032034035455603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 291756618 1250 291755368 291755371
    0xc0f021c020d06021903022109390103050708010b03040f170c0c03010e0c04091103070303020f0601050303090a050f0f03010203071d100f081302100302030f10150e011205 75
    0x2400c0056110420303e9805c424070004100c54400307043c070402c42c03400c3d83c02141080071212860303035441144035a04e0031301542c1480460914042d0b818250b840100700c1d5004411908080c6040c07624000c83c8030345140041d002c82c0c000380c0d040703070200d00560f0041081c0107241c0011980107128110b480381440941c0d8841d8003502420011955240000c80c002e452800208085950684200d0003800285030703643c01e90b5192511158100d009a466841c040244424401180c40046c0058103e4600d6656410300a4549480080c18000350245800002c4c60785000800e940581c0c4000b4600d016551408041146104425082a82203c010409500035075420301c0074612503516a224a80024503106000703903191003c0002a104503018104040515407200707818400340301e5410304040d5a290000241c3c5104035850b002540441c1c1e0443d0b00c0d00107a41034002d5401142c03843c04e03001c1c042e00d810204400703d5116006814507e40000c044968140c401c01000403d80c030123060080c9124042403004056580 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 291757868 1250 291756618 291756623
    0x120712030309060b09060f060a0c1e030914030c041802090f0117070e1602070b040b04090c030209100f030209090a06030b06180a0c0e0d030801150c0f021c020d 70
    0x19250380c0c0b80288002d130b0292601c3c800c022203502415103030110018a541f1032806025004420129051080d180203032000c044e502d0300440d00c50981c41e00c00707040d940540e00038401100026481e1b50001034144000e00045401c00004024241c22017072102404018048840842c021101001c009000340c1c4540108601641410a014546604200c14070b0340c624502d03070150b4040d5014010400640c500e01c181681c004e0300081c007032072080b6a1941d04a00e8041e9903045050312000000d400200c010750b02d4010b1003100c0300b0801c1801240d8020381d069040b80601b2407070707a8011102c05c661200b0f080c0314010f504205106400c0060038081c2000204805881c12140d00c4502c0303540d80b00038024843e0b42904158054000c546c00d054410345100c502a00341c20140001d1800d03a07c540c0d82400301c42c0615440904000003404501400030617080090210100b803255043c40c1568801c50b541291050361003000840d00030046149034286a4203021840112041c569140c421094115006030386a1300c85651050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 291759118 1250 291757868 291757871
    0xd061e0506030d050f030606090a18020a02010b0a081908040f08030c0105150109030b0a020403080c16051002030a14040f0f0305060703020301030b060409020111010213180213051207120303 83
    0xa00001490328100c0f4001c05141445004c2c0182c002444040007180c1e0703c18001c0d00c031140c03034801400100d45480d110350071068000358400c101c45c0445130607a015085440c450340c000c0c041490382105002e5001c9644c014801c00d0b400a610a0501014004508108921528005141aa44400c030844130040380d001803103d508001140122100c007401829040700e030040e0078010210045d4000b0f441580c684c8001081c06003030b2400a400c00a855054400440d080343c851540c400f0682141c581b0303500080da2000d02030015031004100c90038000d4070383d043e69240b500194504000c0e07100030f44010070071100c2034503820030401c808141c11500d001c1032030090802181074a107007802c51410a0400b0b400401039401c051061004002060b02d284001e600900199000030b0060510b00040b1000f80a030700848100c2e600010b40000300c4071400c92200200c4402207054030781c16000304448000e910501102c4885164a8101030045180940d800c0e0041382e500c0c001c807401c0c04c0d603426001ca03240782164815400310303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 291760368 1250 291759118 291759121
    0xd0506010207150c1b050906130f0515030f0c03100e070f03060509060c03040507030b070e0405240f030a060e100903020705010e03190303110c01020d09030e09040f020d061e05 77
    0x4040c040c070100100510814040070242004d0101d4480c00380103010740e205090070300100b9049c007441e40c4148003014850400f03110038030309211101128941a6840e50080c450402030010181000ca05400c81030b00081c017412000480001e42009802d00e0120801e550003094000190410140343c0d802c011841014046401e15005504908010300144a4804000100204400601d01203401c9099a610451200550b02ca20707a0854000580d8030721160094682824885d5070100321300c03440c28200511541e0b40c2070392804024412080c80710407090760950702c024803150019090b504121200221380b01290725541c070010340c02080d42c40c4290709902603040080140659640702115141e000c00c00e4004080041c1d80081000c5802e100d00801b0b410569105140e03a01001d9003412a0807501c905070083d52180c004440000040900c824114040382c0841403200b0726003007003043c00d84500d070885a01c16034800c880d000e01040324420380041b81c000350364504c200b40d4500d100110400540d084400010766 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 291761618 1250 291760368 291760373
    0x30901020904051602190b040308041505150a0501090b0301050915091009060506030412030c09090903080a140f0a0c0e0604031b24030908093c01050d0506010207150c 73
    0xb003140d44d030442041040300d000181c0100f5020002240c00c2527041c5880c141650399401d00d120402840003281c4410fa013004d09001c40f0520300151084100411154100c1599441e401510010003a02c146108040c050004010501c1c00d56502648000341c1c0301c0790454040442e00148d4280c00841d80240d04c029018070034012040a8440c0340043d1400b40c940c0c2d4034604150322420503802d0388150303c0c0205038503403405050082c4034203c041c0080c100c0c0750701032240c4201850042d1221a041382d10708009172034200a50305040e407000120303005001850600c05180c88851440008e40700ba4901e02c414041030700f04168442d201c0100601c0214000c1c02c19800c0158000308080d000003055010034143c1a6156000c203d0714401000c2d845050001e043c000780b40c0f9003030320303008455000e019100750b071000c403c04050302158160860034402c1100741c510004001017000240c10030304810344019001501c180b28030303811148580d0045401c600140119040580e4904110112a20f006444400100d40750740f40800c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 291762868 1250 291761618 291761623
    0xc060f020f04140a0e06040504050c03100f14070903080a1b060606021b06040627030602041502010606090608070c05062508010302090714190c1e0f0206030901020904051602 76
    0x1202400c41e500f201d494a0134441911703854024109070b114560303c0e40480c080000c00c11004a551401805651002004600c000b008105000311410a20300340f00040b50005c103010030a921490880c1c40f070190540c2940c0310003006030400c0c0d0401062281c04d4880200035244404c00c445043d1091901040e40c2d400d2000003400c085104a0320342003d044690302c1c100070f0341e600701550255102c03440d040701c01c650002c03281295000c2d860414000c1e10704d034900200a001040e0014001d983c0381c081050703000c01d10320000300d080314820321800000814611051109d288142056504031406142000030b2005644070746062440c181d46007500099066146000c8001e210312180805601d4140f100e415071458003c28104400184074004100c0d0311070f2044580500c0c4819510040985442d00e0450000884d0190400d80901d005881c40120040f00030954160802482819903114113041081031803503092001c01c3c2c1002d8655001d03035409121a42d0a03803603510810340b00c3d210800c003001321a104d4041c089d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 291764118 1250 291762868 291762899
    0x30316031701180f05070e0411041701060504180c150302040510090e0a020f0d050601020307080d05150402270103062304050c28170405060f0c03090d0c060f020f04 72
    0x201c0c05c00c410810181d400041c040c001c0102035801103201a0900c3c00c0360341c90701c15500b00c40d5014800d02801fa0070400d05600c58019141d007170710104030141d503624614485028030500101040210b60060000781941651201481024240036062039214400900b441d48481113243c001880d15400b004540015035800f500b04c503850314214a00340c0ea5203507964892107070041100d41951600301040300f0741d10170011212800c0d0480c114588446050004801602e42600c1c00b0b04031590b0400d024956141910032500360304440c2c0f0341c0090410304002140f42641c40341d90403605140d95801d0000d070302c6080920130070903170880104e0960a02620f404001c01c171140a0607401c055402031040c0c0400006502c0c0c00740c0002c05058030f9000c1c0c002d05200c106e03507141c0c0744d403014071400404005000410500140e468003a003800301000070301c0d54480300c5400460100300d400a490380d1008107061090b034001d0324242585801001c02186400c00880104260703406500c0d02400148002410130510301030b4203590 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 291765368 1250 291764118 291764141
    0x5040614090a0b1003080c0f060c0a1d030f100f0e07050609091906030b04110906011e1e05280804020108060310050906060f0a030203031603170118 65
    0x140904000e2852075031403101e40b0006110303180c6980410381c001d0124000c0e0300110340c0300500d242ea0761179900741c0d1a00d8109a1a90701868420403001c40d00088075402a030346881210b5540d016103454200310344060301c1d6a04401307034060041c221740700640201808030b4503822030400c2000c6403119801c0700b010304481c840f21f54400b05401c14001401165a03600860311712980844000c0c0d651380380d4042d0743c81c0130304420300006101440d02800100700f00410707484034401e0b80110140c0d1a420b107088180440c0310421180c2c0d0740042d889400e40f115002034054003800300f07101341c605a40c03d000c08034202d0000210f008085000f064020a030307040c080071410914411010341d2604800d203407070341341030141c03803080c02920080c1400036800010b000c54608006120004200b140e00b44a24140030031800d4440c0800c2d1117040c020301c40703d848a00310381401c00a5004595015009601e801d0710b8a5010a000354141c208508102805000d003003250904951140a05451a82039225000b038000a00403505249010f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 291766618 1250 291765368 291765401
    0x30203060a0806131103190308150603100e090a0606030f020306010b190c0f120c0b09010e03120a02042402010501091b140d061409060901030803180a15050406 70
    0x10815002d401e14420a04d460b440450f2641402c1d40d940001e040100d980c0c0130b00c41032600702c0711350030600d0703800340e0018001d03a00d040d20101c14124003001e00c44031348003c40b0307070700d20302e10241030108910f052110005601002c0001514003402c00d5039102400d0f5200340c1d200b5981c034014020507406500e418000d850042c40000300041c980076a0200000400d40e80d0b008c1e00e4244248a40701c801448000324803e03040981c401d00104080d41460b1000d45161401502621086c0c81d120001d504041d05204990805c81c02c03100845c01e0882d40d80850501e130f030300108520041e580a20000a41841203075250f8022110f001020300c8407003c0482c02400c44605038400c041c03040c04c010300d9100d00855005070645402143c80d040c0c005410650504216201e0144c039011294905540092002030100440216400c00c0320790900ea51074150030440c00c0d000a00002d041c002040011608c108051030805c1800000c1c413041e180b1162054035060020b840751070a52002a80760710400042044512841900a00c15840c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 291767868 1250 291766618 291766621
    0xb12010b0c060a090c0e0106050d110406020a39080f0316030e0a1a04081b06040e100305070e221509050c030106030c08060a0209010e0915030d030203060a0806 70
    0x540c1e5074038070000e0b103410300c4207546440d10b0f8140807140c0344a401501151000c0072803543c0d180700c000c01680c048a40b000d00140741c0240c451045920000300d03402c441c03065009001c0301d1700039115460040c01c8981ca243c280100480300c0c400c00d014403150001c0e4520160a4500c0703c528020000d4200007907034000001d260020010f1404a060311002850300d0782e01890551103510100021400c8079801340c2002d480c114480351414021110796000b40180c030304003800c3da80120f07030910180c08280300d003000450340850203200038400c80170038880761680070580320015034006607207484603410001c46400050042c040b0f501082050b8581904245000c146800c01030700100d40c07a1211a10580d203815060301880d20780f000201071243c20080076aa040c0020002c02409542c0e10f440d003484082407090500e180588000555940081d209032103881906031030300c4030300d0f0660208001001e40000c062184c01500100b03003505a8a0420000d418601d080d240184d4a0816408100111900360b002d28004d030700400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 291769118 1250 291767868 291767887
    0x3053a0c02130603050714010c0b0a061404150b131a0a03110702090606030a14180f070b0304020409020a03080a110c0a2409080d020d03050105120a0f08040f0b12010b 73
    0x60000d0880707240c41d4080300007075040e90040303510030b40070b490160540c0a12000d200041d840d641c0a4401c54a0030089001003030700d80380c244402e46404241c0300250b001180d50800007403900b44002d05d5a474034119000862181c80d1043c1000c9070341c505000084074038000c40d600d60706d00c2e058070070502c02d090305111050810801d580042d03122000109514041c000105c08608100400d4000307514444104504140b80c3c40d0240c0c1100c0d500d84000d000e50300d180710b408150241c200021450500762607008a4580c650740d181d03002d00029200b24002280c10141d00340300003020800c05000303003424114684d07d8030080c808807c450f6250542c601700a074482c1710146420080c04011014082150150041e940d43c220b0005005844503201c0d41c1c444110303401580f20004007a40d0103d1104441604d90f00d0411041e46c9a03c140402c154820b882c0030405e030b01030031242c0c1c0800c044030700c101d072003510615095180580b22580307e500400b0650001c1010702c070105916014400c05640c01d4054a0190182c03070402c0e8100c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 291770368 1250 291769118 291769123
    0x80a09050316080903010c0c0b070f0207031101050f0301080105040204110a090302120307080714010f110304030309150c03020a020c10051b0304090207120305070903053a0c0213060305 81
    0x40b4241103450114010038810400410240c402c6050028000c004284200e2005012500c01480072191034940e880007880c06030251018480404e02c96000348030482c00c607a100c0740e03001051242c40c0c3c1072207400e02041d00340e12803072002180603018030000880c5034142171042c8010355082d040c544c80383c1c89080c420381d0040d80e4401070f40b10441e50100c1c0ca41d400100c00c0800e0b00e05500c1440c5003d0096640002c1240600000710240a0042200b4008111803140381c10001c00703e80c1c03804d2210305214420000328010034401d070400c011150150950046039081003802900300d814041000b400309402085d03d58490350144040c40c491502510814007400c26488020018820b002204113100701805500c90081c200b04103540181920040840d5540c030f55045c81210500c5003a109000a420701c00000c03a4180304d90700c6a021030b03612000a0000040c200540c510100110002d5101da189a10880d00c8000700f40402044848103a120780b204000180103110b981091604d10540e1142090307410000035800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 291771618 1250 291770368 291770377
    0x5010806180c0a1101050c040608090a081902100507080108070611030712050708160204050a09150c030e060c0d0605010908030d050604181110020a0206040e0907030209070f080a090503 81
    0x101d140c081c0e483c00700b410255035103490300310f5208a0390711b41000c2044040082e4001d0007035844944030b0050f20740ea912940703692108002001050f90ba010300a00c81c03950b4000f4140b162940007801501d105012450070101246c20880b1243c0019100d1001041140814484c2d94040d10640c41c02202102d06408440c0d40c92050000041010603d24103019405101d40256000c5a91020000c0c0e55000040521130001c0207422040c2d1003140b600020039042c0c480c034462024425803041e40040b600440e0034542c00146041046c2200b450f44410300c11084640030f01c4054841c1034200c1002c1c0c0c48900424074501100e1035a000b89060040500051150510000903030b00c0c500b031075100c08038540d6902c0300890701600e9802c0b02d056030120407030003500800c492401d031640d80440540d8501040710207010100e0f911103000002a401c601c3c100000c1c059540300c40f5100d60301400070003c40390840ea980c0d0125002140c11600080019400c8608488a65011421340c2e04044031040c03e010514140d250682c9078030a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 291772868 1250 291771618 291771631
    0x118030b19142409040506180c03010e0604110a050303040b0705070b070623010b0f130b0f130b0406211e0b0f0406030506010e1506040f0501080618 65
    0x400c4070203000391806a4214145071140d2040b5614242858107204101030201101e0304099a61807000d91401e060910316180304640100080199403a51101c0c844d2242c1e80d002c140780c0902843d151401d2540703090294002c1d0006c4d13070004003440d10300b500700040c1410f00040390510034013400e4020407040d50000f0684043e5880e0340c1c003c3d0356038012450f015141a0302c503441800c007468086101c00c18001c00b50700c0341000413074602450506011071030303010107040d001b4060740d14a01011b0121500d80d402480c003034a070b00c03e600c1807441c0340b0385d07211a140c4402d90400c801001c0803140c00282c01d03403146414920300c4020000d10f1a45800c060400d41c0182828903001070140140304081c14801041c0465040042800404c50700000c001c1a101c6121028110070700701c0c2d500602c400d00c0c1d02482d81c200b5128020840b904440580116400d0061501046a029108490352080c0d441407400c5641c80c140184010304884151012646c5010005008028010700b11840785100b540c410b2603240c4e000d805e02e40e1050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 291774118 1250 291772868 291772891
    0x108070f0e0f011503200415021f09050708030d06030c06080f040609020102010902090c0a020106050319060507090f09020403020a0501080f06011404030c0306141003030f030b0f09150118030b 84
    0x1c0842c13608030f0003001140a00220401e4521714940c842c01c110008005a45081003001e00b80300c8003407410707a61001150380c160419800424450284900e4bd0f100030600c503c9035060700c0300305680b05030480ca1078000d0040420ba140c2d03113002c200200845510700320f00401860505011034a481e000c2c00700c0f03003440140060151a1900260011680f0079442250550350080000e2240d0500c181c43d280301d6004000c01030055860880c0214192800080042c1070041c489142002c1c110301c1d9440c80701401d4081c164800b4081030300b001241c104000007102011b0141c5600040e15145140100440f4030703001d1703101505001001d414003090880c50700d5825445402828a40e403944003090004110380b06642c00980351840210707000c800c0100750342124102c581e8140940906840b10f00b60100a400280700040201e461504000c0c05c950003601324a0300740c00300401c00b007401c82a90011480c0707800115801c049084004000ea00d056801c03140559115445400c0d09a21a0850b9038030740c4608005440c041040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 291775368 1250 291774118 291774149
    0xe0a03050a031d0d0806040b01020a050c042d090308010b090f0d03210203010305010614060a1d0d0b0406060603050114060309010e0a03020a140607090b030603150108070f0e0f01 78
    0x2c18032501c81d03c1c0850411044600c0f04070544001444500d090300d440d03100da8185580140507607c0040d00360541034003e0007a0920344042c0d030800c0002c081140130451815180100041105110070b9140d60307010038902c01051381a41c901e401003180348142c200c400140024001c10000b0348440e40c200603c0c04050300c2101c100c1090b401e0a0341c1010b00310b03440600600d5103150907060014241c0245048900c00d400034410380d0744881c00e00f950701c088651025080783d004d2042c1d9140341c0c443d2030f0f4030b80c100d54291a40301c15459074602191036014421015603c80640c8814070003049803d03c18400100a02e10b010841c95040c002c0c41c580415a402c03000e4030a800100100c1e440507400c0d8450800d0825100490399040000c4c80c01a4a5086001d81982d05014003111001d1a00c5d020031030510400700c40d540c100c003103402d003038041702540c01c080c1c00c040e05481124519113400342c50045242c0a049640c009082c03140c600b02d103403d8500c0341c98000090010300041030003400c030400340c0f1250654207120440c2084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 291776618 1250 291775368 291775391
    0x201030218040c090503070f050102060712091e0b07080402030309040f020d02070507052713030c0f08030109110c07050f0111070308030a05070503070206150a080303090c040e0a03050a03 82
    0x2507800d030141c180e0710a160540c00519290000440c0044500039029111034680c0c07481c10044030b84503442482e000d60007080c0000e41103441450560481d15140b81d001034a2040b40c3c4a6000c6500d204100000441101d0015424817201e01c81c4540d20640e0383c60724450740c0c50181e02190b1a4007c111070140a02e071100201c9650041e40d030180c801554100310119103c85150501565501c6644a82d40c018000c01808403400340aa94002c0914460000318000310780b00d0890343c801e0000359080540400019080d80c400040d400c0e0b800e485454019a00c054813541048520411035090590301e900080c010030003003e0441c1c011560704100e52088503405034403402840140d0702e0f10301c4220f044140d4000c0007070100400441101442c041c0014220810156503802c409903554441618503d0243e400716000a501c004000140d4130761840142c0200c412650310802c0a00e0f582003500e843c011034020101048142c1030501c51091600304010090050729800d84000c2c02600c07070110b21404164607881880314 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 291777868 1250 291776618 291776647
    0x30305070504210b010605030f13030915080105091005011205060102120406080709230906040b130605120a030518010207050a120311160905090f120a030516090302010302 75
    0xf000910070040c1c0918907401182c03120024200c04075081e81e003900c0003080e5070707216109480c401d4003000d088030b4140c4ca80440c41c03640701048003c228200f041300f02001c660314002c00069040402c4c1030312100300d2541040b00700140d111000302903138200c1c48180000c025036a4403100c00c1c1c044800a10002421b92076140c0104d0800c81c414500405004001800041c1c081d8092602c601c189115950710300d405031030b001d1900c012010011816120040c22404040c00d1601102c51600503030000c000040c44032101012600c13280190b26488031040d0345076420400c2e0300b4140901d607940d421a2000e450648030540e4003410502564980306e8600055904c4400c15034001c21031507014220041507154100d0b5070300e900c0c40000311b2104080b0005600000b8800003540300203055007000c465014220700c1e16040455500c010280100001514822104100384800060040d00c451a4907822030075590382c0e03018805010341e074024007003048000720b440c10041c0b4541c0c481e20400c1034a40c2482e0160ba12a02c0c001d4211 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 291779118 1250 291777868 291777877
    0x1103010c050f0d0b0d140d0201020906040501051809130302010b0d05193018030803060d0602090a0602010501170307020d2405070201060518060a030311030d0501030809130c020a0303050705 83
    0x1a0410700c8151408148210380c006146c440c09040300300c81481c0360800e070407400e0b4028500301c260800428003080c00030b0760007100070703000350007400440a05241034203002400080342a2004e546074041650f16a050680c20301410140c100107a0ba07401c40829180e40d40b0395140d40390301c0060b1f03903007002c52611002c00280310700031903001e14820300380c1e02e00c0c3d00582260040344032034030f0310080443d01d25108a81406082c428010490f40c0101d4081d0440e0364078010700400e0b02c28005c048801c2c0d80c0c05c00a00c0481c0d6103030440384001d80300640c00043c0941c103000c000c800f114182d94515031243d106000030340c010780c1c0d031801a0711407561190000741115039500404107043c0800c070051740090304000c10017003d2641540007000f2641c00301e0316104289000c111071a0540c000f910b010350040e4440e6000d00200f40640006444a0030042c2140d10f032110b004a06c0003100c0e02030700110358540d800654500649001c0aa10381b001c1002d0340200410031031302102940d1001d041100805150311040000d071034a00440c10798 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 291780368 1250 291779118 291779141
    0x1020f03010b1b2406100207061b060e032212080901031d0105101e0e060d021c021819050c132607060c081e07030c1103010c050f0d 58
    0x1241c4d5150558012a800e030000d0005400007250640052840d02d0000d12221078412035401030b1810700c0c10310340f0441703403900e1001407951200f080142d0381c030019003c0d2084451420703000001e140c551140d00c0c107002201e000d80010f801851074a400a0207816106039800101e281d000034125a110760380c0c030058019010f03120f1042080c41e0320710500420305d007064201a00c11885601000b02c07664031000c112000c00810100e8081580040c6801d02c00f1b0f40c4e6100d05140c005100810388034500c4510340c00180841085240d82c540820244c41060440c100307440410880d82c20401300304001d242401c901e81a28054080307140e8015181e502003070b0b0310502070003115215a0f45041000005854018148001010042c101546103800030f19001484000c1144010307196903a0b40e20170b482c0342c1b58484d1034498010104612000ba1a400719021003041c020040440c0741c42500e90320200c100302d040c004000701c01c5041e401d000381d04100d40010a02d92000441d0301002c3c00701e801680380e0b0141d0118600801318007090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 291781618 1250 291780368 291780373
    0x6030e070f09021804230402060405091807050303120402090a0e062409060f060d140114101d040e010b060a0215090c090c0c010e16061101020f03010b1b 67
    0x400c015507241c0040c40c9020f04284c010710701c0c000110501040f152110f084001c002000c0b1150400380c00400d0609801900080c01e060400351102c002811140c03043c0c0e03105450316800300b540296444144540002401f04402460402600941c841c00b401d5000780020b10079001c800c0010710313407400b562004a81250342404c5662030303d4140054000034101650340d00c29002d20380c551815916200b0569407051101610568449005a0034401284c0010a907604c5990310740020114044100c4d030308078024054400030351034100e0041c0c1401032010303c0301200300401080c01c00703090401796400110706009000795000100e842000e480030740140100b10368242d01c0714002801034036066000481d8164500b41c80315440c8a900d6600200799551500543c26030001c1308000011080745500003c1e00720b1185020000c40c9030300c0c6200250b0f080c44d1074400c419044481c103000601443e40d200c40c0d03510b5140480c5008500d0003180010b04403490005101d843d80c09800020a41c0403105000c0d0070041c0d203040c0b9000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 291782868 1250 291781618 291781649
    0x309050703080d0b1e04111b011b021605100201060b180f030f0606010c0609050a1211010b0306011403030903061003120c08030402040903020f0d0c0b0702010204050a06030e07 77
    0x100030209030f009081203c1100d05100c1d4651007450450303500b0501c48480313620240c0880020303062001808070080034041c498018000b031900348503522000d5180440103000098516080e289103060006282400c00455100d50300c02c4080004600e00142940d000b210065043e20821078128090700840d00400109000820a40e03041c0350701c5034143c03905002c1280c091307481103000c1d0306240da00c004584400b0780962161012030a0b55005a6030005014014100401c003855642c80d00c80c900903c03200c044514481e201c0c82040715a40c048050344010403001c0082c071030b0840900c00283d07180410700031903041e41024a44183c240e9000c204440b200703840a8160b81040c0b40040f4203181d008460301c810b442c0b003198071491112952140d003402c0d600030303402914581107481c0d64080c0002004a10000c400390b106000760f60004407020003002c509042d0a60720306171f40b80403501c2e20261840011340080d044d0381c0140000e001c29650054840240d0340b05260001d00c0c0d8140c000d406141c03005591140010204109 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 291784118 1250 291782868 291782873
    0xc04080f03120105010201020c0628060e06031c02070608130605010f03030e0402070305252109090c051b010b0405070302090f010e01050f0a03060312030605011d100806010309050703 80
    0x141410040c4502a00b10681e40d0b000103a0907071054008075407554200b07074005a004c241c041e0b0200b2900d60446029802c90008525140c110755440c1c00a4400a842c04104540d91a040001c0003042c00490b000342c201c00711500b000788d658000c90043e030083c40103003400190321050001c0401c94075600104140300c103594494601810700300c1e40c042540010400643c2038000e003424001c0780e413040d0b40341e950035240c001d080d4458400042201581d542c2c20000302200301c0400d68418000720328990012408505000000f00681004190350242054508101041d10640c0e000400c2d503401c2c20311200642d800d0300b81640054010041039080503070151404090107030455155018102041050710703030b00c00319107003040191188680303000001d001500400c640604407611754090042c4000c6410b02090594803591391a200c590480c011600290381c85c002040290b0744000c282400d01c4511011000d45030000c40491145030138242007070300788240d94011a601d64883d0340310803409500b01c8156800d0640b40d2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 291785368 1250 291784118 291784123
    0xb0f06070b0106080c0f1204060b280918110102030403050a0302060105040f0227031023010608070c02010e0f1f020f07050d060e01110c03070203011b080402090c04080f 74
    0x3e0194500040c000000510240b1504c0300311400191207510715070824814103840550440014800c0311903035115000c0100b280c842d10003001d80900802c01c1c005081c005440c41009020190f44948170590400381d8443c049040440115101c5801400d4150384d00e44080050f0700e948200d138001080740c411081c0d20018558042500d03411707182c04940500894500a1340e40c002d82c0110304410b01c0c2c8e01ca404d5481c0c0c5222821008200c4050000b6090740d0301202502c00a0084443c81c4038071018240c91084004000b00742803035124090001410000110700300018002e2062134121802814440f42c0582d801c110b917a58030311825028801801120302c2081c2c030046005206c00c08207004050701c1030038101c030030004000c9642d1040d00c0c405460340091940c60b40760310000d46542c18500d1a9550798950321210084101c0042480005400003103540b0a050302c185800c49000c850360b00c1c3c1013060f00c02c800e0071307540e03004440b0394001d07404581c0341401c6d88550b2081320b100c1c455030740444101d00c9000070030070081001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 291786618 1250 291785368 291785371
    0x50c0708030901020111090f0d05010f0204090902310f02040f080f0f072108090a060504030c08010513020d11030303130b0609060d140106030218011811030a0b0f06070b 74
    0xea000b171044402d40303030304c480280c040c01047d03650003050318a42003124100b0980850006000f9400802c1d452003200959003282d102e9002121480d480743c20711760540c1031044d125410800300c01c9410400e140040c5a100190404111049045e5210683d1841c440c001e60183c41c00340200171418640141d503140c483ea0b84941c0381c1042070190040008250b5040d00c04544103044880c080c0c00c2e00403003846040030007400d80200f6000c642a020911149001380c554100e0308000e0046038650640e607074218240310080416a5022210b160304001c10440e5469581141c1c1126582c140c402c01c4504540e49030803500060300480880d0107201c04001c10440e00c103e440301c0d003000c6020740324140c0c60b41c44184c248808000c00300c40c0c1c0c51f008000144d00000203941c1c5c1407a104580c4031140005202c586a6000940100c03500000d507039486114401404103204480f80481c8441e0340744420043e5405401030240fa03404010800c030040ca965100c0290161901d80344040043c4000f0000c0c0e564011034030303000442c100d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 291787868 1250 291786618 291786637
    0x2071706010b07141002181009060e010224010816060210180b0c030a14090604030c0c0b04060503040b060d0210030b0109030804030c03050601120c030b07090b0c06061e1f050c070803 80
    0x1011444030146c0d040140c503508006102e03507140510b00740ac01409a030f04400e2000ca0758118481d0744000c46a44d07915524184050340c4002404146502d03243c80c00f4a01a140400492140c11904040203c80d4001402c94000e07140d1890210710007034010b0300b003a80604c1100b40600b480010740200301c031407520b6400440c400e40010100300310640b920000c150811104580c4d103103440e03120501080220380506000b4a01510510540c3c0074561924081c8021790007540c00b6201083e004020b000403c028032400035403003181512180e0000c2c8854001903204003207803010000381666943e015809922030701c080c8000d9900300030700f40c0e83c0e07540d030b490203a1002800f0312058a06008400012694201c102c107129042500051749100c00b03411074032450203443c0060302c120240100c5038000101d0408500240411407040d0028000300c1c5821001d0120400c202000e00c4443c048504510800da6981010800b000c412a41c12820f81c46220000751028454003002000754450080b0003d0107101c004010300d81c0c41d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 291789118 1250 291787868 291787897
    0xa11070f050a180b03150f0f0603060403080a110c0709050702060609010b0c0c0d0302060601020f030901020714040e0102070b011a13060c030311041502071706010b07141002 76
    0x2980c84140c404600d03954003910703034004500e0404210a444844604546562140300000c000b0090000240b40211100090020301c1d0782104020064007487c8209608c04501d004103001d03031811f8030000303413140d100400c000e05001080022900e40c503141da0141f00d00d4004114540d50381c100304c0c2001e0740d403000c5600c0b030300c0103d80c03e00c0000780682c2d1010595034010300d409002c850a990810003400c000d50408111940e140c0704010152981d6900d000020f9040390007a00075040751304114000a08000c502c8148800c10b074010006407248d640c0c001101c10886070800c4480d040d4450060014000d4003103942c0c0200c1540c00410081c080c4000555501c1c121620a950004941ea8070031f450742c45400381080308040b0301c0640e00f0800c902d502410055014600c0780c0340018040c0040c0d013408469030001d0304905500e0340f0003100ca080c0031307070100b0040c030240c02ca20f2100c0021034019109581c2e5407805000b0302d015282e02260307030402c00003505800005c0721b030b103078080c0d60404e103000f118403000350010009280040c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 291790368 1250 291789118 291789133
    0x5060109020406140c0a0c090e060703060305031c0e060108030a08090d0e06071e1101031107020a050d03050409381806060d06030501050403031506021c09030501020a11 74
    0x511107031088070111109502c030b140004113402202d050710b401c241180c6009010724208000000c6d000c1a5142c09010409800645031a2160003039142000003020702003450329261080c00401d4000007900d003480d03100c081d40400c004101c1c4000c0080e18003440440c8580c41901c001080024001c0f000c0c0013000c3d101d80d1640700302d60398140019610000280741c0d01c0880c038240071210031400c20000502003507024281d120710200c6038070302c54040000748035000d4a80540c4444504141e6070f040c09406492180860400d042070403980000e000403009100703141c4651038000002d000c0600810545006094080c4204010505c100700c00400b103290351010000c0f601c030003c01c2d206529007400081c0b00070f1400b801011400502c2c80c00c583d2008800341c81542d111310700707020004148000e4061500074500c82c2c400840e4504007480c2c040d080d41c1b02c02188204581c0444c006000a40d8005004442074400f02018801d0000d5200140d40200440e08068180d500000c0c0c040c0320180c2191195244802440495215 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 291791618 1250 291790368 291790379
    0x20303040f0b06361608072006040c030507050f06030a0b0406051302090907050313060b060405030f031908011a030c070f0b0f010602010e0c0f130501120c0909080306011128050601 79
    0x1551080b5442801b04145a0100b81c00303e104a03d06049180c20400d021496503601503543e2034600101d038100e43d50100c0b45428800c04c201407083c5401031000360341032154201400c0004e03401d0700004064828844d920024121956151f0704941e0007000d02400821003092074081c000c0283d80050250f5024100a5010403246840fa5089901c10554060203084144140e0360f018040c0c400b0f0448164800c20500c000300706640c0900c4000d0224040400440da141c0740e001e01c4100da104146d01031070610110100400c4441c5030f0003000b12464a0305002c041d41c0f0303078038901d241c10f09008010014200301e5203040034000300402e0001d058000d42e94041c03201c000343c0c0d03942c40883c280c07080e2600041044d04066030b103040f03500b41344007000302c4640001c1010703c41003da50445d40c1100c1007680300701102c1b543c200301d000c240a1060003480c09403c6607a030034401d080254603182d20511001d130100d410021100b088440801c401d1003252070b82041c245501c002051a28120403000b8001c4505032403900654000281c07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 291792868 1250 291791618 291791641
    0xb0919050705040b070807020d0c0b12100302030a0f0606030b0a06080c0f030c0f0307080f010b150c070b0d020c1608010b010315050f13110d0c020303040f0b0636 71
    0x484592070001341c42c11400f80c0d980c1890b80c1040800b00d800950394840341c3c0015110306020300c0070b8109007409507210304e81c002a0802c0e8200250942403010710a8a061000d82c5001c15050320740768003c0f4145041d64060b01e0030100810855102900c0498080184040c0007500e0308244219480e18003110406400181002400c001030035050340d150b44014125441c508100e4414a0401d10003010fa034001c0ba07540740b80c50300b031803204040e0f11101e9546842008940c6003802c6c10149807814040c0d03075410a900195245da42e0071041c0144c0305c9a450200f4014410001034040352000701150090b00d0000754180e0007502e60603030500482c00d0950034420006460f500c64810843c80e1500d440c1080c0301c4900c0c3c0341c20301203059444044550000c80019010061540c11301a54003c11060a1101d40c1da51000c200c5030300701e0711000181e90031034004000780004a90250b4512400326080008581551200d4000074070307188104614144410068141304070302c9181882e5400780216600c41000d655030780000d81c04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 291794118 1250 291792868 291792877
    0xa080601030506220207060239030301091a12010501060f0e0303120603010e19050c15030a0506061309021309060b0307140d09081e030105010e060c010b0919050705 72
    0x80d000450080316a0400007013103019202c903840e080f401490700d1803549500050341d0020300c6001d002d2040001c4001c2035a1280c42d40050030420203440356500c0041e10b5204c4e120711042c0320b01c118507502d8100c20010084d2580ca07414031503000030b100c00b0710b0301c91500c1d6440c064031092242d1000b003049405644182e03801400c031098483c0004015500d0010760400e03040002d503003d042142c241d0341c0d4011918401c0000c00000498010702000d9000781603c81ca442071410060303545042c004ca0420342c0081000300003030f06a13034000c07004c450302041e90307602c50300403c50a000f200c14201c0800c03078007800060400290341c0101000441c44100320031064882c50382806503040b61248211511003080022202d51240741ca0840800310340030f4161810700583d05030f01c281c40c200e441c1030f03c0703841c800145580c06000b0201344000d4103114620060842d0302d0140080c0c4445a141c20321400f035500028100141c0000707601c10405000001c1010145d418801d20a403050442c0c880d4a800c51840c040211740114002c0c41680e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 291795368 1250 291794118 291794131
    0xc090f072007061412091b010f0e04090f02191a1602090c07020d111906080610021501080616030209130e0c0409060203270a0b1009110a0806010305 65
    0x10480c403464101c04032400c1d441c014a00001060900880303415071841a802402005110000c0c113486a40300c0401030210320345500359042c841c114207c0e0754075a4104481c0d11003004122f80000d001442410300c0b02c0d03200d0030080001e50000c42066024545a681c5982e001030720700403203100b6a1300141841c0c0401c544140780c00b00030313000410300c044401842c4c43c081c415446800911540c2c20300b00f482d800300b44174483c01ea00444109184c030710040c00034240310810405140140109400c104c0c43c00f8406000c4a04c0076001c0c03405010160007141165008222802042c0781758440b600c2c00d507951344a0b03152a10310a9507540c50b010108462000d034284030b4026240f64000040c036625107108aa0081002020b6504071640f0341c1c01031030215001640e541c4920720345a40078510251390313031400b510085480010495540e404c0071080c800a0023070000001d20440b803550014694643d5140d865034180e1000083d40108202418403a06480b8401400c018003024030180d1203101d4070752a10790045d000d554045404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 291796618 1250 291795368 291795373
    0xb0702061e040b0c010501031502120a020d0b030624010903050d2f0d0909060803040306152304051e04061d0312090c01020c030307060e0c090f0720 65
    0x100d08040302410101c0c41c1422000d0718924095070740110300d4094000d0a810f110a035900c41c0100107118010b481d160012400d440b00314a4000d0030340d44640024009407446801030707030104a02c5c0320710407158881090b064006040f10079038509110341c1207459070204210300d480700568000000315400b41e10716909a80d80003001c0e05904d0102c00b8215442100c03000c5151641c00d0741b100110030048200003ca0103440b11801801140c004010003900c0e0818603409007070324a207089010032440401000b56801d03645d12080c0071400f0300c048044896130341441d801041c3c6003807212980c0000c070321482201e0a1903407001d9801380030582d210701c40c05071540800851070f2007500c1d0b4003001400141a41d40401c2043c10130000c0061549910801c0500e590081e400041c81c80380b10701c080c842107404c10098101074042c02d2008103024008900480d4481c00388520040a180e00c07000010070740c11082c002a0250305001c0d142450310300d44000000c102c240e040d512000814040d801e0b2006002e04130050602e414090b800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 291797868 1250 291796618 291796627
    0x102090117070c12020c03061803160f02040e1f090308130201090306050a0209120a2a080a03050d0b09071e0e03010c020d1205071403090c041d070b070206 68
    0xe050440a0007030202d41002034810b500307000036100210781d410000d040d03030003420b03c00c0b0620149850102d02070a03510800c400300c0865410401c0c00001c4440c81c0007118030b00180844145000c103140c0c089988003e501c14180204014031110005040020400031134000000040354400c4100700c03200d0180c0900043d00d6200001d010740c4c4401001d1a03a07500c180341c4448402d5494450000305d400c00d46e01d01c0c069940008039038400d40351501400d50345007801e030060101c01e01d2595074641d1449405d001032094107425203081600c00d4041041c2d400401240e000e8030f18202c00340c60000c0241c1c0c0800030741008117240c140d0000540c1001c41c0118072401d025107422203205111a0344100d04d1160544450811910404c0002d80c0d442c01c4c000c61340c0c81c00305e40e001020000c5e0413240190900b040d68628000861038901040b08040d03000c800106040644600c07240d41e40c4030304590f203040002e400f644e00d4015080ca0825808440c0180a007031850451109498a0503240c0c85041818412480042d5001e403040c1b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 291799118 1250 291797868 291797897
    0x3030601050906190f2003090108071404090501030b011d18010b0409140f031204020402090a1e0302030601050a03051b030a050601080709050a02040b0a0e041116021201020901 77
    0x100902e9a8080103020700c0c00c051607503410503030403404004100006203841c2c48290b98580c005e4262080ca01c0005080c50811072200062540c0e802440c0d9850704000301da402040303066000e81d0b000319030b000043c55095034840d00d81540501510f0300380300458000710404000078541a080e1001240c200001d071280015441e00300f0392401e10107620010a9480d56a8000c400281e41c45100c5d90342c4640c031540e090309080325003415a5041400c02d0b00940d407250020084011540d14042031540c0c019030407a00140c4502c90900800c84003020303034214160801d1094000400007011240a100300d80c401c900315125a80c03240248240e201c102d03c00100140d00084a10b0f20040c08510308101d1040c000d002c40302e0506090310317028500a0281e010f841a608404e2040c0b22001c80c50007095848042e0a82c1940b9091138804400080d1240e10220010001b00c480c0f8296180d4403500403281141c4003040032501c1348000851a001a101e0b000201c0c414035903503902c0e1821000600030799168002c16110301d913991107c070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 291800368 1250 291799118 291799127
    0x2091905131a120f010c030501030506071202130e0a1b0507020616050304061706010305060907030510050402180123070f030c0501020703050405091e0c22030506240303030601 77
    0x24800607014001100ca10b00c00c586980701040800d051000042c1481c0781d40c081094212050108407000301810326005002203100010704680103401c520300b5401107010945d50034003d01030b016409008a4600e080001c0d4480c2200c0818000d1114890402440c918814219403140c0c414012102184047c01610003515000000e802080ba984210304006ca205603211070640d0701c99003048009ca400580d80042403910a000745a00c0a0282030030482802d0450000381e480c4402442c0304101500c490001c1c12030a03000c9030700320090030082c109540303401400c030418101c070304085112400900c1c24280c3d14582213a18240c00d651400b640012403400300c150300d51000030b1000c40b50036000c0c440328600ba480003440034401000e400e0300950381c2c50384460601c0c080019000c00030f0120102030494402da8003c0c440f84d0038109400100303500040383d50b1100d91969003001481002c0b081c0414002c120004107015000c030302c1511070b00b43c000441c1d4040c00e514442c01c00c8a080070404c0e03600b503031080c800541154088c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 291801618 1250 291800368 291800381
    0x402120615040b0d060c0f110a030512090109060c0801080f070e0601180e01060302040906060302031e06270703150b1207030f09060e010b030307150b120708010209190513 75
    0x15055100001311a00e0781c3e0282e0f5401002d88001440c400c0c00c0c034030081d5002400d65807003407090b0041d104038543e545006000d80515407904060882c160041014580254024941658085d0051103100500344010304000d100b4400c0c0003c900800a00000f0501c012070b108058811080451745191aa0070044665204002848142d040c0241010800da941050380e40d000740000c1d500540c0c3d907400c0455010540b41d03241d001c42d00f854014018000c000c41116082104030b0180683c10100e41c2d1040001142800104c07484503e000740a00840441c80c10038421600c9510a0788092006202c00c02c50080c560034580310b00c01940368140034468407007241c035051907080034180c03401051a4041c807038048103c2d201c0c0c0604580e242e9588103040c15514080c0994152450700f2005503003413901d99260501010074070000001015507030240c2881d1136448009480d20b20920b40200c620107601c41c101d1a001f03505c6000030034421a0109090912400d400c0c48540558401030000521f41003092013501c0540b46 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 291802868 1250 291801618 291801641
    0x2190201200714040b030d030e03430f080d020f0409091106040612020f0d1b030608030708040e07020a02061602180405030304081b070608040212061504 67
    0xe20080c41e1410305020001411005181c000362141a1425004800d8040b8214400303000c0d034100020540950703404030b040c031055401400d01107402c40d1a11005801c2d445000480b50058400c195030148500b40c00c1c440f80740c012040501500e00f1103103180341910124200c1001011a000c1000f80d00014404001501401c0e00103040503041500f04c0c0003942840d00a03800c0190800c0d500c495040610204003010b82070b202c1d080e0b440a15203410b003038004040e0320b0986405001c43d40c00003000d24072007200c981110910300030f03000d007000031034a10407051205001c1c0c400c03100002402c0031008564a07201000b216140d40c0e02240351840c040c41c0007401c1c03c210b4802400c0c1c00640c0600c1070840c000d41c0311400285102425484c1d25030705111688100f041a48491042c6035840181100304400510000216900640c2221800344c85140c3c0142c090303034510648045441380c0c01034a000040140c7c1100100d4000d0f4402c413020404039402e12515580d6000480c0c40ca81d00041c44085140541020b50240d0003506 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 291804118 1250 291802868 291802877
    0xa1409040f0f230d08010807120507030515090609070503060f1f030b180304080a11030703060f051506030601020715110f03090109051801090c0e04090c030302060a0c02190201 77
    0x102c1501c071030304503000190000d00c41910700000340c000b5036003e10004030940f99604001071703d541001d400503903d000e14001e8105082d845101c40c800c9c454200107600086600034100e0308003030003440c0c0c0c800b504241512492558490200031924600f400f182460503035030040d008200315501c00c08020f0000602805006c21000d03044440f2103281f21800110000d1405110913103c1400c1c84240503001804401000d0003a030824001404038180c0403510403e40ca8000062100482d40c007000241018102d90009240074a80a00004a10b80c1c82d04450701c07a403ca040f40069900081c0d041c04803a2000b1508140141c102c3c51080c0070301d0381c240c0d0080c0e0140038185841040440200348551512a81c9141e0352059400450001620341c0d00ca0301c42005270105442d070b503e500c610342c1c030101d000c90418010281081d03182c441d1040341d5441070700751030080000200140120380190a04d1010000c2c60301040e40103000c0c41c00006d0700031045003c3c001c41026941c0c0100300b2020841c81c1851107400e0707080c0490411 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 291805368 1250 291804118 291804143
    0x906080a022b110f0405040f051606080c0c03040b0304030c1104020406170a0219030506031606021005090a0f0b040b010b040f060507021302121006230a020a021309020a1409040f 78
    0x385c8851040a1207540b1074055401c1d02c004c0760070300c10300d00146025092944516560103021a59108445d15042503806521944502d900c40d80703242140225080f584010202200b00001e150744007010313100803805490040121391290080c081640302e00e00860700400c03030217124503c2c0030b00202506540055440001403c001081490117407201601d429080003130f03141e0b814031041703203801c1c0407168450b02054900311442d45410320203501e0345e808029a61700b02c2d81d642c0004801d80001e00140384095803080e503030110701d501450021440b8009980c20785003081010000700b1400201004c680075100300d0000c00c0b1000e4a4104121030542c803540c0304903000010080c1030600d0303000d14000740c03c0c003580044692089290190480407448102d40c002c408000900c0150a80203501035400440352405036003a65580d20380c000d0581c94043e01900007500041d18100c024544c2016501c40c01015200700e03440060956556040c002e03802d22000b80643c014800c0c03000c01e00040424840420140c880c41240c3d801 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 291806618 1250 291805368 291805399
    0x106030b0a060e0a051302070c08191b05030601060c031704030905040905010f0504210c080901030b1f020102030703060501021b040c3509011b0f05040906080a022b11 73
    0x4484c4004421b042c05c2c0c02255080421030b000c0402e5014042c02c0d030041c0b02444100c0c0007007407014064903020b8078080d040c500554100440fa09040c0c0076080150840329075503510900100029582c0d9419000501110361072040c40f80500102030180b60140c0d1003802c40750500c0d0401000f4104400d085600703651301d84141401d44070310b00600344514010034030035520003701d86110210071407000340b25040001f90054540000c0000f025200154000c1c0381c0001c02c0100d00010882040050745a19480302000081d203c501ea4150001c41c0304401070742d0180003481d600da005990350422600c80d006014084081005103080c44c0d4062440405549410902d410f160341350070503840d00610021703241500184080c40d102020005080c0c00228000003001600c903011010308000681c42d5924040101098035240060310483c00e84001d0400310100b0011a5030702c180190317079002104e404901840b0300c840144541350a583d490044244509248a80700700f440e52419100401149030b50351060800303444412 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 291807868 1250 291806618 291806629
    0x30516210f06090c03050705130b03070921060c020f031e0708040605090405010e132003070806040209060909060a200c0a141f0e0f1203010306050106030b0a060e0a05 73
    0x38042e51a000400380781c020f074000c054846c014020814000100003555040342800703000d034100c0340318461158483c0c494040440f0044180d0340200d400c0313030411903441d0003900380c541d0508480348500420417600340c0c550400d90b05c44c452800c00c454581c105109880111134904518a04040720603d80c80c81e084980e070301c214035a002034100c07100103040803802d940c05091910807940503001c074005014007490803c5070305080d04441e6034001d1040b01110130301c0713503201c5000b1070742c040b4250000c051f10702c0c1540f02c50b0310305d941e44402c80d070aa125601e82800700d0240d0511a003101d01403074521000e4405030703540a5580001c0d20f203800d40c0f0985801050000c040002006010705824040c44024100c504403904020f001c0c0001761514030000d400807031000380d080d01100300c100d28603466100040349070984082c1c4a400c2000710030000f151350140d40150f10580440000a40c1a2485203208100c145d88500701102200c1d0105092a00310317220b614280850f42c001c0b2818401c645006242d009056210f101042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 291809118 1250 291807868 291807881
    0x10e040e0f061006091401050903072c0c090603010e0408070204050a020c0c03120322060204090b0111070f0e1812030126070e0c04090908030601030516210f 69
    0x1080c1c1c00060601c4030483c0d05020b100020415441c0003580c950401c2e41e2850b28604c0d0841d868188800020458440d450a0180c20000d056622250b1038030301480c6220b46071405146c10008090f90741000269812901d8420342e41c510602070101c5056a00b40710300c0149203d8003410680340b860050007003400695460050310b101d01015100542c403081c52607800c0d46080a090b0006200703401600b1440490740070350060301d0b44140c5c000c403a03980c06e01600200450079100908090b1021340000b802084464450708040c003170490030f07a195061001e40001c04c5850307000500032008507194014003000b03d45000001203410100d00411130b219030315641200ca24000c3c01c09019100e010010004100c0302620300320060500c0d100d800500800442c4180ca29100c3c1a0344c09114000303501a0041005801e40000761000390000c04000c10499041e410f080d21303c2d420454031036001034100400940b900c4a100b803001000c031410348a6a1056604400c5003c6000081d1401c291183c0c2e29440358455212074003401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 291810368 1250 291809118 291809143
    0x1030b0103110d120c0c0b0319021602030a0c03020a210f02061b010504030f020a0312020307030207020a0b250f0b07020c030114010510081909030c0204021c151202010e040e 76
    0x480d207018680f600346102411ba0380410714440e414800c0000d4442c40300c3d0200c2e09200210300050351190112200202c0001c098006501403055003070001c1005040703900181501c0c0219013000101c2c0d6111f4034484158540383c8141840642005070100107050b12004000c01403008145504101140050700c0fa801102c040d58051a074481c01448203140d0031007054040c4844a101801c5d240305280c80150020f00f10882d40d440095000000418403841307581a1003200b03900130b0065000d42c0d51220104c515801c90384801c4c9101e003030400008101604101098151584260310815814007a00d540c030b078541004107000c040d03009071203d40d100c42e5800e12a0030220015400288060b505040034000800c02048546d01800307200702c02c2c8400141c11751100b0044004416000c6035481c014038045a1803407144000135001400881c400756904002030207040d60340c00e076030303006c01c50008240c91101c1c0090440c404c038200f04103054000e0300554032940c100240c0d03a60241c40030031400300c5c14403203501d82409030400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 291811618 1250 291810368 291810377
    0x30f11030c030709080c060a0c170403080a080a27020f03010501060906030b0904030e1909061410030b0f040b0d020901030501092102032a1213080601030b0103110d12 73
    0x2000070080c1c001d00784c2800740c004003008044481804011808130b10400440d81c0034019071800c510100003406da09614031022030078141c3d40711552803814841c81d0b000301c0d00c4100400c0c0c1301c00c001080c4138000e01c01ea0b18690b26500c9900c0815803901d50124860341c084030241e0b000706071020307040d010b51000d0180034001c2001d80d96803811a440c02500900301c9480917041031141c00510180800b203580070790107104640089818074501d034030b0820140603504056209401c071604200d000100004890f0041600d00810b4805181e0100c004c04100c04403544600450342c01081032801200078200b990001107443c10240c00c0141300c1000b83c0008020400076802203605a4580f400d1000700400307000005c2c84288030301046000100071813030180d100d001d16000030758240340001c20896400340050b06008a0040c8800b502c0c400c1d40c10420302e074103039030000b411300d20043e450103000105e01f2000034203141240d030413003600c5026908646d15600704024100f211a8440c04024900001c183c0c1840b01001420301600d6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 291812868 1250 291811618 291811621
    0x90c0307060815150901030e0f0a05210a081b09030f0303040614090709050a1b0206011a0a0503010902090303040b1204050c0109030201050702040e1e010f110901020d030f11030c03 79
    0x920a851240f2118514040d01e4800d4800d40b00310854402d5a000250900300410301c40120302419180c003000030303155182e900c03900b8844c070280200490384c291401d040b448445004d03032022034810307a035100d8003480030001742c8400d000401038a02a24210403600d840901300d0b281c40151f000092810101d03ca607580660400400c1c00100304181c8200d1080c002002c4014113903203454810710380c40e04500c2c400d9009043d15980001e48041d55907020002c00c1c290390300030001d0044504002590348009000b155550600081b84050700c40099003034400b28a401d0780e49510b160308180c013241c083d400c142011501440180804614105424080c144121801072200500d03e00f9007480c1b840d10070070281190600c20600010710160340d11038110344641760182c42c08180c44c42c44042807442c0c00e50b0840d0a030703d4440b105080040e000320640201c43c0410700c44006125447d0384540100c1d641c450301d0b50240c05a80b0800503004414026005003800c40f84030503002401d80550206045142d01c100c59208250b0700010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 291814118 1250 291812868 291812881
    0x2060c070b1201120b0406050c1e0a030b010206091f060e0106120b01030203130303020702030c09070e0306090f030306090705120c04061101060b1806040b0c06010f120218090c03070608 81
    0x7140b150040c07884480c005a000b01903124160490000b5001418458a440002c2c034088140000c5885052114240100900d200040180360b9088880c200c40001c6c24052840a035600c00a456070040c1c038008054030b040c4d01015102c0b80d9104440d00c032518003c0d101c0000182015040b0202d600811054031204220054107148204540920f000e0b24149407060003071192a0304002040e02626615040040c2c0e1540f4900001c3c2c075111041c0c100982c409410804c000d261588060341000c010801c2d822a0a01e07100e140d8015120f85818041d805554000c1c40090340500d00031014079040009810110326040c4401008418032004680320000c0314000642001400d62044114040381d01c2071000700072880c00c00d03902e4141d910588412901c0e0301d4280301404840c2e41d42c001150001c01600c11216075820403500803545841003403241c40500005040c0025081500d00040c140042e4020310001c02d41840c4000c0315446400905a0403d6100355184c00c00d603500c00700304c4003000c0d0007036482e1410b5529028 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 291815368 1250 291814118 291814147
    0x30102070302280c090c03020c010924020306030c010c0c0e010b03040b0c0c0c060d02040b12010f0b04140616050d120b0321030402010c0b040c1401082202060c070b 72
    0x500c0c0004000d4162403c5001c140f80c24801d105130740400e43e022403590750900049020340519183c2412551030804507a04000302c4901d031100340400720440c40820301011039003000301e005c2140c01a030507401c88645884298841c40c01c062000f88110014400c036a12000d002c140315001b41c01004a01c1070002c10f100a0142c460842d41d03110340388102e51860310020440841d1030b1041c41602c4d5015010105a0710525200754050302e014001100b41c0d03d8a82c0b9036469600305420081c07007401c8015441d024080360222a180c00c075410b5030720f41017204043c078101e2000c0c4a041da116182c00c254000ca141c0d5002c00007201400b68090a003150307034860302d1441d84c0102420031034000c0000d0500c40e80c029502e0b60080800d0b510764182c906000110980c4a0b81da0b030006032040030703104600400901002d01004104446552501c041c2d850705800b200380030308103c00668000d50244c0300805903a0584252600c0912582072a0040e980302410f03076401c0c0f9092a205d60306d458003680001c000c98038041a61024403451 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 291816618 1250 291815368 291815413
    0xa0503030a05130f1202101103040611040609030803130807030507050d0306060903080f040812040315060f1e0302040c120b0619080705040f151205161b02030102070302 74
    0x4903030142c2001829900c08024080d00c28004117901015034500c0406030081c00308441100d40040e09202c800480507807099240c0c01190b04a50b400d00e44680405480f80320300c1034805450720b0342c9a01e0303003007400d41d22484c101d600014a50040314145400801c00540d40c000a004100c0c426180c554a502152500c1401d00100d205ca0108040c54204204019640005280700316504206403a41d0b6001d200400a91071007a500f01d50128030035118241c0640e060007000b00112405620009800c0b1400fa86680c25522544540d006101c0d59007070034407800d00c003281700d003040f6a215291918102c2d07480d40841c007945c54003808400450702102c0c1550707641032180140380c0845003c50340c1502d400605203240005802075140c003800c20000c00001188a401134007210041c281d0f136141c5451107a540c191072800c1008622103000003c0400c85d40480ca05683d0244a00038040d00a5000e82e100075040120364100490b81e00342c513070017020910b22015031020310003440214020781c068840b00f403507031803c180e40562 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 291817868 1250 291816618 291816631
    0x10b1305070305060909071a04080f060403080703060509070e1810050a08010509060a090c0e1006090603022803020405060d0509060702060c090415091508010c0207080309090c0c0a0503030a05 84
    0x2440c9080040f25040807406000359984503207101c0074030000c8d16207021103000e00d4000900b14440da10000c0e031100000104203115a110f596810403a03540c00c00d0850965019104040e046107202000c5841e0b20f01810031158805005441440d2040704110001c814003806c1d00e0f81c81c01420b070510244002d050240c06035020300000e400074030240c02d10310380c0765a54402c0141702c0c0348407569130b14441c01080903135039401c00100746694100031982088040139650b0384503886004003152401e500011800e0190013910408403118042c0c180102030103510782154500c0c10800010180d08020120303055403950090034141c1040c010009003490003000341854840041c151200b9913004400b0007001d401200102c489101c020f9401040b418180740d691080da10864022440c0e860034a118010300003d420469422650108000d10019100d41001d9848060600452526400400095045040010230182c005081c01c071101d103081c8106c01c100d800c140c440c1d00200c446d90000402d000c00c0400300d00403a45c000e903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 291819118 1250 291817868 291817879
    0x110d0c03240f0c091d060405060406080d02010b040f0b0906040903120908040503070b040e0c0703020703020d080903060709050a0e190204030f0c0e0c040501261501090b04030305090111010b130507030506 89
    0x200c42d202c5d030905240000c1ca440d11840d00d80c0d000071000d85440c0c21410080250038101c540480c203001020340070300b480c021002d0080c1d03d0868110714102c0d55001d41030038884080c0500c1c5580c3c40b10820b100203403807000c00640500499280f028451191489641c8400d80241c4425803143c0c1808101801c0c1300296000040c401014071080c000902d00d44a034540140d1101500b030f40d40c000350318040e428101ea03984040d50189040c4100414007a802d4010315900c08100c09407009556041c50581750450180900b40d003005c2d01d0042880703217450242c50b41c0d400448003c0c4116550782110300d600240ea0094000301c4503001d03d00e10000401c00f0420500000e010322b64102c41c014a80603d005649001d14800c180c10080d8001507580854421308070342c004401080701442d4107103070103d2b4820300c600400341c019001400c040c80002e0b030000c80005650991358180d881c6483c040c50311004507805806549950b8a5550751b51803013202d175139029650301e0b0850340d0000204041c6029800a400c45000178200c60040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 291820368 1250 291819118 291819149
    0x1060c0201021e07170726011415040e0f0303010308070507151d0409150b1c12030c2706030c0309032c0d05030304110d0c03240f0c09 59
    0x965000c1004c4051300c0281c1001c2c07940c80c0d203201c1c07100d24104495000d030811521807084081c1802280000c0212910310fa00280001c80030070366100c1210004444020100d8020046441289059040041d8940b000e1040751013000da50010b450655100380d00468034a94006881410400d092001800030945002400e000900700078003e0140c01c0c0d0b982080d1080340e02880342d20802e5686500c1a10039581204051030b00c9210b940c0481c0061900640c043d214000d850301700089030b07081840000090760b00c8009403803140c0c2107500a0700079141c0c1c15a4002070000c1080002000314070701d2880c102e0034091001c204107080c031704100902198811042d5030201414801d4440200b0b800c88082c0e002038138110880a0035840a600518401c0e14641d450f03030303100d170000803040240007001018601481c015825003a42d42140c008111420080355002000c0281c06003041011811101500700010030420782c92424604e064012422103c0344c0200719540c03950b84c003a00d0546c0d030b0721841c0d400240040d4040c04141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 291821618 1250 291820368 291820423
    0x3010605030703240f0e010f15140d02030a120201050403080601080405060f0a180f0506071b0b1b0a030911010f120b03150108060f1308030403030209030f0601060c020102 75
    0x5050480d8290b458a0710b6440044c000c02030154820004022a00707070410888070003ca106019018a076001c0070701500709843c90310828252111001254040901010f4040305601884001800c2c0b54050f44d141c01002845804104038140d25408803c1680c00001d05252a28000d400035030003404003410850b25404000000d8000920150400c2c072543c0341102c2e0b650f45a42500c0030b080302c4034540011900a4540700304110f9034003040c80c1c1d118410030035034606907204c04080300d11521007500740c10014001d80313084010403921080c071a040b08000382841e450b0124058048115030080c1060400070360340d00c4840060160034a02e0304103043c02464000341043c4001c2000f46a4201609901411076964240c109161740030050105800c103c2483c0125640c1c0d02d04c5150348845040304c84014a490800014a5441000e9811441143e00804d82403e646071900d08030001d400400c1e0558062041508100002504200c0940204155500c540c07041300140b0009042116443c040400410070034110001d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 291822868 1250 291821618 291821633
    0x512090a03050a05311811040e10030b010e04050105070c02060318030705010509012f030f0a0b0904060f0b0105030103020306011a07080d0b1206041505090a080f0903010605030703 79
    0x70145410715100f038a9001007104803007902c5c039222042c0006001144100c100314030f0350b550301003180d40b484c600303e00005485010006681002e0018541c8440c1000248600c000c0042880c0e088508110780e042c549131207a49a9480c0070007030b00a061154040c50811040040034011194050f80c2ca02c1c2681e1420340c180d01103403007070001511101010b00303070105820000c1c85c104155400f191f00700b0002d005500700b58056078002d01015500040349541302290704001ca5503804102101c2c0c0d0313007500300c9207540d5800484080198000c3c03c42035030a61540540321066461444250040703015550000707840300d181801004441d02248600d0500c00c01b40010005aa030115060b411a0400e90003401030115100b0041820b2044a030000c101d4100428041c00401169101d0040803070b040d1104000ca0000d003100c02c0e07482100315001002c6030022001c01b807881e11250001504652400103c1c0c00c4041240c2d14010705801880919042400c08190032a841c0f07000d024001c0144820f6000e42080c9085489520303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 291824118 1250 291822868 291822877
    0xe1906060f21081b1603051501181505042301050f150304030315141503010b0d0c050d020f1c06030807060b0604091a0102010c0806010203070f060f0c0512090a0305 72
    0x100a070f1004160340002c05201003807049140440015940d807041005120b55240f80d03140015200e5104040a50582c010805501d40c10382c0e040d03c0e40c14100c00400052a805000c100594005a0a101c1c03400103c546541c00f4004000317205044800b10400014900289204140c1c4504e102d007003445841102e41c0c81d01000c880c0c0c00c0c51503489055130395442c2c1c20b041d03000d00748010400f202140710750300000d001210000e000061a41c1142c5283c2048604a550a01c5020078000c0718600c6104001d02c0940103d603a201e000d07004181d081c09801c01070000c240328101e822103500c0f0090780070300180707428845101103001036642d10145010032480c0e0950710745200a00070884000d0a65641d0307a18595540c0d0740320140e900404100100307100c003c1c41c1c20101c01a0040032a0514059030070440b4103000c142c001c0c010700d03100e407406034011424200b55884e81400084003100c01c0d10b2407595100c07029a041164010052a102c8548455540d204010f848404192000700281c00340c1e00242d415400080d488401c0b80d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 291825368 1250 291824118 291824123
    0x1515190e01021b01030e070b03130c05040207031d15040b1c0c0e061b0303191a031c0302040b12040302160302060f0315030706180501090f03060e1906060f21 69
    0x6806c004003102c2c0d501e44040da4000b04040c1c00040104801c500826140318510341c81651072041c400c2d035800500090f0b0041800040128141d0440b850901502c1c140503220740900404180002c180384044600035030043d08000355170303c07000422400003800035250140540d05140200000488198010010102011507034449c0500140c550f02c00328120b2120010211400241c0760b80741411103803078100c5c46080c101045540d0601d1050305000d1800004494094000350240141e1443c03158150499119a000181415400d0101240c0c43c0340c010b02a0007215101c1000324804c0c102418044d00c0d0801004e100030488007a4941400141c981c0f1090b01d100d020308220752612a12407450f001c6807101030f0281d942c0c05201301040012103031750000340080741740300f0745104141042c5c46000449001c0018060028200d811980400005881d90b02c0507198221440c1602d00c2c1c2c0755094200c42200d1015803003540c030a900d41030140b241e1031010503607500612410342001c86041c45528040d0b01c4605e0354101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 291826618 1250 291825368 291825371
    0x60307030b0303210601090b090906040506060706020412030806030a031403060406080a030201200406080f0c071b05100e0132070f05010e01050603061515190e01021b0103 75
    0x103100710b91000c1080d00c2541a24031000c131070b0203030004680145503804481c0c0ea030024201150000b115110401101c00d0008050021150f66031513000740b001401c000f505440d00144108035a0f8081003840c40608084c08001c1c041c03480320707109820014540d1402800c001c0c803035040011b950b0700198024006440d0080018083ea0b100ea0301e0200090007403030309600110540c0141032040c7c04155040d8821030201d4030180d1607181901e09103250810501581c041d1074046940c88001c2040c840199004550058012110a1403d003d44d5101d481e03044402001800c81d5080a00500051500c07580c4045030382c0b0765142414040c803920000030030b0240003100c605078034103c031503810000c1d1010700c841075111203c840000340d0b14a524a094980e0320078907030b030079511940f800d00c000303245410602580b809448000c0007010310351103c0031020340910030006070f550b1000010b0002c007503a10302d13140900118145020200340b400030358000a011070100c04100c82c1103421070000344104503070b88505480c8440c820310b130 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 291827868 1250 291826618 291826631
    0x806130605090313080c01110c010e010503100b0a0c0611070f08030402150c0d021204140105210a090311160612020904021306090806070e120c0d050d02010b01090506030703 76
    0xb50b0841c421a00c0c031303c0243c2500c102c04078110000140c48540f16500781d81e180c501100d0181003139201c0000306041c0b030000d0f080d402d60141c2d56115201840d04070490300100407519941e1205c18000d54803807001035001c1107031503e0030028031280d0300c900401d040140c00524a4a90256180c8021803455240107005800c0030010070709540346c80c414042040c4100040a07036030f8004810540c0d80d100d510900c5001172107110099100c03e1440d1050b80c040724084642140c50040280054a8940140100e07c45c0c250400d5007040802444541c1a0301503580b91400188000550500414004840030311000c9940402d04d2900d402000e0070150040324550301e0020a03002c407480c0c034540684140124540d106001048019110701050b900c801200c8407900d50b0f2415954413800c480c5c407110100c402e0008600c980042d40642d0600b0803407142c800d00c004040e22165100c0c0f00001d86450502c1d90700b41e810b03522185400e0400380d0240f0074100e220781d090030030805851030400000ea40f4400240141c0030503441e0f85 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 291829118 1250 291827868 291827881
    0x150112170d18060605030d050414150706050f0a0e0307050d0f03140f27060a0c0e030129030f0c1e0d031701061d01082208130806130605 60
    0x18050403000350704002c1852512014108040541028041c0500c2800380c00140f40d80d1500610480301100c8000c1c0c442c10b010050a02004030045142a51000b0200c04200d2403000278418821688115000041903e240c10540d1518040340e910040041c8281e00400c8802d002c00c100191400782400d40b4904001d503000140800c4000c1c00070300030383c08507007400700d021302c040c0d107544842c59482895140605040482840c0d40158003680c0541d003407025400c40c0300410121980f0340c005280715141400c00406404082c0f0210b402c480e418811100c000030422031b0385180240c0c0c0040542c030140c045000308010b440c40107c0903201e03042d02e00841e200ea001440d070505800386880c0c0c01000c00d0002032000c0705500c21402d010340891826100d648045400c0d100220303ca6010b060b02c00c0307104030350b0002d0200d04001e88006455840010f460080c541483d49003400c84005004040c0c0c08480c81201c24507201c00a450b210795401c10b031608020996046001000b0815030140100701500360800c0c80030cd49501c590 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 291830368 1250 291829118 291829121
    0x304020906221e0b0913050102070b09010f0e030a0504090b0d050102030405061f0b040603050403110303010b0c100908091003020d0f1407090b0f2505150112170d 71
    0x140d940036880c16800110107a008640c800c8a44851107a903034624081400300050440d0419480564045c0e4544081010001900b151142c80ca2052000504e81110760b295440c842100b1580c0c2da15680d11000b4000300c00002d0700651b00e134000404015410450044805800c43c029401020b480940c2d81ca02c44505a84070740d00c1c042d01c581c012000315540d08090800c41e45a00d0111942d034484428010301d0b61884154240020840340000c20301401c090521a08401810001d0003d60820030607c5803d0000c40091000354003c000c2d603503620340d644c001421610b0030510440307e64040c00745000a40d00c08241c0c000e0403030300b210170101e5460200e036102d03e006500034016240d1802c5a6882c0c8541700c010608680d00c4102401c49003080c07440c05035603030340b421203040b180b50054001d1004140448903a81400c2d201610900c00a0240c441c4085910800d1503600901d031603080d50b407988405e00300c5000004d050107440c09000d40e40301c5030100001a4072041041079049241c800589400a44040000400d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 291831618 1250 291830368 291830389
    0x1080c04240332030f09270603070b09030d0f0909050703090b01080a02010e0112180b0a06210b04060b0d0b0601082412031605060f01050103060b0304020906 69
    0x354450801c91946a0604808146040000f40012005200210500006454044115031000005518010b90344007010440d82040a000f0f030000380484c089603804200b00c1550040408203046a80e541ca00b91040500d0304a031648030607008031040250540c50380f004201510069a5030030304d020803c034510022641c09620303031302c1010f00c03919100900c40d4213941604120f02ca240503044960b090707620f640e1706031f444e0b030880d21000f4003040c4140280c2c11194086d00c050342e030130542e25000003451001950400d00a055040040b50030328101820001e66200034031441028004040c51029103c00d84031030151012883c40021705010a003000180030081e250f0050b006021002d010440d81c00e044c3d19007042801c205403a66400305020b80d001500e82d201d25501e2143c0701e0721014103c480300c8208002c0c0504402d941d20108250702080040719180380c5c0d58540722561b18482e0f8014404e51420b000841c904144c1a00030504050615008110f00640b41040e260001d8040340d00341d040e500c40742e0019101990 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 291832868 1250 291831618 291831671
    0x21503100e0106030b0102010f020f0d110d0207050307050d020604081b0316120306090506010c0b2703070c050a050907030b0d12021f0203060a0e040501110d0506030c03010501080c04 80
    0xa1401c0003180e003a6040d00000350071102a0000d0282c0c030303210001c40c002ea0080c1d031406010580c041c0403400c0e08414a4000c020800c0c2e06003050f03031034424490560802e03a8071044040d603555100041d90400c04c141008034004002241c0b0280c401400c00b0b40e03585100f486401280c8808030031814100c00c581c2001c0c0211008081c0e003a44886080340d80d071904446c20040e818242000c00e10f46030002402010500409100b450140d684040120055031014110390300a0075000c482841307030341d45c03180c0400c10192022209214400075921080740d0316000180e05c280740c10441c0200145130040269484100710aa080039943c02c0214050700020089410701e9410500641055040d4503001100c41d004100013803410102200944000103030805501644000d44d4995004481d444042103408503041d54141c1040c807520000c5688036040400a0281d04003007400300049030386c0c1050001c00e01e400c00c10507a480606900900040d80760101194450088061319802181c07500d9520016071001c4980303403034100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 291834118 1250 291832868 291832889
    0x1a091c061803210608030a03110903100506090c0a02030d0203040f020d0b0901060906030f020f0307030803100e010602060906071107180509010b011e0c06140f19020702150310 77
    0x4005050080000305540001d00c0c0c1402c0400d96a40142020300a65050b20505c20085103032011100c0c00300d004080d4a07210349050075042c0000320541d81d0074070561840c44149003000c17801d801c01c4010800403481c0034015181801e0200469442e480d00807090302e4400600c0c040060f2656554201031406804141009510001180f034203010420030203580d501411080d802040606d40715100d4004640e40c601014003810700340100e00b4011f240030700100c1006000a030039142c013180e41c0d55a0b0143e90b001950000f25a00d4185004d1013100c615250ba10700500040c0f005100030705100c41440d0300d405001d000c4004000841c0340e01105e01008020141c0200840300c0139146035600c0b07400388402010241c49120495081c600101320961190120084156100001030541c1da402502030f141d011026204684035500d42d140e00b0421080b17454281d12490150f0020001c600e4660040e400d680854500e1708402481444044050780b60564001c140c45150000d2590380d80780c10001402403542940640c4080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 291835368 1250 291834118 291834161
    0x1120c080a0b0411030a020306060409110613061d130f060b120f0705031017212208070b030a0b0d120207081b010c26041a091c06 57
    0x10000304502c074411405451090303000028101019129102d1040c0694903a00020206e2028a843da10446040d8420050301c0020121007011131541c0e0442c20310f21030303121300f0144208101341d0419516070645043d1904019071800103000280c00305c0300b20032020191780d40c5030a035400d9040c881c5d1084001e04020300c5642d4480031039441e0011a0002121070050300301e018004110541c0c050701c292800b90201980c404401d50804844280000c110301d405921485a80d10a414444a010224010904003441141c0d10448900c40341504a440300107240307180c26003c1c0030048440d0100d6900182c910400c401036590711104040c03c0585090182c0c10741c4100030784140d00400c01d0600440010700241e03004d4032000399031070000d23540315507100a1000b220301100c4141d5140790b11070028402e62034072a80e604000204038100001c081c2e0055803d5000d00f07040041c09020501c501a40c3c2c6d061103201d000d2075854030003880c0c0424100f4503514020000e0030180c07807001c01007080c680c0102000242003415003500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 291836618 1250 291835368 291835373
    0xa030c0c05070f08011407020309120106120f120e010210020a12110406090b0708041205030c060907080c060403150c1b0602040603051e060105090303120a020d1b020601120c080a 78
    0x40326054483c0804c2c035860002d00c0700c1c0c41000e50104074420000c40d00514100b64441e4140406c13480c038511a54455543d56502048202c9403042c850310450203400201d4885200b0f281000a0800c0022044240482e561400a09070303800205500c04501040c005600c81a054100307484481070800d01019150a2604c0500c035180b0542c068070840d1026511591010780e43c0c50307400001d118000000e046020100010300c5800c05141c14406142d214204582c5400001559541088000c1c1c68400250300080f1080000701030030800c0030050310080320924a0b0924682c0e40c4c104402c20301c0c603800b489036103c0c0c800400244c0118198100541c40340216110994a894620000d50144c007844001c01c0c03405022581c600c100040890001101d40044030b03c0d519a038006441a0b005982e05540c184003c010020b010f444161507280200686407004da12001514403603802d0343e5181d0206010100410174540c4407a60020381c060446415246548040c00c5905281a0401203600b24072914481e10000404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 291837868 1250 291836618 291836639
    0xb030105041209122604121104111204061a0312121305030306010c051608010b0f12060114010302041d101e05060306040204090606260c0a030c0c0507 66
    0x42c284001c0e41d5040000d6103491840f05990b600250140a0f1203a071000b40342c50b814010307500040d41c1680d01206041030b580740c081c00402801020304031045811100c40d61102e041500401405c8522030a9407800d1603202d001d0a00507400040000c1e2080b40c0f1060034440d491003401c02071440d40405000e585032803a0300d490030349050f400200d00c000040e00e40030001d55000d81034100f60a074164020059860f5484d42801198201f100c0078044da4240901c146404000d804941e440c402001c8140011a5402c0705d0401c1016013000518214040c0c251201c06002080d8085902815140c00c864084070510f04a00101e0090085070000c0c69141800c01c2c200310b480700c16a07942071142030000c48000c1603035215251901503c80e41000565503200780300c0706100138076258001e075a1001c400b6000500301a610301c82030054882651041020480e040c0f084e07500341c144105040380d0111a250504c400d400d1080100100340700f030708020000c1554590881c00c1441c89000541030194201c0100c808043e15440c801c503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 291839118 1250 291837868 291837893
    0x14070b03040302060609070e04050403170a0906050a0e061b040801020304200a0b031b1306080603120306090f090a050607030b1306051c08040b0316080609060a0512010b03010504 78
    0x50244c494a80056114608010b0042c420903040c0e990f0540c25030700c8404d00024080180046042c44500f0a0240c080e400b40c1d00100d02c607000c0154003240008860503e1303422154040e1a20081d14200450403441030720001d400c0c1d4010b0095a1074954909152107141d007a400341d034000f2601540008140b10620003c5d2002410110800d07070740040c085109020040b00c440e00f031103201d05240003440050288220513400e82c200b4040c0450452034185040040501d035159a045040402d0040b814047d090030104282c4000e5440304107024a1404c0843c0040e40e110130081500d00c0d1840210001a14a501448540104d03540103084801c81d0600d00300c0940540504a00f5502030000160340c41b09900090150300115203002e011058000340d030300e00c59540421404800d0760151410400042d01080042c0218401c00c030b081244803031034a10360381c01814400041e10140c030803100322060202030f0f500e8040600c11034208075512540da020503440c0701c0c05401d00401c9507903d9403800c01004180a0380c0d0308000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 291840368 1250 291839118 291839123
    0x604030201050123090a0c0905060f130e04241404030809060606040605041203051e0a030b040501060e100201150e06090106080723250213050112060914070b0304 71
    0x492120501c901c421610440c005a403003017000001c220340400c81ea11031010000903190056034161120080ac2965006031000140a00009404203121710200c144002514884034800001d0809840d20342164400e01096071184018200514481c0400d5201d0420f580c24442c031b0902c03e16041c10081c1078290202c031000485c1c02208002030300c1e0b00e040000c9405546040e114141000d084ca00744214114040c801202030000401810004242a21031003003040810300040d90343d01403803600101542c021001050185080c10300510007aa0001000c20301d0110981f00c0b44040c80c6200c00c02c03030141c010b403815500ea0011040c8003145481d0a54400b40c031519058421110a903611081140d42034070440c0c0c094001140552600b032004600c1c00114141050f54030424180070002441d034680c1a001c40b920221240001c0c071000c110b0500451001109501e980708224030341c54000b00d0640e0011040008003096600d1502500300980314122003002900c150449100320307190b801c6481d45500c2980c09 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 291841618 1250 291840368 291840389
    0xf0e06010e030c100c1103150106020c040c0507020f010905040e07050414091203070c0b1311030106030302030a1412090d08091b0603090102190518030c06070f020307030506040302010501 82
    0x10760005040000d00800c029402a00c112030a20922501301e40d042c007000d004854110407004041d007540e0341004075079800c404060324070700c05500d00034000c0d251104989005000703604141d0000100c0da0060300707554082d601944c403d00d441c04440012100840c0582080394004d00c1c15400d0b1954a1001174184107a85080c1d6003005160790070300d07850154202c01ca5040071a0340c043e80040c0700d2420a880515041600d90400003000c80c032554901c03604100403140c01c1c0301c0803a07202c00c02003400001100508446400d4000300211815520300940b644541c18080c0140f0a004030340e85c00c0c40c2c4225003180d001c00d0707400c10302c2c4460b4208100607944900042c0d4590700000e220b00081908058081000d8454400034110540440588828020349400003042c0f0f05007550b0a20000030903188114540503041d599540e1190340c3e07425041c4a030881c11050740044e01a501403441c07408103840d03c1c1c045405483d007101c030b142501c2c40b45100103881d001c0d042d080240940283d406000800d601500058140c6400068 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 291842868 1250 291841618 291841637
    0xa120e030433030b0d060e060f0a0c0801060f0903050105090d03060e280f0e0706020706030e0721050a0c0f1202010804060b0321040306140412080705040f0e0601 71
    0xb058008000720b241c546203920404482940c40d03074000c0c0d0065403400000390284074513035103984908048132036072a144031140d001002000803071505900f200e5448080c0d40e200f044001c03155240100300700e205008035030501c2800010303a83c025005901c400300843d4810003d1200d803804500c0e0f1038665612a2804000c00d0501c6408591529840c002a109104181074a030f8900a4910320340b44031f90362019030000150b50790307201d101c0d910898000e4a102842c3c07a00184106480c0c610028a402807a40c4a0010140b9003c1c80102040340442c1c060304131600800a154282103000090030b200102c1d800c020818030680320f101007042950324801007110325880d1081c0c0a00c0c2ea95a00a032001c042e080028009000c880000d40001d090341c1c4808a0008090200e85001150440d02c4142089030301c9440290400071504100300456030090142c0d02844040000c4031b03091958405d00b4848042c02502e081c0312615001490390361084098030002c2920a2454041c030b584c0b550f640c3c646080680740e0714002202d012 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 291844118 1250 291842868 291842909
    0x19080102211503030a03020306011e02060402090a06080c0d02060f1207030f020310031e0b070302070b100f12030e0303030103060606030e0604080933030f07020a170a120e0304 77
    0x1c0c0b14106920050041c529268409400300d009501c018215414014508030501c5500390786604a41407880c5900106a0703420a40100f040c0c000b03005040c40200741c20020309004088010864400c0d400c0c0540712040c52208900c0000d01900440f941507a0b81c200101e1512081c010520900380500b1094030b0800c8280c49440c01d0405a100c01c9401e10604211113008000117103013410b102c000841b41c11280f421071246a9600d0204820903911100066000b1030940d05115103008400e8100701c0b10041c6030026850320321078200e81d4995124414000d5020a80003083c5801385418881e4000c0040540756a03684034980400242401d001700c000092521110300c1c907018002403402c4c000ca804c460b6032414080c10104009015540300d0300e40d0f03451501c0c54070214032210f2002400540d55140c000301a12460301c0000d41c144a40700502c4202190301ca203c50b440400c190021000d01c10040f0410035030b4030154440103581c04d202e4a40041c0c5100e151a61614410902102070016541800200c690842040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 291845368 1250 291844118 291844141
    0x50a09030f021c0c0318030c06030e0a0f08090607050f1509031305040e030d0204030609110d030507080304020a120b01140102030403050705040504050111030103050c04110a0507021908010221 84
    0x3811842e580c8440f42c3c00501c08140036440741100342c0e10910b040c48002080203200c00b00d0b03445907031048032054010303d401d0020503014044c2500c2c80d0600c0006001c2c00c20170b512040301e0000c6100b0090300341040010f00c080107468030801c41c0ea0f0396821504603038404080c9005d8070743d1042d0500700e080c10780798048e01252200c0b03404000c803900020a00c00c2170078510708090401c0700408119134105414481085401c00040705030001c2c10003140036440006450000781415045210202106849a0040c41d45680042c0d00041540c2c5400d4006d80348907101c0ea190310102d15000300a81042c82e280c0f0380205600104422000e681e416503259604590580b01d0907001680c1e28011800010903d4000040c18001400d140c0d1106501034042d10011400702d4480a268007280d00a070001e4880f0381107240040014141405441e0080c0f6900d00076516058403080000d25500542200a11801c442d05ca12203894000c001054060040d00008540c4c031201030302030409170700700d2090212000400900042d51203005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 291846618 1250 291845368 291845383
    0x8160b060d05060f06040e1917070309060309080d060806100801050105010f180905270606090103151b05180906090712061d0405010525050913050a09030f02 69
    0x1c1001072003c0c2d10344010b10000b10400070303caa50002d640b60003040ba642010002c3d101d102d20b070001b40541007100303810070b40010045018002c4c070401082005200203680450340300d0440b280c5203030000310050245440d0b40e8910600c040c610002d0705100b00400d103a90003142081c000c82c1da034000395920a5541c000380b826640240f1400740460300040e0011002070243d20b082900c1c03041c4041040c451038035840a001151000c0e600c1c890144000c905060f4584d003240c10301000f5407081c400601c0329240050018202c401c0501004042030b034020102c006246403a0072003418403c0ea0002500c0b8200d400f6002080707038012142c0e4041d00c3c030b000310302d461080c10a01d04490042c2720180005419644114099480c000080000818580c0d1020001680260814034507030480329102c41405d142000d040c25800d442002d40380440113804580c43d50002e07503009040030010301260070440d440b1028480014642840ba10803042d04509103010010700c441c2640c805500144030b522500d070812103c440407a0788544 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 291847868 1250 291846618 291846623
    0x60c080f1207180503101e0c020303010f08010605030d0c0f151e060338010915080610050f04140a0f05070507030207120f06020c06010f090c050301050907050708160b060d 75
    0x440203c2e00902129080600c0c40340e1f00400d07482c5d10014524000d0110380c140785a50b00140c001000511a0b011018446c5e001842d048009004032400c0500080d110000f6030301e00000d01000e11044400c0213054014003401c0e40d0400b0000c1c1e1262200105c002c00b400e550b0410740c020100042d03000c0200d1a45120b0310083e0703a000044c54030f80540d085054140348440300103d000340c0603541400b10041008403182800b81c030410340f02113041d01d5040c4c1c0360400081107030403101050b00202e0800c211030507803a002703c2c2182d40481c0c1c0140c52412510201d0011b0180c003000c0c41c0d05c81e0f02c4104208450301c1c5600401505500d02c0010480360343c03104811542801503140080040e080080c04000040d03004083e20f01150044c0c40351014a90740756580c3d4200d0344100c22240c800d802040c0104448454900c030030000385900319050140707800208009040744014012a8499103550000c601114420b4081d00c0b429540992110390f10015040d80400d4030303940d40710486008074490001001410202000c1200c1d6a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 291849118 1250 291847868 291847873
    0xb030307030c0f051c110601092a05091915081312360f060c14010b060a1d1804061805300301030c060c080f1207180503 53
    0x10403560703a4458210342018265813034841d5505921400400e8842c8004181d05620b4100c0301d0f445200e0020306102059000c108428503011161800500102028214009100e218901141036110598150254a1600f508003125a56004114103c0780009041d00c00d400c030b442070755184450040b180084100c8200101d0324202040034001074282140c10700e86111410710800c030b0341504041c00c12a004504441c02c1c9a140340d070101c1c0c2c80ca4010000d00c00036002901130703614201d060602c0a007025076002d10040c000c80c81d42141a50b00c0b4420b5000220006004000b81d613501e403140001450001d03100a0001c9010f400e045480d80c914180444282c1c410000c40c000b8441c1d0f86035261718008282007107040010f02501c590000005409103c48000015000c500120001140301d11100360f21607100c405040200800047c0701040c0740c400e003141180c1c500c4c41e000500d4140e518044486024000040700c2c98407011809031140d4454852085c80b90004c0d42ea82504490b984040042d00b00385403242c02d0701074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 291850368 1250 291849118 291849137
    0x1a071b0b04060c15020f030f060103060620010603050609011401080105010302010f030b010e09011509080c0319081204080a0e030a0b0705030a06030c12050606030f0d0507020a0b0a08010302040b03030703 89
    0x307401490f04208580c0901c0c2c90b08642d04042d64514103983c0640c2e0401d038034500000422a4030707281a0521500144203103000c03c0100e042c00f80c05061422101038903241050a42076440c807001c030942140011395030180544685062400809020740340591003110080c0c80f600c0081400b002c14418030741201d070140e41e0000107110030081500140040c0410340d0400031421000039150b200d40324664002c1001e0307048179170000b00151008003841d91540021083c1d0704000c038940840d0360005488a207080c50480e11100345089454280340621984513900c07066400c0c1d8040100b4004440080e08092106840e04017148008a007010707140c80200e00b006200584840c08200418410300285611184da074000280302d60312a22550b1b6465015401200104d547c0c6c0052000c2140c184405600320304182d00421451815144c005d1322001240c0c1198200034010030030206564442540c00020490703c40c0c0107030303a070310f20801c02008004240000c1e40900e08202c04c03d20307a82000421140050b4043c0e0b1400c440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 291851618 1250 291850368 291850379
    0x1303020a14030c01170f100b03070f020d031416020f0d030501060e0a270605040905031314060f18091f080601060912050f01021908010f030b06040b0a1a071b0b04 71
    0x2c00c0c0c0f019100c8940e0b500408008a2388403100c000550003040d40c0d803164010711580c0ca000030704d404084140c1d1000c041c1000516a0f03581e01201e01b80350400d0004e0171840707c0c070070780160491414154198550107481446606189142c0643c08103050f0381d880d681d480003042c08181480b8611020f4403a98004000e05200c034095403114a0224181061415000c21a40c2ea43c05c002801c5c1d50741103206840e2508000b41203515000c83c06414002000b6200c4924581482000014103a00541480c80305031080050002c000140204e05140c00a800030008040e50402c404404c2262424140380000743d01072603004a5544c200080c1d0300d04031806566142d07806420311041300d40400010008581c00e2041600c8528210340c280050620403c0304118540c1c600180f090041124006910545020007004818000304540075010313070b032103082070b60b010400050990118641c42c5c01944016401d08407840c0000350030048800403c20395025025011823546140d4184038410307024491a0003a500c104410002e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 291852868 1250 291851618 291851641
    0xb0603060d1101110f0106061d0f010f020c04060308030a240909020a080111091e01020712020f030105150411040e041121100c11121303020a14030c0117 67
    0xc031541e062501c00c4c04d03001c40c584510720b000c018215080c5265110301050114981c004000303040b2400c0300040c00502c0241001280d408000d600305207042007504d000b030940d824020040c07c2e02da0140500204411992401c01800711340080d10521142030510881c85074003082641c0a200106c1000805070f4042e2500301440001d203e001d400b00e03001410310900040e14642031080704081902d80780d2179592281300c182088101000802030a010078228078000b4080d036400900d04046d42d19180c3c000508405600024441180c1500459899800c020820540e0f60b82002ea800106070290f4003803004500648688007280124080c84407580803c41c0024049088101d101000140160010040007000e628005110b007200154190399030085001010840d00c904c100150b0ba005440c004281021203011300f03803a424240707102190f01e90702080743c00c500028881500b0003103500400604143d5920307802018480a010802807290240400c0400076502888250030604010300c090f600348d641303201650b00e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 291854118 1250 291852868 291852893
    0xe010e0907120213090905032107020d141b0a1209080a2d050a030e061206040e1f051005031230040302030d0e031608070807021908010b0603060d 64
    0x5a4581d04d003070000e140c91543c8100542580100b0280d0342d508179020503a80b00201740c1c00000c43c80c9040204200c101580420094120281450008500488480c0c541001e0099011130610741385610b01c5403449990004441c1c40c501e00c20f00002c45121710000c01555118610704c00c0c1e400503005040c1d0350300061103a803070b45c034500c15403140e4152201c10032026803541b808c0e07104170440d2071f0f500a1100606041c0c1084040e900342c032080b035138140b41102030804525000d01c050280d500443d01e451303c1c0a00d4a00601059848030313060042c51702440d004103020005000283c803044004060316034003180900340400c0b400c1c241c01c0329008461420b0841c4101000740d82c20f1195204041c90b80b40701c05002040d00c0300500340514060350055440303503030300b09c26401182c4040e50101c0070782c0c0c805c004541084980c808a50360309070b00a0b05c103c0d100c0815040c03002c0c0f24892280025480b1345085040c618070020103054200f40e440400003045041e501005210319440283e039840da20241ca00d4152000803441305080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 291855368 1250 291854118 291854137
    0x40507020a080c160807061409100e030c041b03061205070e19020307030c1b030818030c060a050121020303090d0204090c09020a1b020d0308041e030e010e09071202 72
    0x450304260013560f03800c02c0700c1954003c14901d03048054100071081d8800d407070316502910112801c0c9020003210000d11040400c051840c1070002050422065035002d1286c03101004016009212100828080c035800c46082040f00b00801d24010000c522941e582c0781c122052a84500203141041c100758040f28280c40040001c0b615400d10503840d11140d005001950055406890200c1c080172400d801030071a1070325003441c05080900e20840c00109501c03a44013500200790b20030464506507020002030075031146a06502c000d10407403040c0f2241c1016540041d041301e807412907841003821001243e1007103510001c00a9859401400b54507a580340807000c903040644001c1000599850703a0760740484000803580301c03c50140e030210303078904115040310f14000a8280780560300303458411680025488801c0d10405410821601c0010301000f0300303502c00c0720405144054281030200549030041589400801482c0011045500d0b13090a05000300d517180155541d440742c00b54960301100c00002504101c0f0907 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 291856618 1250 291855368 291855373
    0xc040e090304030f061a060c0604080306030a051b10050f0d1d0105130204061406040e090708061003292406120603010615120c03090c0b0c060105040507020a080c 71
    0x20020f103d204c0714000c007a1107113101041319008600b00c0b6510048002d95180143d1041010150310003002c40c240d5489644180d5840d140d03201c0502280c030782003500000501700d12078100384120b01401404504058281218100000c4880f820215940c1c00354114605404205204114000310345800c26000c281e50f10717640e0190160130140090a40e401075860900c00c40d1100c0a04c002d500b0035024400183c1411b500715805154040d010920301e105600c82d0616841c2d048000c03820490007840520000c000c150219502c5040c200074500614645101c00c40e0368140800701e8640c0aa55100b040302c0442603040001815079881450f682c2001720406400c020140c002d074052425030740c9101900c08005940450005841c121050500311a0943c0100d00506980141090040d9100400071040540030b2004504059951000e0b00a007200d9500188150350b540da0100d85941c00e0b5000d82401d04d641411240f4a0340d84000384402c4075404d503400740040e000320b41c020380462411001402007c40340340c00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 291857868 1250 291856618 291856627
    0x1802040f1d0106270306050714090a0e100b0a09140901030c05090702010f020408030d0f060305030f13050402210a0e0c0d050c0a24090b0d0513051f0c080c040e0903 72
    0x2540319604c40c0c550822149141e0b90401e1000e081e601081a04186007070520191400c03001100040041110707106144c0d1002c03c032000150341210f020b482e600204075400c030320781d15115420406030654010380280001b010340f00e91403400380c1c9418070f0042e049a03008010780460314100300910052450052040e000e42d134070340e80c0803c01300342c061005100801691020b152a00300e1110001c081d03032000084500310600303041d81030000c5000031048500b400031081c117596803040c000d8170010a0031031641c80203500910114007400c071180303090610750f070300f0490001c8d61445956001d1904100c51030080150714036800f001c0200341c0c6090203811240380f54042e0044499a1a04c48000f0b40601000d81140c14444c00301081d2544000703103811105410500c1e420000a0300341803801e086828040c0440011515803200041448880e0340c400401c0c50a4100d810384051111070414026030204000110180c0d9141c249264011841620741038090b0b4601a5800e00d003d19142d00160400005031040c0e405001c00c11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 291859118 1250 291857868 291857927
    0xb040b280e13090c090c210b120102030403090e06030129010201050705120a0b060d050403170603070302060d0c020708030301030501050114060304030f1101061802040f1d0106 77
    0x2441024145095903110034031510941031000207903030380b801e00540c18140600c400020b10403070940f1040e107054800c00180030f0b6240d042294406070298481d14100401c0303121030404150364114039038005040c3c03003401c240403281240c40c1c201d2000300ca0103800100064420300c0f81015102071550407000c001e001203030f4800d031701c480c049140c2d052a900d501c0c0c800b2130044046840d60203019040c0d200310a400d0850400f10200140300c0e249000030002c0850a0b034070409010349035201425940c0072201c80c041004949000c1c60040d00300d429010b000e282a80c50400000c0d4980b50004244003601c0c0c0c0901060b0411700700c00c045074041c111280043d0158058514040350300da608001642c000c0d80200008100c1d540b408010070b0401c011020101c1c0100e41c10010400441d420000e107225484040c54104091583d4442e40c1d0300501c00e98000441d1110204400803421100c1e8003d4404d503a5061081280c0d140e0302c100d41c24040c1c600c0b01c500780c0c62800005c0100910790140000a00401c003a8070680b04001404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 291860368 1250 291859118 291859177
    0x80303060409060e030c0616030b0a060c020301090b0c090102010f060621020f0c0d0e100503130501060f0f06030f020403110603040302070801050c12060315011403030c0a0305071b0b040b 82
    0x3020000361543c400001c000086a00c0d48001180500ca42000c02407002b240717010811808050140909000c07100d201402103480940c40300c002a6080203000030581003442d84a506036020702c040d24015030030107005130b019240728032488080304c50946881c2c440c0c8000d421602d8030000e04c11401240194288181c2c0342000400c00240344045000b1702801c6924114900a0810038101459501a1a4a116582c81c0541080441360410703610707944203240c0d26451800030302419040e04074031414141c4c100005a2203e408400c9001d44105840c14070580c1040c4400b88100c0c01b46200c01740126450090180c038a051135401160400d010b4415240c60030f88800c4e00601b95801510091401000003500c01c80020b80070a07906e4200070210094804407168480c0c16010460600412503003820000fa05066a5070030800c889032003101c20103444100c83e1504000c2c05a0b0800b51043e9a030b02d0303420109000c0143c810400c2015984022102d50405040441c10380154006a00740030303a8008586d5401d00034200c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 291861618 1250 291860368 291860377
    0x160201021204060b130504020a0b0c010e01060b1309051302040c12090b19020a020606060d060f0b030414030c030708163002030a02031905130b0a0305010609080303060409060e03 78
    0x100e0001c02d42207070b540180405c41144030013400e042031070318083c440141c2d504c690813401c449000700300ba922211460034842c01000d000c818240d1540c071304100001c0c15030b46440586015075103202c0b4a5003460b80c8030070b5607065550498021290389a501c1c03a031001460554000044800030380b034810809414103114608a40203e103050b282166164100200310703c145890111140701d941f03041d824140340c00c40195079000003a001d1031154402280c00c000d203c05680c090001009c041c24900d14441d50b030000e428641d0700503107050b548a040c0596640090800008a8a46070341440040d413030700d203042c5c50b10181c0c0d03001143c80628940c040480a804503410942000c0440c00001ca0344c00c0c48400900440d003002413005085007550414005045055008010358030300001c80c0c03040141003022032400b1286803107624a0402241318100000c240c1407082005000c0807c400e490820003662181401d03520304091f0b100307034107159200b0400160142459041030010511502020600b04e01564407d41190003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 291862868 1250 291861618 291861623
    0x60c3c1303020a09021615020c0a0609050706020715050307210e0c09010b071b0306110c0c01022a0a03140c010e04050103110d0f050303012408010e160201021204 71
    0x50301005000750315000d07801d50010100040110318120b40d80640351080041c001016100825200305680700700040e4040750011903040d42914601c003034528015000b01410032050b031712881444000b15404d03000003841d0f0180c0342e40c1040d519042120400498441e4001895003042000141c0354a0941c29007500c40040148001030214481c0552055646809800e444c400d1041c2c01c0c21004018080c0504200c403441a048040205c03c00e14641c1c0411244078241c2c001082c0a01c0c10501390f000080b0074020700030080e004000d4030310304240c3c0b40c01240c2d152514009455040103212200c81846040f02410395620701c0600340d40ea00503034030303200c4a506060b41c0156040e550060000240d1941e0701441003664101c0840d0104003650554941851180d00521a503005510003c104424800403503064403000b0340c414226503070707580c482047d04104d503400010f07040146400c50b104c0100da4010b00709241070741d14102c1801041c0e9504840b045400483d2032403981995400c01a00f0458001d840e8110710490 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 291864118 1250 291862868 291862897
    0x60518041a160e04060e0403080103050d02010209060906070201030912020706090b130b074716030b06040e0103120206060d08180f0301020705010509060c3c 69
    0x585070411001028450458a000c84003100030400341414a884805101c081d900e807000040d8100300104005043c0c54000d000070f000c0c18403c01080592140149058910800030b9808030742003071800b81d00b40c0c002d40315403d03070007481130180704c0d086e041050150448600524022508850b00d40b101e03010981c0384010b810040c0c1001070103011603500500844000c00c14006040c1c5440b65841144020001c140107041e4005000182c03102170020034031024600421514112004030400c291600c42c0046810043d1000e451070041100c0c000301403445180704000b1802c2d490a0540e50100032002000c011406c036a2210301404086400d03000d10520318061442606034281002481030041d152040081803a407041d01120056000070b82100c0a5038030305003030001140c0791803607003e000818031902e1460441e0150310110b1201c091203015040039004820b0381c5d042c0e601c0d54a42e0a070504a42c8074034003a80480c08034010f607080e000c1d00c0e401243e9061049904046002c0401c1074101000c5904c6291101c030450b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 291865368 1250 291864118 291864121
    0x4020a150e03160303170901021921060e0402090912070302030d0608060402150d1e0516050c19140102031003050601080706210b03010608030a09150203040302060d060518 75
    0x2030504010050f819001c2d50074904001e031860354001c00e10464965014001400c81c2c000c100c003150300350181d42c207105001a1500c045402e105004150f0402040d00504200d500040351000122500c60310055079414680d641c011307600c2d034090210741c400c080c00c9800148600c0901404181040b009400e001e442980999551500200325200361400c3d40c01c00741e0706401c0302c41480700503581e481418403c8c0d200041004d03220072104040d08000d002e41a4034103c64001d41e55040001c1d04103a1106108140c00402842010700109084419000e00d0741c4000c0a988840f1a000d298003010800c24201c41c8a1000340b5070306416030480e242680c01c2a183e080380c40d40303201d9007801000818007800e030141c10b003080101001c03840c21500a20001d540c01d40310b01d80d108070106002e600300403504442040c86001d402807102c10b070381c2c1640569941c49202800005603508a011030315030041c1d44000c0407040f1650085082ca030568080004580c003480211195035500c1c0340c00a03140e160040551003009540b4180c1c1c105 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 291866618 1250 291865368 291865397
    0xd09060b030715110c0306010b072a0b0d06091104060909090b060f18010b040501020c0307031104050c0d0e06060103050a020901080705160512180a08060105040504020a15 75
    0x564880400e4140700e608295424402d96041d10784884818040d03207480c0014080d1128658181241880c0103a018002ca40c000700c0c004041c03e004044c1c3c14850207014944241c1e10942c41810303078040d4001e0804c02245c0302c04000360410080508441c01d60518001032055480ea0b070700b422500d40c0741e41100d0214000c602008242e80041c0320b100149040d050500c2140700c950f440307000c2108000d00413849091080c00035511512035032001041101480030007085540c42d221503001039045032141034018420401c942c02c45c0e0801007260401c90703901c45588142c610f4040100405403000402e20300b4a18002d100c500418400c50280c440b40c080d203100a84114108080010181c3c0d200604040f403072401001141810390740200943d0b80714000c0d03c1d10903110350102da8400540041828054400d1050300320307022460302d26900070060035049a02401c11014a4070621200c01f02c00e00c03c42d10641c0000004001a042907080b0b16405440200320282075621808940c6010429500c072100058500c002c088a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 291867868 1250 291866618 291866621
    0x31003030f080705040b0d09060c08012c19090f03030203040303050c0909070c0206090a08072c073009030e060f07020103020f070b011502100203070f0509150d0906 72
    0x1d0201103072800e003101c0d2900d00340c00b07469849148101a08180001b601204200303007584800034140e03000d00705101540315210000c15a040030b0040700d00b80d0407840390902c13001c40d07010701c0e4000f40030f00403e4000075665041221950784400c0503a521243e40c650740321000207141e107040c5c21201c43c03090302c0050b268141410000c04503031008216040203401042034450641c1e851141650004003440c0241d40c000d0b0500c04910301303005101a681d0000f10460011400d07040229030346084ea050045520040d1024105000300c05100c0b240046030003d0080204081c3c91041c401c4240c4410301d018030405406400c0c58841400103411070300c0c10115500c040303140806a202926820041d41214010b040c01d045455801403403144210007414141d00241c0b12540006201c180d8080c9038010b2590005903035101480c02303501c44800c90845c0180611428000082c4040c0300703690007400291756040344180300000680301c55001c0c1e81c003070754485c40b02c0300e8940400c04007000502404500c0e080104540a05240440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 291869118 1250 291867868 291867887
    0x40e011808030103031e05161a0a0b040506040b010c0b18030403030824030303150409060501060309050f1b061606060602010f1d10022a030a080106030c02060f190203100303 76
    0x1c1d24600c546c0140c0e41c50303448070a40781c20440000c0544402c007100e1504844016203081c001020014003400c001c10411581d003c2001c5140a85091080c1d584203010881112983d12001d03020442d076441d001d010036008000c40c0d5008040078a09085403451710304103440d540141d80200d000a400340100045212100324030180b401002c07140341e8055100ca40040e0f22800014003d075200501560700980344e07039440d0880800b8640055040205503150307203004024006801c02034a80d441403114440451600144098100012240d04040710900e4410000c8550000d4400d8101c10010000c401c042016485590020070301c580001580400103000041581d030b4008440036142c0c10080712220b1007002141080040b0b0303107004016038403003600384900300901001d03010519144140035000f41802000000781985420b684800d249aa642c60382103003503c80e1000a04010703002007002c50080e80c1907121440d00003500c04503405e060b8828211400480c2c000721823050207082060002c00034550400d800f40e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 291870368 1250 291869118 291869147
    0x30c020a0f030f0905040e0102090a0e010e131106271009290406050301030201031103040816030e030a08031801021207050c0c0a06030212150f040e01180803010303 72
    0x419201200761910060408603501c00b600b48150000700d2440c182c42102a10081c1c44003c00c10410107900014841c003e422802c1c0310f80c000c042c460408640a4116000d060480e203252964002540d2101c3c03041402251010080b28155800b20741490185e5508020f802c0c00044141c0c549c01c140001d44d40d2484091501c205c0a000e513a20003003d0205560102e003120581b0f104900006089401e0781d020038080340540c01910040101240c0400e802d03601100850481e8000d03a41888112100d00164580e44020b803402010220b003004541103a40100b41015182806401d10f400c04a81b540c000c02d0400410141c2240e80d00c0000040006450a00b100903030944861710003107080c80c4282c941424103000c0941800c0c103201021a0384800d030343d4100704500381c105000d8049140140d4420b0060083c1d0807000d08981030710b0f01500001c441426000041c00100c5000700881181e21581040c480144005400a1125525440080100048100c0b4107a40e1440340c2801d0b5560340c50b50030024814003242550 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 291871618 1250 291870368 291870373
    0x40b03060a270915050f0117011b030b010c02090703061701090f1502190c0213150902090a05030106080a020a0e0106090b031e0405161a041502150412030c02 69
    0x2056514401d40c40d000c03400c01c100706001400302c8030b50500403d480c134100400c407409410801000b20300c6080c81809412a441d80c2000d107500c3c022150030318240d5060b280080f61032264044442281d5110390071095a0017018184070041751056008194040300807a0780c03c0c0442c2d1200790407c0400d68181d2001c105003541c800070007114580741e80310100318000c0c034005004107111901c500c05982c025811210010911a1881000313480054081c0612070f4001d0260301c0b91581c0001d030300d81c403e458011030039080c0c42c1c030850f80c0f2410306209148000390850403c041d0004045400070030252424480e003400b601311440246a1440244100003402c040d68108242c00303108800104a01c0e600144103030b00f600d503246541900c9c1d640d4464000340110900581002e1080d104d0280310070b005000c1035402c5c403150340748034800300c070384d180c0000c5a520381d510306020b46e0103042003001300b00700c0795505e80c501e04031241d5105946200403072240440c610392050b18140c1d40350460743d1000e94056018442d060524095001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 291872868 1250 291871618 291871649
    0x60222050f040c1202070b0708090105040510050702010906141f030305040e04030302071b29030c07051507030509010b040501080303060f24030103060b01020a051e12040b03060a 78
    0x4254a2101d41503610300894503904105280b43c010320500c42030402c18501152110482e04064038031040540305c20780440e40b51004510f000e8018010305108a40001c02840088c40013443c1c0d40040c407005003208219562003a5110019625014038441450041288000e504000b800d03840000f80141c480c91018410001c108002a0840180d40c111a0f039004411025a5581415006072223030342e20003803546a440c002610b42c00300a460313110540b080045414030300c030f45025041c1c000416840d141e00c00e003401480040d0740d003210600106031162103981561490040d00000d50b60382c0b01c1c240d0344000481d490314200700c202c800900c240c1190240444080c0050351519980f1616484050041c0b0b005101d403035940075540d2580e071019588800040840850ec00f124882d0960f182c10a0108440081c14804007086940c8002151400d46400c003014014103840d1000a400c1c003000540b45049500a002520300485c2100004d0710050941c1c000c3c407666850407000708034440c6516041480007424400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 291874118 1250 291872868 291872879
    0x32101050906191806260607020c01020c120f12030a0c050909040807050f030f21041713050a0b0406080604060e0a0b0d060f24030515060d0609060222 66
    0x400700046403001121101c486511641c4c04000e03141d2a00250300e40c4940c0781c00c81c03a5a55250030f031241c0c8540064159009602d031150200e03101e6000e40d001130f0050380245845601890429003069440b4110070444400c410000726580c00c1c13050401e211050194040204681c070a070a0181c0f50b034050003403800030314065410300000c6159a010380040c0c44400040749a00400c9410040c80511403040000c880d01c2d03030040302c40320301c456014030550b141307800403101d03850788466581c108ca41c05594031000d01320f4444810460420140c00c002078040031140e016a00143c15140d50308840301038803e0000d80e82d07a0f14180703140034041100151400d4021403400700c0410103100100030b19604401c0c0300c04003040010f400700009144401015000d0b0a8034508880aa040c004a84c40002c640c2c01c081c510200d2802c16003c0c07901c15000e28031004e04560004641581004c55510455a02510040000c40540c840740ca6200c1200c103482c8044888035400141030f489607106600c600740d65004101c030803100304d0819 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 291875368 1250 291874118 291874159
    0xa0605130b0a1b110109090204151124070908030901021b0d080f13270c1106100602060901020c10051e13020414070f11032101050906 59
    0x2485540c46445000c02c0c60110180700341210090320b0304120000641e000c2500f48407840001204560380414180800002c91400500981e4200d4003445105a00f0140400003515210881008903105e4007134101d0010284490340800c0e5074040100c07404580d140350a100241048a20b508582c8455109010b80c0065a80c0015075030700c945140c1540d40a004000c10100d04181400342c8024000310300403030361801c441c01c0440900310390b1030b803c107a404c00c2e55a59140f0030200c20030805184404000340b01d4807401c80460b9005851409241d1404141c4101240ca5550a1803c1629903000d0a6141401003084650410039160400e203070000031407030300340782654455131030544600d8014041c2c1c4071030000300769000c0d410220000c0402d44462880ea840c107010b000c803a180141e003049200c1c17440d04402e0260100b102418900c41c0241c1e46800490181a64040c1c59035141d0f00d02c0940f092100b0032006500710383d040076403061421640c51102c040d506103820400317508401007030240509150030940c1c441c960744 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 291876618 1250 291875368 291875407
    0x7030c170f04240e0318120a03050f0d0507030b010207150e011805031e0d030b09010e040c03060219020105092b0210020712080604060e15120109060b0a0605 69
    0x3196107107a2212407901d64420b0040358040c3d04050320303050500740c840c070002c4020403e03009041040c0a480c03000004122106009502805803940030002d1380c0e0000b40940002c00c07045c601c1d040b2480c10006080d20540c1070b41ca00300c1e00c1c480041c2d00c8071181400da58041241a018103810100c2d903004004002000703003c1842a15010304100c1e0a601c0310070b801c103103004844003070304001d4151008407510011000c200203c0503040c0342c07648101c101c80e0403c680300784514500c1034001054001e8592030b15422028444001c1c00c1030792a0388025a0010008180d48004c0003a40004842d030620300c40c0c1340c0d00c0a400c440e0021700c1c0448581190801c2c440c8040401c64440328041c1c00300600b9034040701c10004a28000022180780c242910005101041c80f455007a4000411000d82e500c43d0b05540390020f00c8180d903010704c60030b0381c0100c151000c100034404140c1c0d98081c0d2200580000a0390b0400700d0034a0944041c00029170358642c0d5102e44140500300201d426001c2c04c00307400c0007031814143e006070240c2202c0303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 291877868 1250 291876618 291876623
    0xa050105011b03030905060108070302120c060a0f050c06041118130201051e03090105150f180a021c0207020f060a050a0f20010608010f06120206130e07030c170f04 72
    0x1e0801682d41014002d90002c4800c5070064111103031580c40341102c6541c0d2040f4001a881440b03090360803045540005190000c00c000540030303a04081c4ca651040d600950340301546d0f014440c0605c01403600c52002c001032481035020b19410b0100601c1d040500980e281000114080115980c0030001c440c04424010b805503079082c40c03d10b0b590402c0844003d60f6171003011131224880300000c2441002441500308500507560810200724581c1e46c4c80800c450700c041c00c0034181c0c1020b00030310212210b2400d118101e46c4040c05404c00342c60404520754054500c2c000f80c541d10020341d8040b4500c0c0550610503070000070309100b039401a01e01541a5006132071030181c0e4009000b08103105031481d846074812141007091b13a0305900303a210464518141c00c0e000e0001c9016a0065601c2d1020741c45900c481402181d04030349034680c54108007170a540910010b40e100180c84040c00e04441e5000a012521031012031184600359000074850540c003c0c020203a8522202003c000690031040c030040114890750241c00c590b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 291879118 1250 291877868 291877907
    0x60f0603080304150b0a03080c0723041d010606020307060f0902091f05060f07030e0105130b09040b031207050d0e100309240b03070503160b0f0405040903030b04050a05010501 77
    0x20f0001c45900c0103410f0221700c0c150081c1c1c184500008118a01025051452026054a1070075803550740c0881d483c3c071381d40325040c20b0341d111308460310301824154015042e1102c0315038003001c140c4200202c00d0940360743d9480140180e00000e150424401140715818602d160b80a0034081d1240c19000213046100c05040351682d4110408030712514074050001000820010709a940c0b224143d142c007061540002c407094020a8003048a011250311078030441300b00107c0038215100312070a160481e1100c0e00803a99664202da540d0900140c01d50b0100030304420301000c1c0d0b80c06030b0b03102d840f0b1409038285083c480d2031105105901c1c00801c0543d6941681601e100b8051600047d10312903800c1c0f6034019151003403c400144a011055080420359400c2a801d014060b41182e403400d582d0340c28195034002594400c5850103d00344180810308082000b0070343c44840c08241030400b070311000018111001c0710301c01c030701003640c0e00c4131f4000c4d0b41000e024582c2d0001415100300a590300d00000a400c00d5042110254040e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 291880368 1250 291879118 291879143
    0x3030f02030403020a03061e060e19090206031f0b0c030a030b18040804050a061b23070602061b07050c01050904090503030429040c1412010203090109060f0603080304 73
    0x180300300709031801140c0040c03101c4030040e52800d0000007046140340280c595031910340319100740d80c0305004680c122241014126960380d101d40c001203d40c01d180c075409c2c0c0b81c0b545455607a4050394a000181d406602241c44086400c030030b10b07420108184056204441681c270500440e0145580031040d03400030751b01800c0101d64010040c0002e0780e050b82c0c0b440c4101c9070040041c244003e0083c6c010107082900d50a640710a429034882d501a0342e00311280d0760b20b01002251031440c20024269007034a003618044044c2e040d82c0ca1510403049420401d8540007400160f012808014421204d0406580e120860102461801c403003074403415110345c0c0c0c1c0c4601e64180b24002a400200f51110f60024a074180c200c000d0b00d40301e08080c68040c034440c1c0e031264403040780e64070155484201060358519030700465009010609043c45c041640000380884d40c1e049901c00384840e41c2d441c881000780020751117002620000203a02c0754503c3c00904588030301c00c01c03c00700d40c0b4042e014400600c01000316500150408a0107100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 291881618 1250 291880368 291880397
    0x405070903080405240705010b030106050a1212030e0607020f070509060105030411150f030108010f020408031803010f09050114010f080d14091008010303031a0105040b090406090e03120906100303 86
    0x288150f19041e944c5c128400148003041c07107810b60180341d1200c0e0403002030040c0d13035946041111808460044241c0503400340140030018a060440140d0940e550070040b6882140c400c245007032000455403070300983c010384088003404805104440c081c000c211421000c50400308002005800010002400310b44100306050195036503070000c01e140741e90820342c142d40d1000d803002e20301700c0e030000c0c030ac2c2c04415170822294881d048a580282c40944499100541c2400c004145640800c0c0101100f1500755680310851a07800000340a48142c05009800100710344c2d54250703c240044405a0220b20402e80140c02400005408250030f07980d84024500f14440007881500403013240318041a80358411051241a480701d40c1224082d4100ca005e910100100c1e04603050120f01e4204000c1540e0019801708001d0014200e0314020b01f03001c80c00034000040c007a451304c00001c2148c0701400c1e614110ba10118050020b0b6240c90855035200b0035010181c80d184c141004e5200311801e031800010b0501c842d50030558170 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 291882868 1250 291881618 291881659
    0x80c0306040b060c012c0312041703040c0501020c03011506110c0405041b080d0c121205090106180b1e06070b01060c0c090207020d0b15030a0b060405070903080405 72
    0x140c0707002c002e1a02d81e480040350105402807824124158520015003081060311001c605583c03144c09152000e50b1501728100d070101146203000380f003100c3d050758a0803007101c482c1e8120051845140700c0c0c00f0500c1c2203400e090000e4078001600410910030fa04040c00040b20b12040c0c400c58007140c00c641404103103018802c489508046080d86090b400602d80340070003080c00304240c564082c07452030890742d080c03440d164111039849010000090001c11300584e0380c1e00c002070a180a045841050b0300c5e0240c10910240e940800ba500b054641c0c040e969100c050a11000b070040001c40c02d0040b0b40f0078100016001600803a14404241070070300020410111940d4050302c42404469400340d1108210413035603122000500218000441501c1c840c0e01e400c000304851007144225803000da001403038181002c21070750b51128541c0001b0501181004014030781001510100503a03507005104101258452900b03034148412904000d01107810084820020008190224101c030306558082e21103030001070160141e4031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 291884118 1250 291882868 291882881
    0x1302090a0b0414011d0c03010e220f0209130213050406110c071401031a2e0e1c0210030b0d0221070b0a050912010b030a03050c1c080c030604 62
    0xb41c01034200302e220a04009960b10355810b0b00d403900c44050410441d070002e5243c40310222034000c1700c460208014041d901009d0350141d400124160b10066001e000e0f4031000300c214441d40100d4a01c81481240411850100a82075000350204000c440020458000542503000703d59420f80443d0303260041014020150012021400052610f90792345141d0344600c2d603600100c1c440c804c289000c1c0440c0840e10362080c0074440e04210a00180b140e0030402004000c1519070000b002400b10031040e1404103400e1502900114408050b1103120586803440c0c280101c03000c0301020020161254852240140e0311210007107a400315a260000f081c201c16404070340a429543d174040c6d4011040a5804071202400c0c010701c001e042c0c03000580704903c0c0e49034586030442c040c144040c000f0410034414030501b030400e040b40424441c00030001007412a20388020030b007001c800c0c10741500016400204c0b550a400b08024992000c208021003101840424200078401c14000d01050490f4100202084c0c00c0c2e89d5541081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 291885368 1250 291884118 291884141
    0xc0d09060204030605090f0c0405040f0201032d0c030501050301060815070905092d04020a140604030c0e071701030c030209190e03030a0c02060402030a080c0313060507060b091302090a 81
    0x100700505019010542c0d034420b0390811003051142c2520510310303089c1070040b503000f00d034090104480c04c0c1d05a4010340290100781d5008c1c039410040b0010901141801c08011094003034401c000a45c041d04000090640d00140c005034000e038107200303042240880000d591404100e445005c2140e6441d0400c003102d002e2107a62100346d01c000c2a90511203082c0403021000c03134840041505c0d800046d00d010032a00d007070504070340196224002c00703002c0101c1803061142c1101803c0003402240b40589035034030300c5600c40d00c82e04140c401211450403c0b0015401c00c0c3c000442c000e0041d44158079624641d00c00c080ca00703640c00000d0045141c000892084940c2102c03144503104e443c0002d0008031710a40e1410798a4204582000c44903050407003c00d10300f03002054442c0036a4000d00984181c10043d1039080d0680d01c90f40a4226034441002a06a000d02000c00c40000d441103a130780c25074a20386800d2800030b0312100c4003c540308503038540500180302000c10046105a9054444440c150f849200d0f980044c185403514 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 291886618 1250 291885368 291885371
    0x1e0926070b040306020405011b110f030a0b16080c03010317090d0803131b05010e0607050a0b040f0203060a0b0102030313050c04060f0f0f0510180b040b0703090e0c0d090602040306 79
    0x103c2085407035000741c015a0004c0e40c9400d9020001c00101c0c90b442d20400380600b4040d41c215400021b0b0030030b0300700e40c883c03560040c0444d044135201e9551025141e0044030000c400d041c158903020700465000908a800102890b9403500f19411521101121101107590501c10071000810b490316071500241007a09030380100309583c603840d2102c2e0130391020500c200101c40f41840100150700020700100180143d0b070044c0d50764120035404009015080d8007801c07007a54581300ba05c000c07400003007103001c1d014811071148800340c2070340a461050501c0c000d0007600c5a00319a0a260014203582d03400401e0f29405035544480315800d40290600a0030710310500d4840d604142416070101d06a6041c03000a011201c040a030601c0300d41c0d9410805060040f0350043c02e521a005060044d11107200301c0101d0308180042c43d0800c0c60a40e501008003241d881603000c819079100204007403060507000154038008042d0380101103454541200e02c0c2d4400c1c41440380791a995540c03400d4000912025070305640155a01410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 291887868 1250 291886618 291886627
    0x60c0515090c0411040f032a2403021806090a08010c1d0d0305220e070c02040f0e030d1e0903050405031b010503010b07020d050d1e0926070b 62
    0x15007030302c40c60060080e0b40900d08040c0e4040e044c4148030221000c94180a01003070400b811613036000c10950504a1b05000c6e0501020078003e1a000410300c9401045181100340100710f007517221441092900d41c40505043c410b01000a20716603101900401890031542c8541d5418440000740615201d90011101c5603c0c22410038511394101c83d246940368141d0201100070f40218003000380004032044014000b4000303000d448101010060784040d0a1010442500c200f5159444500e40403000c480303003800a0004402ca5055045c644218800d0441403042440040030380b10800d9075a1107400d140d40c001c55038030a6079100400c130006c0d02e141142c3d0b68010600014130541030041081e0040d001d041d02c24011345074058426403600285400c01030041c0c45160640c0e203040c18030b860070f420511003640c10400c01d8089400041c014064000e1110b00c9843d20981c0d0907141c01c51400852600d41124140b0206071802d00140460040c0d40344819180c43d03607074103030402001d07920307080403c0c5074055441700c0c20114 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 291889118 1250 291887868 291887881
    0x605010e010f050409050c0907093506040f0305030603030c0123090f100906090b04030917150a0207020109030c0f03050111270102010b190306050718060c0515 70
    0x3029030480c1d02c2c0b0703800e081c00940c0f103c041004650383e1481c01440351380f1529185141b0300b448414540d001c041030070300d025120750310811482c4a54110748100f00800c80c6500e8031503c3c0300b0130f48901a01e050f4400c01004a0701e0b003950342607030050044901400780034020000031250751f8100103d5040c20241e078001d04c801c0d440c40d0550040415110150301e5940c41e030704002114610001100e00c0c490541e14001d000f0b00c51380f00743c1c50b002824014002d607001912200e00314045040703958130601407482556210b50591402c668807900e80007600000c0e80a0300a00c00d015100d000c1c403205540c100c035602c0d200698528040c070058840004d15030000302400c103200c10008a8199001901c01103d0241000f400001c0198101079018441c141c05603240041058803104180f40b4031010008449043c0000203019105000080c6480440e0f5030802103541d00c0703c400d0003040b00c180161a001040c0e0704003040e60038801e0700010000e0b1450300502c01000f0441d040c0c0001d200081040c5e100030f030b2600900c1d0509007450ba = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 291890368 1250 291889118 291889139
    0x30313061b0203090315160c0f1202210c0c061c05010303020a03030e070b030a1a090c041e030c051003060b1303020301050603150c090f03030c031903090506070c060207060501 77
    0x806091190080301090081c0c1041180070f14441c004203032a501000388048000c2c1c420423030444003a2510f0383d000007504000358900e02c007002d5200940d0010b000400285081f020307062820110a00450014004071915a00000c0c1154000000306d075000c0e1152410002c203940f07050703400910007005007004000030a16402050030007000d030180c2d60500044036100340040e030f01c0f82d242c400d014441c94200001503030b942c181e5012851894402101000540030040021074090040c0c54408101c40001010000d00915030b00030040d15603507079484060145141c03500d0248034504c1c81801d0280c891802d080b01c27994400e6026001900000c102c40da15042c42001103c8650303154000ac902940c40c20002c0707015403400184158202503010740422081e0b4940d154880580c1240710071303981004244288800568003800a000ea20300c200c402140c45100f410328003451100c040b41c0e60b4041c540381c00c02000c0400c8010442c01c0e8030013181d04201d200c06805181c144000d101e2b00801400b007515082c00461040c040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 291891618 1250 291890368 291890377
    0x903021b040b280e04021e06070204140106030608070b07060b06040306060306050a0b09040b07030b030c090f071b111e1201051b2d0c07090b031b03030313061b0203 72
    0x3c40100f58111a01c0d01c503442152001a50080d500a65030302080e9140c1090f4240a00802c4000e003c480c20818a940400d042c2c91100074070040c08034a140050203c29803504c01d8400603c030480041c4101440c001d05010144038955029140702c0e1600c1107088a502c0b81d2003258001c0da4000c004014580c0c0d40e04082c1d00800c0e0a6400ca0400c5081c9102040b00e0f142c4410483d011700e030400c021304038903102c40000381c00404003588040d405000f000d5140c1d04994a10014a10079800d484203000d075494034441c010011030a110030040301550140c05000840c1400d440b00300002c400f542c0d050b00403050340251901c0e446030324141382e9000340c01013541c0c0304040042d00981e00500d000210810702180b08009005140100c01e100c055a622921220b9842400181e039807940440c0380101c1c41c5849180c010580c2820505d410a01000f5140d10f80b0581d182070400c40051800302e51941c42c030349c1c03020140001e502c03480003030b10240c408018044d002042c00f078150b100e10400312a03400300c00c05810300c081000c0d48a801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 291892868 1250 291891618 291891679
    0x10e06040f0506032e23100e0106080912030406090308090c0f061c050403020d0906080606030a1d100c03140402060403080f0c06070917010903021b040b 67
    0x410a40c00c0d4018840c2c0034150040a0040242c103542850f1101880551198030f64142506507940150103881030b0741c07040c090b40c2502d505000c16801c01c681010060300c40080d00300da081e8403040104000024048039410f064412a03d000d05058071076182245c90703c03035809003c180601000041c00300700181035004e41d4000780f090b101c41d00d880d0745101d511074840019001c1503810000201c0c00f41007a141500041400e1a5245851410400c880007200d0440d00200c0342100541c0c0003101c005d1120303401000c400003c1c100792030405e0301464040007040c0640405840103e800d030b140c0300022100c02184403a100700000745401c4655142600c20444c000d400d031003070b849020a00e02101c070f0700c0c000480d10440748155009480146030502c1c55880d5030407036000e62030016510101744030102020740d050240d1401481199906031110781003a000c820382e0303c110343d02040d0982c0b4001d24840001c2e00448d01864050344400c0302c031040c0d2400f00105014050aa42c82e9620201c0c030903410041d40340600c6507060022 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 291894118 1250 291892868 291892871
    0x12050406080702060c03010b25031701150512182b020a1e0c03080409090201030507170a0510030b0f100503070305060609070516121115160302040806010e0604 70
    0x2c5400d03100340d0300c4850503a5210308003075040005010790004680101600b910120450b03a00702c40350309403611200245001100060314031540440c0300c1c11074403812409001c6d85501840d08855181c4041c11510400c05030a07404200d02002400d005a2020344031882c403401400e8416001100042031641e0849881c045e81c25402d41508100c4036200040da01c15081c3e21044980b4285050f5081c4000e40318107140c22580035070107400c040700260004026100624800c0c0c0d0204803068644000b40544100500220420200801c200718038404150540d03040047e103c2e002680b503cad20400101580c06a80000d400c8200e4007040c8400480e0200b802481450310100707038034590303846804141d00c84d0380600c4050690303401103021440300c0c40c1c90400382c0e4004e10f803030400a141c01d4900f400710601e030f00030748020344031001128843c0381c1954010092050001121000e031010300e0401200d11808030020b003080c950076500700458441c06009a0494010300182d00481d1010360391401950b102c0c081c00c48485028a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 291895368 1250 291894118 291894121
    0x213020d2a1205090309130204031a0708130201030e030705030403021c0201051c060302180a0f02030118110c06131b0312030b040b040c0c03090b1206011404031205040608 75
    0x21225034903035915010980d448049a00b034510348203003d028060700044150000f00409078490755100b84101c0041c0401e803000d6141ca2a60511001c0c1d690158402282c0301015401c2200361039105c03950b19444000c05c3d1007c10800e03c42c1c001280100a109801e00c0b5502c4001010818400c0c000b01500032244221407a9000c3c010305450410000c900700002804607000340704690f032004000700c041805414041001a929a803034001600903004020354040704200d40702800038440c0075014907201c141c0c3c4410300b94a55458412900200c01135034400c004415074444039062030002c00d42c21123030409000c0c1c00b2154581410b980600e101c3c00160002c8800711420049001903041c0c0501c010708403900200460503060a8400135000b800b0840c0c40c041e84956660445c130081d030b903144206042013042c1d0f6900201d01e19240750240400b402a041200310300c60600520742c50100700c440c0107a000c2000c2c600a084108805d881042d0707405107800081404440700a001907440e07000002d0000c0358605d0b130340c1c540607 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 291896618 1250 291895368 291895421
    0x40626030a0c03050304050f0304030623040c05040b0607020415150f050a03050601020c130b03011107080406051309050112171204140f07091b08220213020d 69
    0x803803041080c074001140220180d5400309000b00060355000d4052410b40d10781d80c010302c0da131314110360081d00304441480d952031504201d240d00f06441640d9013448240000c01d410142c0380c5515203c068802c1a00c2241c84019580a41d1103004c10340e40f4030780d070140091007a40704007007072031201c8078881c0076003040c40c1c3e500340366500d203684a0761010002013025140c980ca04200d12408502904006041e50f066110303506c0e18944585450760b99900410302041c00080c1000864200344c04d440318010000c4078100c00784030000c0442c0c03a500446003280d003142012541c80c02c2c00820f03082400300030782c40109003a240200010b01820000305208202e40303d00c2d00407039441044421540e1034040d401428051001e0200003500080800c2c15020b1001001c4046510710350019111074a00081c5806c424075481d208e62554a02ca10310a1f010f50380500e01d800e000700036140000c0c50b65914410202e034040c2c000301128100d820f54584004900c001c42100c4c2d030030356031941c6010700ca401410f0f0190f4174a4520100400c2c1018 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 291897868 1250 291896618 291896623
    0x11104030f060b120f0a02010e0126070e0a080601030c060c0b04150b1003061e03050616090e040503120105060f0702090c1908040c090b2805040626 65
    0x340d81d03116208041080301a100d0000425042241c160090305110050141100400c50317075114202840040225514510005242c0d0551004440c1400845e0080c140070b500e50120705520f144200000b014540e403095411503c00400c002c06a4011200c0d80f400702d0080740215800c4e058a01881c030a42c65240e8030901240d02e81550b40740a0640060302e80802e0018811000801103410350203c0810342004500c00540c01d94407841e000f401080c2c0d02d4104008403082c1c0c299045480d450031021128041c5544c440780d40b00d660081c40a55103e911854104005008440c148098076201e00c49036924946854130300c1d03482d4400c4880100004524000003180d242c440d0840b664414078000560a00040c1c1d03003880032104000e0650495401c0a1117019610507080096145841d90799036050582d00745801d00c94600e14030754210703407449820007219103841d4568006101d1311004103071001c0c850a01c03188401100131000e4009680c400d04201c0b0010f1001a1024404031f00d034019211312a0750302a0455656 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 291899118 1250 291897868 291897877
    0xb28061d0109180605040f0f0b1e2b1a3403020906030a061e050a0b03040501020d110306010f0c0c090506030721140604030806040f020d1d0111 63
    0x40c001442e07004140300811038000d00710769481e1801804242c00391608009400c0d64071601070070b40800e9450300300184243e602d019190303030701c0e00070b42c0c03054640000c2e441004440c484465140d401010900c0c0201f90301401070010b080c034100301e1440b11208034040e10f03107595004903140d9111503144000002c240c2e00c02855042600d4040da000100008840207900003903000c10f440c0304481416403c1c01400703283c6d15800300442c480c011100e00001c0c082d0418840f203280090703e011105195088400502054403040f14000503102d0032188581c0f296640d00d40240a4403a000742265001d0800c5080c6560701d1110340a1802001c00741c8880d602201c015038125a2b004860701c020b0408901d000c000c114904143d4401c58010340003400362100700d41c503480c1a020981c0340c480a0600906481d06240900c4810203042c1c2001c01e281d00500340c1ca061a40300240503d0010300018801d659800c08100000f056a045034064020301c50300b84540c00c000e51880c6241a0350742a4100c0c1942000f6450811043c1f80d800c58 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 291900368 1250 291899118 291899177
    0x7110d030f1a010f111204080f120c03160f0203150708060114030a0903020106081c1b03020a1203020d2d05060a0b0703021603080c0c030309030a060b2806 68
    0x24480004120340840c0c1e010f0440c00c0c44240da01601a50002c070348000b50040c1f01401104008080070b100030403102d4500800031403071044100091258041106000c0300710f4003948030550070000064280c0c240fa400300002400700035498400e0034101c00d4040400340c0028810541612080080c2c0c1d101030055648034180710985110100400026554580c598000a0610b0181c80005a1a0344940c8900d01e0301060410305861440c1c40d420390071200b584900c0307076241d440504c0000c02e070086081d50302940d207815420f0f0060014030702c0da800b41c01f0391340300381d0680d400c01120315402d01459840c0c4441c00425185400a640040c890707034140840710160740186ca000310740160490340707481d140961000031a0000c49003101140501c80c4d02440311400c1080300c0c0040c501a07021355651b4a0f02194091502496800c905d001c2e0b00240100201a90302140d001d154980210700401d113421a000000d42240d24041e0300346446141412048600b41d2103070f9005c00b07981040e181c44810088550484007840300c1c2c002036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 291901618 1250 291900368 291900377
    0x61806060112090807230f010204051503070315150e040b010e091f090501050f090405120903010209030a0503030f0901110f1b0a1103100908040504020307110d030f1a01 74
    0x401240b4102c56215444450160760400e04060695a074045085e11244060b5251441014241400c2c64140040320705044250021882d0600e07050100751030403000e2194440ca4000400040e110038041c0d0050710084007c040410b408584a10a2141c0e08070714030039a0001401b8402590f002d400e043c45482e82d0301e117051b15881d040007042801c0086880c001011b03014190803042205011190240104001d0049200040703180d40c1040306006210000e08042c81c405c482900070302000c42c1012a1002d4070780803522200f55140000300100c0d029200c4d0000a68046c031490010030180130340800a5406030103c040d01d04010b4892082a9080c2e98207810306615801042005c1083c101d812401007050294000d240d80060301450354a0342840c641420607110f02d44076241d00d411919042c0400b40060075544000c109040d541d4560000c01c0c01b4900800780a181c0c00030204030390307600640001e00c001c0c404004a80c00c0750b8210318028003506009510528071800e2603031100031059200c207140d180010613541c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 291902868 1250 291901618 291901637
    0x180209090c161e1203020304030918060503060c07020909031e03271005070f0e120f06040305180a05010c020405061f11070503060720100501080618060601 68
    0x20a95410b50065050503440c41c440810503000400c3c80d20b4001d05500c2c0b100a81a5620150824001c030034201807031030041510400c10040080d410034101001d8480d008070004c28940d200c0c884c003002b40070a81001d9418444c9404010345600e02100400c02c50344259003800d050b40b034240c1c00603a603004078840d4210002c4140c0b04c0404024204020f90b620038042e07941d088600c900c0c1c0c00990202800141d17101041d8011002c0001d20b902e036402055080311180ca001c18170459000130080c0500c08690b11284909115250300315040c030100288040114400140e40250a05240c058165801401c2010001034844114019440e088081c503044030810384550060304203a074204401403100400440d400b11105559180040c091801c200503030746141c481402c031001c03000803140341c60f100e9031001d4807a900034403c03c0072065200c14010344000c4480f940800d4507214404080c24454180c01d001803861505000080d20580000c2c032134010600d5080c240400c200c2003031415140d01049500d140460781881 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 291904118 1250 291902868 291902881
    0x1002030a0503130201140c03070303240b0c0709020412170723070f09021b010507091806053601051c03051606020c060c04080706031a0301060f18020909 67
    0x14980e03c0454030502d00710a2102c010440c0e04072603003100e80c290ba43d0754404a003440802d6010320401e50a09940d03803180900b46141c0c1d02807041c402550040003561440420f0015a4250402c00c0202400c0c2c1d42030199212a02c501500700301c1c071042901544e10701140c20001101c14640e000302d80300c442d00000d01ca0740150310500c40d000002401494400346200c3c261000440c8100e07490b43c04040c0071080000b6079030707500344241d04a0f1100300032462401c03a45048284034150f80c2020403101180c0c0e8240081150901c0c1c591803100030107081d84680c1d0003c49a07528003c0c05c0d40b58030b181d01d00c42c035910301c604074980c907880c28076181d04442401503940000803c8581808100d80200c0c08107001c0c483c0c60410b10782104181804000283c01d4801c480b600d4010410010f603150500409a03c04054880641814a803204040d9202c00354402c1005043d0358a40c05c0d04094020300c0c01030340c145c90281c000d0018580d0340c4841440707480548913448115024030789010381070105008507016507030010880d121544522 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 291905368 1250 291904118 291904141
    0x18060309150c050c0609030d0b09060d020d150c080f0916060e0415140906030a05030d0518061e0703090203030d02030915010f060206010b121611010e03091002030a0503 74
    0x2042c00d0818440103000300a2192400c0198603c580c8000e4040c645070390840340c050701074640c0100164810580d400130042d981e116803040e100030765011103202003620041e0800b21a02440c090300c5010300e0342801c0c040c150071074100f00c040340181d028030700e510126a00c1c034002a440e512110685040004494810004140304050201d0303124001400061a030f0140d80c044010701c0c546921042400f01510b03002c10181ca4260199a8070a90503005001486520380d110340c2c60b4401c502c0b111840e6603807440030030070800c01841001c0c2160303070940c03c8800d1800d0000381641884880800c088180001b400001e8042c0d01c603005031400706070b01900030341c186240c07950941c2c041d410040c080da07002c0c1300e031090703060b0480440340c0c070a0b0003480a000b54101440c14000d0090904005800000c1003003c20449201131070900300764607521140a021640d411809800f049440079500c1808048945c01d00440e1310030010b02100a1030340d20001c030303916505880c1c1c002050b078a9009480b8240701141050000649403020b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 291906474 1106 291905368 291905381
    0xb010306060801062703110a060e0f012105010b0406110a03171506030c0901081303021c0e0301090b0a0b0a031509030e101806030915 59
    0x5241c8040c0514a040c420403003003210103024500b0030126144d10503543d8480700401d5010503580d040c00600c40c60b03106c000340c0c071a10800030001030050103400031924041c000b07005040c88040f054015248130f5003c084c0e0300030452105601c0180140d01d40b203014042c0c02d00c418840c2d2070360b0420400918034420031121082d03a42c0305640c2000800d404c20701e84082c8250800c1d2003c410380d2640c0a000e0221442400d02c0c0d008030000c01409117602030b100c040d0810020a80c0c5003c0d40d80d851030151b540c03029a0801c081c0150700002481755607007840c40c401510b580082e040600301205020302107400c481240000765001a0f4140c14007902251602518803428000c5540982d4282541c031017400a0b80c0800e45411850b65075480c610400d4003071210201004001041c0140d19140404081d00e9031807104a4000700c40e03808000414014040d1047d9219203402a0440103c40c50040300752006204 = true := by decide +kernel

theorem cover : BRFrame.Cov 291726618 291906474 := by
  have h0 := BRFrame.cov_init 291726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 291726618 ≤ n) (h2 : n < 291906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
