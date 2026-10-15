-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4263
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:02:59.945901+00:00
-- url     : https://prove2.me/submissions/87aec9f7-8f8a-4fd8-a6bd-af1d9ce76116

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 766546762 ≤ n < 766726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 766548012 1250 766546762 766546777
    0x12030804080c0a12030c121107020f03100f05010302090901290f180a050603030f1c02160c050f0102070501021c0201060f080a150501062304080a03110105070e06 71
    0x2040380c4540c248803182d803030000260342c0200421102c684070710a6039450340c40b840e1560019924403400024a65401c4219101d041d4030388a408410000ca40250500280788005d9001c003800302c0e00300802d1402d5201c1110600d000c2e001810751100f004100358500a180c854115451800070001c500c11071200850942d40e0149182c00e2301041820005580d8448440c059040300c00384c000e41c56080c0c1c0040002d60b54030b048481809051401010890500b00001525845010b5502440c50546104444030b81000c2000406807055000c125001c0b14164041500d0210b42c0305000c4050200c1c00c0c0403c20404031065113001d4115400300604029582c0d0002c1c40468a500c40c4803003118102c20a0000c0b400740c469030300b00b034001d009a403200084000d000078141e080300740036002c0149210301e111102001d5502c2071048200142103011003440881d010401c3d019804888245246080ea8580c00ca45c10000c590601b600416800041c1c950601d00030301031b0950042d90381c0350481a41c1d20361380c0000e059000704030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 766549262 1250 766548012 766548023
    0x30f060d02010e031504060c05040503060a05090c041404020f120309060c100617070b040e270601090903080a05060604061b02030105040809031c050d110f120402090112030804 77
    0x40800c15079020b01104103110001806845144009072100d040f000780589007119003030f141070300501c80280b08505460507240002c02800c126100c100c0f452018140c041d21992883c001c2c42c8440103955254449d00c0300e0a00c45034240c072003d203014010000710302440300125025103403901c15040a81004000c5980304142103401c0c0da1146650b00b01d0500d802544d000d89610149404400706505207005225148030494404a604564a4050004a42c0918458844001c3c0f4070070115807865103480c400a5210314001c04010b40061200e40b1b1483c18000381d00076411280d45104041c280765200303880c1e45d84244008002c0c05a802c1107008620584030f640728070000c0001c0c2ca20a900070003003402a20501c170f42c00500030b02032070810f410700684a03401001c1c1d0300d01c28800c90b0170016a902c1030f1100711405080079103442d418000c1e04c80001d030160803402c0030014654010002040044034000181ca2400e240b804220041e203410300c140110241c0603004045002a80c6414000095111507400d03406030380070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 766550512 1250 766549262 766549279
    0x110615040903120f05060a090207050303042301050f090d05040e04080304022e0f02010b0a03080904090512030a150e010b071401050f07020709060b030c070302070e01180b0402030f06 80
    0x2402c084440d07007919488581c0d62030402d104001c11428540149000e010119900c55040f03a603180039404a01c120310000b00190028400240841c0740c01204044558112161045007603078640f20f01c0c215071040700c0d107940310756086d030501110440420216008111a0901c00d207428145401240d240c00001c00040c41c1820020009086440318458003101c1035000e140605c00680c5c072022840403001301c1110f000000c01c07218000e80624030501810310f14213405020b0110040c20750320364100310b5005c440d0311a009903c03202d0f01d80000f00c0400c0103500003102000d0f039a0310382c2402500801500c90f81a0b207003204215190040c00a494810305007070444480280081d5600103604e808000038096141090043d441c000c03c000580050b80a1a840f038403265003a41c3c4a25201c0070400101d501900840000410900006800541d0702000307010841c040c1c012925015a10300d17030087d03812801d0700700c0c490300285500c840d46400010b015402d0841c60450b404d600310310f480800310741c00001c003d04051240a01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 766551762 1250 766550512 766550531
    0x1052703010e030a050409052410031107050c03060105040606090b0c120c10111e1309090f060c0201020a05030613060306060f1a0f03040209100b04060c0311061504 72
    0x9501c10002c54090380b06032070b01d4254124019105410500c590100d00b41840c2c00505101c2520722002452440c0280c1100c41c030b40c01c0c0c0d05018030303075500c03102e000c003455a144050356030110228081c0045a1013000100081c0714054241030400c001a03100341d005604055080c092282c00421142c1039032402c030226519241c01001180c40c0000c861160b50a02c1400600c090000a0204881c0003490031306100f80401c21b00c41110490038854002d00340b8501000080110007a01d04030000d01010301000f40300e1160036101c5d02c8203401c9035496002151120b078101c4141c1e0810440d070054440002030341c0000c604004201c20080c04030720004288501c1140010102902d420742540007101842d006a000c1005c1e03a151080d02d0184041801052442813005114a104083c584121844012502040f07070031030304c2e69420301c45444009844601a10400040442c4d14480c207400307000248203503a00c0c0c6522a1032828080d03c05810880d0241c1990424402c004402c81c003000c0212a106040d580010784024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 766553012 1250 766551762 766551769
    0xc041706151c08030f150a0b030720010c050304120206071e11010c05090325050603060a0305011a01090e13031202120a1a01020a0308190e030a090303020705010527 72
    0x120b2010040c40750380c0210030b000400010210702842010b070910441c0c0440070030350030490019007510410760105020400114003034425452074480e104140c5503481740056107003409081d2501510304000145c0080708020501c07144480c04450f40c191400030f0f01490822041c02086580d00300500701d00200880c040b00c80c0d0074860354240c04014245c03402040656622400101141d03c2000350758801d10840c0e1000e0400c03101c000340d0403001d0003a007a680300043d160505028040d00010503181d40f24524000000c00f10740280600c42d00400c490720203d11102c07000002400345411600885905c566010400010803540031040d01055014208541150310910604c03000e8442c040e80306003245c1c025014004020440e8000c2e481c40100302d1024403202d91407400481c2e9031740f400c600180c0010580400b04403210003202c5100c02c01080c410020464a075941180c6186030301c98540783d40051641c820030400d169050005801411091a10b01c0c0742c00b0b00ca0441a00741240078003840400318407401c880700b5564 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 766554262 1250 766553012 766553059
    0x304080906071b030c0626060a12081c090b060d0206160308010503150907060c020102120315030609063c240f2d090c04170615 56
    0x343e00145200c1251a43d40003403090001500c022266000365940c0440c0241c040e40409160840c0380c0d0b04010410201c548907600075601802c1940c00c1a42a20b000c20001d9503038100480351802209581e0fa140100041890360f041d8003000c07030008501e01441d000c0050000340805810000495221180c1c0003640001405807140e5004002c0100c1040340c1d20041681124009049034400c60545d081003e03410700d0028110b804689a4034103800421041c41903501403400c22450500610445d8482c000300000d009540d0f00c1a110503522007030103022052903140401045070700c2500540909220304200b100702c0e0700340d0703106024014044041c1e4a03d80c0b011070f982d20000c0d0030540484104100e07082151141400c440860300c0000c1003400309915481600380b018424205c1e00300070748448041501c0b000118582c40ca1000d907811030801c2120b0008690b030b140380b106400b440d44001d1035039075180f6000806108108007801160070303030000010041c0c0000140c503101c0b07420a00b03030303071251100c22030004451409 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 766555512 1250 766554262 766554277
    0x1080a20040b1e0f030615090901060b0f0c1c123207020f01151203050d1b170408071202030705120403060b01021908130302061c0c0908030304080906 66
    0x1a902602492048800b0301c00400c010f06031444000d000b020302c24541c4400013100c1d15010309003c80c0b2080040d04009182a610100210001540c6601d07000364480c01d03802000c20a403050340100b441140903105101c1120340b108140040e07081d5600c528400340200002108426185a07113400001d4088485021035204a40a841c1c0991000112841c40505801502c080d801407084a84410700107034148100c441d80034600160b04503d40c540790148901c42c40c1e502045080201c207002d105c285801d103005108902c0a0581c1c40c0007016a070310710091298120100c101c0056640d40d051002045010701140d080d1604150700621035004c0030030592440c810214000c04510480300c1c43d9a000d0004c2000d00145c9204580c01c0c071800c018000120b030355820540303521062100150644c00002c650f4001022020b0003100c400c0c0c0101e560303070001001600300d01d040d610006000903001d20030040030304c04c905041701d01c0c0c141a841d075030400750700564031701000300018201c0c100042c0003c016503681b0203482e43e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 766556762 1250 766555512 766555519
    0x11a01050d06080a080a081b030604090f0b0906161b02120a0209010603090b07110c010309050c1005040f050102012d020912030a08010501030b0d06090804050a0f0e01080a20040b 78
    0x4403600d4a112540e00c6810030380009810100801d41482c1003171312010b2625403c230300d540d0960720b60304104002000c03240c4044550b04043c3c028500051a11459140708500a00141120389001d41c1b08900401815440604000d45d688154200b620400c1c104503401c0e40680382002d0038150408c50901c1c02ca802c81010b580505020000191194140c01a00c010b62081d020921251aa1503017a5186910103415801076000102031507010b520035032013085020f00500c00c448400d03120401003540c813041d60003c03130700161001406010034010440181e000308130a200800542c00c0240d0000801c0e80785c550810711040c55001446107164164040d100f030941c00402c0901d03540c810308001a625401010300e00082960380000044941c040e20a51031410000f41c0090f000d9181039607100c00800c01510115a81c00c1d00703005c0070845459072848030011f0418106880a22420181031100a05050f889400242d00c440000000101540e002e110b603400321014540084000c41c000601501d44424006d40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 766558012 1250 766556762 766556773
    0xb0c03090f0c01171f0b04060914090c0d0f06060c051501060203071209080d031e0b0a0b0f0c0102130e5a190209180402060f071b0602011a01050d0608 66
    0x150071140d0300080045581b1a214885120f13a40e40140883e030506800b095440030000c0f0004030b885e0038cc41c009021a000790440000c090960f140040e0403144d480c2c00c8a40001c00599003001089010404005004d00500024110358134020009641c1c1c0316008005121408864919603410301441030310000d400e501e815940140740400000b002031001f0002d40207031800c00861518100150b108110b03030410017500c180c100908090080000340d00841380e00380c0f070020410841d0722408003030cc0900440a10f1240c00c81c1c00710702d810803410b8511405003000c1c04050384983d0b030804450360461280100300402e000c5031310748103401307800c07200c1000600103060900c2500304200c0c109020206442d8414041c00701405004505074100703404034000c60130701c1da8120f00301ca020201e680c1503142e40c0c1c90317000d40b00520a502d000c4000c1d00d42044c94000ca078044861440c15036110803a04d09009070000074040c248001c0011482d8501107960340b00003811400c0c180040055803100c1d50205400100141148108855 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 766559262 1250 766558012 766558019
    0x30409061e4511090a06030e03120114030628050a06080d0306030606060e21030f040801230f0a05070912051507050a02060103110d0b0c03090f0c01171f 67
    0x410b1400003650300c6540e40d1030942c203030460010f078105a130b02d045405403150310403e08081058009002981c2d41e500c81c0e00c81802500d4880c901b041d80c0754007030800007503122060340062040c10716101c009007800710742000e05040d0400d0a2881c03e40d00c514020150b5010405460f030444d1917005006c01d4120714042c0c0260308804802a070941c105a044900c00e034801c201c3c4603640d4004417203002511460300d078000050380c1c0b40b0040c001611340c80d0420119003015a8681080f802c24600c0e6988150300811060751039043d4080a0000700d0340c0461035848174002e409851418018121040c84000c2c100b4050f60758400104a0312031182113641c0190480d44440070390380005082c50359650001c00407990b0103040d03203c00075980d544980280d862116581e0000c260607421541c0301d5900f1070604000700d4000030144e100201240303034094490701070000d8801813580c9041004030079003040b54040c81d032051a80540e560000f6664000503803c845005485010070548800d180c20000403c01030344900c0900240700d011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 766560512 1250 766559262 766559369
    0x19110309060402010e0f1c080904050403111b090f0415050a0f051305060115030e150a0c09050f040e0309040536030d020c0c0909030409061e 62
    0x40c0d010ba8000d880c1d585c0d417034060b00200598203241d500f0042d00040c5002c0810f043d000e50116092200d4410101581060b0740a00814110f91080368107070300003400321000401c8200305100c44c03400340800103440340c442c0c501c1700c0c082480c194002d010487c1c02c64080c1c0000d01406400302000307062a0402006125a041c44242d4070040c040c01d0980c1e400c010304e007001003500302160503260b1403500da021014101c0d5a11b40000f60600416030742c01c0509241d19114840d140141c00c1c000ba620005e985049085c0d1030030000a1038040740c00f08484c21f02404184517003030105907070f940205480004105e40c003086013681c0ea2400360035400380715030003a0014100307004e00c900e4a501c0c0c0404041c000501030403e825030304d546032884180d101b0418491207908104500300031840c040c1c004081410018080355030140d05e40d40483c1d07403003508031911042da0f000800d0901c0002464011003000741413510444070794414065803605081d1451080915070001a4851004030303249510010800b60b0300d40108080d0210031002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 766561762 1250 766560512 766560523
    0x5070b03090c0406031a130b07050a08061009030602090103140f0105100f0912170304151805070e060a050a090f0f2703020f010f02130e0f19110309 65
    0x540e00340c000d90b4030090003400c05120761011642c0203080d015a0315042420907030b4801003c1c0106500001c00d00064010921521740301d405620103070307525030b500c04483c600240030081c0605494443c000400c11a0003c40c1d000b025102035941000005980f800a6001a402400c0b0700030702e8102c10103444208200181501d0b403585c1210000d03150b079045c1d03008101003128115210030039040494079408080c001c080841c941250080c0c0300744603403081662240d01400071608112012650100c042c0d000d1a140e80d094012500c003210303219034007695248141e0b54030ba10703140107000e00c06501416800192440c0e441d80504402420301429407002c040d00c5842d100050b04089800901190416a04480d0b0552a100303103400c01c00f0b4450360080004906840301c01d02c901c052016411840b6801044411000030700c01d900850340442c3d00181e5800c8401d8081541200f903034404500c0182510406c113003c1d400700806544006d00001c070113074800303001d4120002400c0c09420300c548440080304011240f20006036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 766563012 1250 766561762 766561771
    0x72010031a0405100e070201110715200a0806030a170c0d0503011a0d0b12071a032809080f091212160203071205030301180218010c030c05070b03 64
    0x1404101c450031801c0c0300650f101a9034856051420844c1000664610702066401c104240b001148050440d501405d4075004a801545d40b00200582070961445d10722488040c00c260601c81c101d0f4000d00301c001002070081c21241014040c050700024099039050000440d15a4042d100220089558bd07903544690044a105406403007001e0b403044155004070196030480303001d509164090010802801401e420a04941da00c03162075000140e51a5291030041c10b0b50070719640103040562404a0800504080c04420680d030407080091001041d0b074445105031400320704004105c0030b2002400e210080c405807402400700140031500449031400040144040a812a0f09030450746410a50070b4a594840c092280262003c04c0309000410242030380302100d60004050300c080d5a5240c401130690550803004480d15040040144882c96050707440e2800415050411410082d8a40f074090b00a0340c9105294140031032001d9a008041c401c021881580d5408025900500d07524a03003642141c00684 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 766564262 1250 766563012 766563041
    0x303030108011e0204030804090f020702420a0f0908070e06040e010b0d060b0a0306020412021002060708040809061b010f061e030b09010b1206100501090b07201003 72
    0x40c400750f002074540c020382c4c01341d070b42012950380392600e015110300081c08030a4106070321903002e100e4a00035943d9010340c43c550445009510f0041540300c801c46502142020002400c400c2a1100e290401403441c2030740d2600e046428a04e100e18044034050324800c0c025406001c0c140306040011501403440007880340201000d56051050180248806003130f203100803044d03604074000745034060214515411118100d100902100d41142e2641c541d5402c0c0c1e0301c41d0308000711120440305807900b1803d04150219026800c0c0c8050107071802c0855004041490140000e001c0100103e00e4400aa03900000c80c0c800c040e520842c1d0004400c01e1003014080c0140010b10b800d52454901e0000e099122540070421014903c8004440b89040d1303900d1400082c5c1c05455090b00b0341d41d0342c40c0030800d515108000c034400c00301c96000380070300d15180049000e03a10070342c0c20460400c10407902c01c000032040281130700c7ea155402401042c0d1440b0380010388000c81481c45900343d01c001f03a140460305c900c0d0143d201080162546 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 766565512 1250 766564262 766564301
    0x220e031909080c123a022d060f0a110a030e0f030a0f230c1509011104051003090c173021010311180105060912010902030303010801 58
    0x80108111648580c1c201480380c0c00141c42d40301180d40c0c084001070345c0d902d1140050541c10080a01000501100070000c015901940c11000b41c074046c1d080d41c200582051040030818030440c02080e1300c544000c0c00210b1950285008150b460030070750066540c1c04803600f2070a89903c0b07101001009415011901355084c051301c0c141d1170f00e1810100444104000903110003207404000c400803182131480d24000450450300e5250407000001e4140240300d103c15010042c03020b103104004080c0f1069000c0c0c60b6034226850460380f4445440301c03206072030490344122000e000e404001c40342a4041c201c285002400e41c04820004100f000c59500c0d8082c02e0f442d8a0b04494650841c8900360044403501c00340042d0004010143d807203d020b044c2c00422080d4030307001c10000c2045102c2c2d43c240a0a40a81040b10001d00f002100e034070505060480c031018007003060f10202c03154034090200d0f01600ca42c84080340107032103003542c10f818a0800d400c07825440d0740c0502201e80e03960351282c80900a10903032110711008200c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 766566762 1250 766565512 766565533
    0x3090518040b070c02061902070801020a050c0d020c0a0b180909062d0f04032601090b012f160915061106070c1e0f11220e03190908 58
    0x5013480c00031164094401c44c50074250003004014044407040c418210700c901a400701d1000c1d420b0000c2c140720003450f01c401d0b450f22185400a0308040001d902c500866010102c02c0100ea610b1406103012240d81c04000360781c2d040c00300f10141d1340e003c01c940d40d030f0341140b40340c0c00788201d44000090303052003400b0b1400307020b5800000c507000c00c400c800761010f680301040c010341c0807403031005149901c0c5401502c2410130482c00c0c0400c19400250405d0380d50070102040104e4010055101c5074016031490020900c0e104454884440940303108261366062035a45c2104401603071110b1904000740000c2d0303e9840002c032000e5580b06c80c844040c00000035400081c0c082c0000020f00036000e8550301c034100c02c07202c1c01380410390b03250a021501d010088900f92008038030300c4e28008610051410124400c0e0103003413405183d00480c20701d1600e0002007040c042c010442843d070081881484040d9a251040c40900410f40c000800400d0307245000e44046100ea0001da65130000700e46030880b0040c0101d03030180c070954402440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 766568012 1250 766566762 766566767
    0x1409030d0e01031802090c03280e0c040204031a0712140a0b0d030f050309010216030c03030c0206090307030e0a05040203100906050604050f01120618061d040503090d03090518040b07 80
    0x140b014000b0740046549002c0780e1030f594101f0103990302c111034010036136180c07000d01e8990f00700310100004041c80b10741c1d850744400001d205100950414105407019490180395640b1043c038500383c8100350b200600240f0208030342078481c140150f10003110581c1131210040040d5003440b8902d00341c41086d040340c50410300210701c0c14075000d48005103426407a000b8918241d504296030701d40c402082414295401c201c4804034048201020340c50798080e5a51031640f007440d1501400f12030070301c0568410b551100b170800c02310003000401c80c1c80c010f5051403c941306900b04004200303000b809810065201c1d00210070820364a50b1340118008803240607800b4807640f0382c1c3d6810700446104500071075411111001d00810194007078a813035032100c5c14443c00001e81682d00c035141000c0203020500183d03a07540314801040f80f0441e05140704c00c90702d45020491014103256840503a603104540c9010300070559181045d0a0501074014200100005400c61425070001e404083b00b44a04a50445071000c2d00c0000c640e00a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 766569262 1250 766568012 766568051
    0xe1005091e010f0503040305160308060301150f060509030a0519171e031906030303020c0d0212070201080c0d060909030f03090f020405060420090307120c061409030d0e0103 76
    0x40e1200a21012901c100310fa95900090047d802d202d800c200391182d0380714a0a56180745030183c0e030b60101c0c0303041c4402018203641e480d03c288548400454800d1100c107200081810883c2c000d41003182e81e07091030101107420720b0500b40b0091700d280642d02c008041115019a600311542c800c1e00000c40c00c2060041103951070240300b0005506c84080030800f40000945001503401c2600962100940321031031681c0c0c01a81d61507001200081e4001c00c1d09610700760208031003991a001400501143e111444244200d40168000130b410482c212021446150403030b0100c51154542d00010b009590302c0c2c0388000080d0103005011800241503500352100d05201c2d1103003044880e80001c0b0000011916001c0101521000c2c001036481591020400140000241d00a0185892181440d1030740c00e0a4101401c00101e0b50000704c030207000510190000c0e142d002005c095070f040307050000d880b840800101c0c1540c002c480c6016010b102d0080340442d82c17900113141900380d641c01d0f6028822900000c07121003540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 766570512 1250 766569262 766569319
    0x2a0c0c030303013c0527100303031505090a150305070b0a122a050906070b0f0604090b1f05060d05160504050a0b0f1e040608010b031302040c0e100509 66
    0x94180b03502408185010003031003480341c1514240e40c80e64586002409404c46c41a11300b0721010001d41020001c1603014000c8080320f1001c8917070440440c0c40c1001040107050024808582c860391803030084141c43c0c514814401440d0407901f1140459143d94104a59a01843d00c040114903500b04a40c51409940510722800015000c0c80c241007115002c1c1440755442c030210882440810702002e055501e8032070143c0020350103502c1e480094200402283c071001c802502c920b00581c1884080408942040c0e91540c024401c004e40082c40e40c1300c400c52404c4820742d80c209035030020b0001b0300130169001c0c90b040300d07000d01c01140f540044e1070207007039047d1103c0c450342c42150b41007104140104541010a000342c400c001a51000c1c51074206910022803c0790b1006c041d80303089900101c0c0c01c0c000c0640c09400540134000c0c0b206c03014079500740507145101c2e02c0e50880c4009c0c0300c1d5440300c4405508501c0741489071018007014109000300e1800542c0506150480982d290060105410100c006103050000c2d2240f03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 766571762 1250 766570512 766570619
    0x61409061e12190501120210020f3414011215031109060a0602071208040801020304061d060106170c070209070905041404020607230304080105040b2a0c0c03030301 72
    0xc003806c03542404400c1c2e4402c10700358294081c401c2c0e8240302850611072203115050401c1c440301d203a000f02103509243c01451101c03000481c8241c509000340741e807400a9034030028090074035002002c841e1222402400300030b284034040742c45a03d4008200440014140c0450f1800c031140b1075039680300014840315402d184120300059000480401c0fa1504554803070039007e0050080901c1e10b91503940550076030b030054408495407950760004410a0040220016000c0c001c81c010b8000d80d450100010880340611309002e26485154010034041c420300d01c01c5684081c0c1c007800c0c080d11440c0040300581010100d100e00c42c021800d1102001e07600c25400c0d105803041c1d500402c00c6003001c03141d4451410761020307144191030682c141282080b41000400241c4014001c0c0c50000c1003502d4149014021440d02030a101030751810110902d980d114802401031a043c9c044a0703035501c5d414854070107440d10342914171b0990940000400482c9581ea42c500c155407548081c44800c140500460ac2c00c9016400d58040c4540c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 766573012 1250 766571762 766571789
    0x5030601260105010318140a061506050414011b060e010b040c0c1b0509012409060e0d11040f0603110105090306152d0a061409061e12190501 62
    0x1884d80030b036100240810080168200b252142e40d9034107004410101404001c0d8032500224081013210700400800c00018040085524030303201000d81280140c0c0600038075410080940641d40c0d105000903190f0a44500f804030030040d60b4100b0b100100f050b540d50b08129420101c3d807080c0d9090a01411560450302d541d02c400c824050780b03805000205045042452a1640c003001516954020100303001e001d1a003111440190f03140d00c00702c6002c2809401c8014040709200811519801c405a541c2c0890309030f9403001c8082c4c007890110050680c4090305540540381c00d4058403d07100b240c2c041016248200488441400010015a241c0c0680b182781c50f416404140010070f00103a40d07081010401000d8120459141003546088003503881180160a40f0ba141a00710418a014100303100144201d09060403048a4000041c07903c2c4101540203010f914005481204a03000b43c0b5051a08040303907a040e52185854008040010070a0351008005402103c0000e1a03002e58881e00d4101d8058080b40351 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 766574262 1250 766573012 766573019
    0x30a0207021504120f020607210810060503040b0711010c1d06120c0a0309170904050f100b0c07051003060614030f0a0e01020d060e1b0f3106050306012601 68
    0x951784401a041240c0019050010100048000e541050340055008400610400c51000203080d50740040050507403031061f280800080d0b800c00304032038116270010780a00155441c518195543e01c00c1c0010380006600e0001e2000c5015448000181c03041041070130041a406d91504100450085004021703450002a0120341c1004c40b030401844000e030942400304502e211926035040800060024400b58480016403080368a800e100c1e05130b01c5200500ea240c80c030704046004040b26022401745040c16039002841000035003041042c10010007000f08401c00c603280c040e00040142c0b4841c07107044041541942c00214605210b02030742c0c170030240c500300c42141d0765a12071600090010b00f0b01c43c07003040d5400c01100c880001240540800340500c600e000e911070a00c0108400d20030b05980d00442101c805002451901c807100003141c00202000c24203480d0f007110383c3c05c552140681281c0c40c0260300b02001000501c690000061813140c1c6003626140c112107842c5810803a414003c4045000b018801c00050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 766575512 1250 766574262 766574273
    0x3270a231909020a0305010e0a02070b04030e04241d070203071b090e011a01022b09120b0901060f0b0306101806050403060f020a020604150908030a020702150412 71
    0x9003400074030307048601d00c241da0380d440304000c99114150031030010303403034400500018256040082c3c101c1d0300a001103107003103003e40b01c800310000094002410061042090405582c0b150031400d082d201e040342450740320a4802d04040c825070b0b50f2003540c00b00c1016140b2840d03a091030b1080c2c0c0e4071403829074015624100036561003200c08001040c4401010300c165102150001581c80b4011401b020b00d400003800ca41c81c030200b952040e00c0c41d15203c0c1107500c00b0542d144545a500c0552501c200c10038401c4004030510902035401940a4000c003051008000b45030017030000e1411074901a8180100822206840b05d010081040f820300a031588050104003068207810040603400944c0d8041c03600f203518140408c01d4101180c81580010000f60f0045418018004140300d005208640351030708600d803035032251010b9100c00c0b0041000d010070701d00d00c241d0801c3c0c03513407900004d004a81c404407803a07980c0340550021000b5003001f5402d84c0178008a0303080c0c0b0080c0c1d14010485095580400c61442070004a0761030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 766576762 1250 766575512 766575529
    0x301150614130f06050c151317120c180303070f1407090e0d0801050406081c05251a04050c0d06060f030f1709090c03060303270a23 58
    0xa03041c42481807400150020101c0d00750b6018100c1c4e5070790540c0d03a1038801440780ca0305403105040c4014003840700500c0440d2001417480360095601070725000300003044450001050140300d1030000614011002c0000c094006401801c1400c0007060640304401e140081c15900d004614008048410040c103500100d240411089080110401120090b40d1039800500984540610130245070f4809100b04400c145c0080300c80c1d01410082d2800c012945c58240503a03503444c2d0300c3c071910340141c41c01d5034003240c01172040045038804c400710844811205e1500604800c443c92445013900c000c40c1540e501802c3d00c200a0f00340740201d420000a040c1c2c00e0000040001182500c2c0c42250507503510080060441c0b889082c40e40114010000310b0150159428021910b17480c24050301d01950341000482170640d20520015002100c0e40c034815240c3d03035131030042469807041103140e200742000560440750158642c5641c01040710305444da00741155690314007086c03100480864a120f400903014407425401e10114 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 766578012 1250 766576762 766576777
    0x30601080f1f0b12061e1501140706060e070f020109050d1103070b040b01290f21100510170112030302190309030320030a09050c0406090b0301150614 66
    0x92034040715002440007046610714150b6504910200305102c8905d50349007406da040320721120b0091824514107002c04104442040c180404288501046242030741940d820b150b0006080110a8880b4030003840c0da0030032140000000e40504006201d40d106002e0420f0140e4084018220000c602e6406d5070142c2c03180043e030116120034040400809c2c48442d049029a0094270b025500394141144103155504050700c2600381d141070032441501030000c9048980c18540d4500850703c501718900055209412980111942006c1c2010311503242c88000141003282e030100c0f0b0358210650500010b490800c00d82c068420490381c03c01c010011190583c607248800b922900d07005241030b049403045c50800302d07a01c1ca4200000d58030f00b83e003801c040d014816205d14000b6200c058000c0e40580c000000c06120041a002c0c030039485030082c9003000390804c40307642d1b0564018010320200d0b443d06060304c01024100507152103982800740215280036561a58030a0f10001e81d16002c10507116041c2e980d05034000d0a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 766579262 1250 766578012 766578073
    0x30402091b0a030608060601090b2203020a061121040302090405030d24230d02010309060e03091806091315090312150612090f05060114030601080f 65
    0x401e5801d408403003000524500d0314644000500d00c3c02c048801c2d1800350020052410304c0035001044c44403850301010380d555a94136101d4050485500340d14400e2a0400d6403009402444d0303010040341f03068120f03418175040c0d0b0320001100c1c0311a0300000410b00000c0c0540441d014000104014005410200003296000b80118200e0f4600640342c8603250490304540641d40200140200440420000c0740e0031400624529406000a840c52080072902004840c50a031203200549989811a40650050341c05a604030904009403000e025116499621038829913118403101c0c1c458604403c0a101c2c10f03802600090412485a61031444414400c0f40d441d0003641c00c889061126904007125014034001d0500c2699116158800700c81c0039401d41e003142100c0c1c10f60140c0c048c8280006907001604401114420801040e1001142010054100060b06c05400c80c01200c0011506280303400c40481d540c0c034258200c44283ea80c5038841925a0509482c01c8941d8000300d01124070842800f01c4124120b0095 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 766580512 1250 766579262 766579291
    0x11209031403010f051e030d210603060609150807030618080703020d1214040318030c0e07020d09080a0807020a150e100201060503060a0f0204050d0606090c1403040209 74
    0x28031081c5030382d8009034450314502e601501c090200d8140311040c0b07582c2042444400060000000c0004c0d10381044404140800c100348c2030310105101516807842c0c208200c0c0208110003502c0381000e030050922401400c00580c10180d4100c5a02e107680346800465014001400c441c03421560340d000030700403c2018501d080c141140000c00b20343d040e402020130502c250020308220360081c170090603031300001040800440c6002c42c19181e203160720141942c0141d261401d01100c0d15852120780b241e48203904041d00c0306a0005002c699038010120940c000c2c600b940864460b00703a1140c045401070694010800e094201140040000303080a02030b0202a1000340f10f6101903488540e4607181c41c80f41100c0310002009000c5845080c100043c010845600c14030003070010604040110741d5440c4098040443c1568803410242c45140d02e03416075001d400f00600d60340840141e400d140c40948140c2c021440b06919125000700024060350101940d0b0042d130301c040f170456446408110194100409070000b00500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 766581762 1250 766580512 766580537
    0x109050a0221040606060e060706050402120f07050a08030c0d0e031e2b0504060c020d06050c0d11120103330618020a081609030c1203080601080601120903 68
    0x302c00e44041c80403400020389140c1d1400c0e040020a40303004d036002e0410312005d4200c4e9103568488004071021940c100c02c004c1001e45562001c0780360400f442d241c01c0c1c03942c001c04611361400d00011500d403040714001c40342503604507200c0000319113900c0f420070b0b201525484807955a0010380035205110b00d1800007000d6800ea610801c0c503640c500c215503648200c8940200c4601c481b0500760f511b140342900307024603884a0355842c00707101401c00d2081d03000b910140005c0e150038608641e40c4040080030a5400003090140781494004560540c124a034203071500350a010b0084291034101065030074000811600042c164a152030307109640000700f42d031004075800080c1194038800c200703107400e1102c13040303c42c0054517078548005c0080740311105d042c19443d540108490b80525911141c0141c01c2886001c03404e2108500a0003070794115040c1d031004120007090b00700000e55040f400c4411442500a8450790a1541c4810045440d40005c94820b0b0214100c4031401c03100300b08990084400038428213241072030044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 766583012 1250 766581762 766581787
    0xd0311070f030b090618060105041805030f04150c03090303111509072610020c0a0f0b101202010804080d0e030316020c030a0b060409031202070b220b0109050a02 71
    0x181a002650581400c401340700f00d65100f00000c503400765103d88003d170b089040c24401034440e0b0301032094502c0740c2e407640c21030068003191016a0000c5680311048a0307880b40c0304080380300c0c0b81d08584112440d0900070819407440d24040c0d01404a001d5240ea0f1309c001c0982190390582d03480300180445402441080b500c810a40b8040e8000e80c0241d00e0b03000140005450024104000035603501c00d401d0300740c041c182091f0b030400c0003c5c5040010b202c1100140c4c60340390022000345800f010507005042c0580020028003070100c001a181d01841031030100c01106910745c1104115000e40040090000744a10005004500301d18080d0480e50150b60003c500103403505980d9245030000d46413480701c007a0002c043d0060b00c1d010040d4800c1c0080540203003441c40c00d10f80328800710990042c4514099a103c4580701e04040c481d200c5642c00400d450411502c40b295403d229040781400c0700c200c43d071401d044a04d059070000e61194120200c2e40324509003543da0801c11620041d040140060b00265024007600fa070019 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 766584262 1250 766583012 766583039
    0x61805030c01060302030c010203131503110a0548030408070b0c01050702070f0b0d0b0a06050715110f070f1416060302040312050c0a1b0306050c090d031107 69
    0x1c040c0c100204001e82140100740c140b1160a804905541c01080b10710780c000803414110341184d510307040c54500d11440c00d5007500035010808a43c2e441d40c1000484408164102c0041c00711865030300914440b0140601074501d4000d064120420851105914241c2030304195641419007141035058a04081d940e00881e1701d03140c2c0c5a001b5084014020a509503000d00034424554401d10f1403005000740d0f440c1814021141402e8080d2061001000403006c2d841d2249400c85906520041e00302604199501c030f0007002d64102001c00c40e15140307001400480010140200c034400c6a0002a50b464104d03403c1c0301001591021204642d1206000756100101e4162030b070b060342400d50071000d410322401200d1031012030301c0650402024540306120034400300c3c040d010a00255903960410955811140d082c85190020000004007505040c03010810408482c000680850b41702d407209120071303116410b40c04018003810200303d8000700c4818091010900c03c0f0b640c0b002c004419010354120644034241c102111 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 766585512 1250 766584262 766584277
    0x3030301061d0901050a0501270e06040b010c080901050d0f09050c0111010e0d050a0e042d060e16050403140114010509060d06050c040801090c15080c030406180503 72
    0x50006840d0007401c1c618048640c410302c0d022500d4010715030400c00010501c080d54000c460411642280b503c3c111500c808214894481038100281050b503110b881e080316203812240c0a002e80d08080e000151540905001242c907640001d150341040c980d40011245908102e03d40d5040984030904031010b0641e80c440e200043e4060805422007003076110001d0700d1a290700c40c420180340c0c542021905642c5000c500e21056065921340155207246543d011203c52031441c090302d60242c5031a00e105014181454210112031018a10a402c03583c0d04418600b100c000c1d02c1181c08031001f86001030500b4070719901010540c806400c5c800e00341a01c07525803008125082c001c140240c1e641d11041c00c4103012814100d4014001119842514a0002d0201d0448102440f004100c02e448002060218000c1816140a403003928020494000b072410a51808800362150301107015401c0040d0b00100e01c01d50035603206006400355145180c60382e60f03d060040003000140309007200c03030a68800018400f8070050001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 766586762 1250 766585512 766585517
    0x9050a0c0e1903020d080702120709061502030708131511060604090317100b070309140409031b0503091e0a090c0c03080603070e0f070909060f03061a0303030106 71
    0x80035500140c01410080d41503446810004241194025001001000e583d410386845045540c5481e051305140145207000750f1200101c0000c1c80c0c00440002c088003250246042403028603a90501c075100c94148102200c0141c00801400e00807486e408010301c0d090846040303d406065840b604d98021000301d04c100e0000401c1403040c02c0d00c03140d0401c1515000f080440b401c1040f1995941c001e000203840322080c501d00024480001c5203000504120f000401c1c1080045070355411514000b008000b240c001c0c03001c0740d01071a6484007541401c2c8601c0800551603210429419a141d0105003070b00da071200d04031028401000412030304d454a00003010100c00300400f07039401038844410821050080e411601c007281c90a8060f82d11150311641c100c20464040c200101180c03501000300f030506906811403280c00c11200d0a009910310003101ca00c0c4070300202c0c3d40f040300b166180e806140640c0c2041c40f901805400317440041c004141c0d035900c0007000288080040c031807144607001003425500300364040c501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 766588012 1250 766586762 766586771
    0xd0e030f0601150e04230a140916170c09040804080709020a020c0906210309150901140a0804120c0203010e060105030115051509060c0f0c120604120305070909050a 72
    0x1d041e60884034046424204072014484840d4070a42004078541b5070f9420344504c00413001160100b01c06501c400c1c01600107003008005454030122041d038030f6070040ca880c0301c103c04012000034810b1150403104942036030b41c0c02600500c02070300304002307805d83c0c0a0401d9550100804c0000352220040155030000c0003080409605d8040700c00e0040d042100d003040305400341160008106213a6604650303419000410000320500d41d02c2c408000d4558080c6100c40c1c0d400c015030703c0c10340500c0d584c5000504a588000d0341c0f001c0c0445040c405007500741c00f030742016001054880c1c0c04240040c0320001c1010314601e140c07400050324480c03600080c1c01c0d03803034040f08242c550304080300621040c1000c2c0141c05441c8000c5134a200c62902e00004241c18030f00042c0705110011011601041a54502c01180c000501d850202da9400741c075580c2c6035489041d441c1c40640315003020380e81e0110051000c0380c503511172600900c02e94450711612005030080c0c003004040b03a040101041011503805050b1046501660f2550000070f0f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 766589262 1250 766588012 766588049
    0x30910170421110709021b030f0408070b19030917070b0f0c040303120b0f0a03050318040b0108071d03070b130807030506190b2215080d0e030f0601 65
    0x800c0c021112100b842001448400510180380003d80041102c520742001a500c021400e2540c42c407102d80442d00c0c0e140d010004514004004541c0500180c0740300005840c6001d946026010300e91141d21103e0510400058100441038040e5000410351030182c4171110007404100c030504003e41c00100222080d445030000d01508080b8402c100c2d41c00800004514507090641d103001d0f02d11442c4140840c0807076204c03003d41840352120344844244401c084c1c02526507648a2a02940348d402c0f842c810041e140321140200300603c1e05001e050804041a118030703041da2554003048420104d00003511040348480c6424401c9614200b10202c000c1c8200040e2f141c441c03106500a100f00107140e40300d001550301c00b1509101103100820304031b8015622880c400691107a48101e0030142c840d2914055124a030006000403601c1e619020314079070f8007903a50410241880803042080c01245001e4034155031701c0b80400814540c02404420f604000c018229024400010021031820009800c03013580045840e1410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 766590512 1250 766589262 766589303
    0x15071b111012061e052b031110021c050a0603081914090303040b0309390a0f060309020103090219051302072d050708030310170309101704 61
    0x2040070b131080400c48000300c2e0803e0041040d00300f071809040e1049070070340c3c594903142400010411b0b4183e040a051031190000b4107010709142501c0388070f001ca50054140c14104a12248220760003482c111010341da44404d011126402000e008004511103940c9280100219400782d0182c0600140034490050003d0113003001452000b8500c0c007502009000d0003034050707907030300030096034144c900507006142c69a0311503c00c10310300f001c00f55503509250f800e24408548608035001c1d110014003540d480e90100020602407044285031841001c42e00781c882c4506201081c42a00070310300290052402203030b030b10047e070009240d14018145c041c403072003a100000c100b6800c0c426086c003030600803600110304240b441c3e11102e12002c1403100d001414201391090a1742c0e144008448421540c020b03048a030304d180c540e4101640e9900513640207040301c40c0039000180320940035000f09007089181c005107007064505c2091200c0d20f00000380700c0c1d041c0400943d4a92051030380720103084c403942c025100d184030f038809184003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 766591762 1250 766590512 766590521
    0x22170d0605030606030604060e1c030c03060608060312030601180e0103020307080303090a0308040312020a090e010f0807090c050c0312070305060d0b070e1f0c0515071b111012 77
    0x106010380c00c140d0401c4001d175800b08409074000e07045200421005090310455080c0b6840f880139120404400e00794180065040d40108161000c0d9101004041d49442c42a01c0d000d10860300c4030f500d507100158807035001c09203102440c0c121382d042c10445540340e1221a4940c401c40d50390445c8044c2e410aa0040066107802c000302001440404051403071402c0014401e6210301f0400005410b01c880b050114040600c507038500c1380401c408100c110740b01c20015030020300d100c0c443c0c0b06581015a04200204100640c0020101191503040040c102d0303620789060740303010f8824180700e032050150900903c0340e9007000740000d000d034159415541605240c00c4002408030307100030300228000c0c0081c591801c0020700314441c00e41c00800390f007422300064482c074000400e100342603150241d40801c4814412010394020091000a41c030480035a4001c81225402601da10401c80301800041c00490065052540d0503810007030942c0501400050166030401047c84500c645c5502c00004140203480351425a05124 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 766593012 1250 766591762 766591769
    0x10e15010303050301030f03090902030a020a08010605040f180905072403020301050625061b0e030d0f1409060f18030607021e010222060807030e0622170d06 69
    0x10520940d50441e00c008041d03000500006000721805e903604404c0c140900c903071300e0041040c1041555645010750300c40b40650010401c4c080400c2c204800800c2040c0a14151410784600c1401120542e00e401520b106e8407000c3d00054010599030407044011070310078002c0c01c011b0180d62070710f50b0b130240314416522425804101c411040500c140014000c650351030080343c242103440d408100d0541001480c00a4102001400521080c40e1412000c0485400c10042200741555142c52424803014401d0584404400c1200400188148000c190a40c0942000301c041c07440040391604025021010400ca030780045642c44403040d0100714000309200d040e00404180900390702815140c1442a00a5511140e890301021038000411440c03460740400d605852000f0750b54010007007030715103c0c6c0c0d01c0d400d150864010342c0001a00304002a1605001340180b40e0451410401000385e039681103007400c104019404518000d480c0d55958202240301c0b400b2400410000c2008199214a01c011400894026070b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 766594262 1250 766593012 766593043
    0x11031207021c050414301005100905040302160801050f0702190b1e010905071b0302250b0c0610081504060b04060b0406030f23130309080a05010e 64
    0x20407468116910400351003c81d804400c2c00c074100c1180b000012816080c070380c1c041d0a0440040b452040030000c00000c01010602042644c0b05003c0c0100001c064408c2120444c20200480c07404100c007107070031380c03085902c103000b4410f42d912402d00d1404034061500c0c41c1d01c074143d01d07915101480210300c48580ba035908101140010000c8401442003080b81c00085a00682000b800c000054540004e404a07030b0900b59044404120540e15092104c0003028180e41c0319000070243c2800342c0003002e44000c64182d1300c0d0590002d01c4d0481422050710b511040034401c0801d0310b030491b240040c10354914006000d00207042c402415040ca01100c640c1180e40c00d680c0070100036808410380c2c8800400d071800080c3c0140c0c000e41c000c2074a00c5402c01003805000c1ca5449118040800500043c1c40c540c9640300d00c2c1d50850740c00c028008101c840c100e94125007101c03005444889039010104001c14541000c0d850454428108030940643e81c400c1c441c18401d04080a4450713946800d800201405c060000104462010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 766595512 1250 766594262 766594303
    0x120303100f060f030507091d22080418111602031c09060e0a1d190902061801031b0f03110a0e060a020c03070303030207050f061b0702011103120702 65
    0xb50014210381085140c3e00c1803640d1000400d000a20584002000d001918046805442d01004400d0f280300c0c101c80c09281d08103441c820544050b0080340204480d50030144080c1071605110450b00c411300d2440c0c50700c9101d03507540f842e00011001d560103045100000d50741050080b049005140c200904144130800e20912030780d902c40d005800c80384c400b05641b42864501e044220480100c0c0c4080070640003800d5407640d0640305052140e01c2011140f065520007200c02048170040c0245095442d030300310080d40f0030b40c280b004418034a8140d4030344120903014940071424180031071500310140290200c80d40061034081307502c4da40f0354141c0103c900c0e4100c005e204601e03001c00c5a2001705014203856003903100b00301c009a50440e41e482008458076503000101070740d09a43c0d8a10300a002076000383c204480e1805050082000300101080c0c00d8460944101745000003280000080c080b50301c5150304906005c2c0002e484100000d040025011200c40015008480c2c01d04901c041d1508807176106000302b01001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 766596762 1250 766595512 766595519
    0x100309050714010509040f020316030b0a0b0a0c12030e1513080f0c010606020a0311060907060311072108101202040c030e0a0c090606140405060702040b120303100f 72
    0x76094088445500458040c9000030300101c50700e214001c04141c0c00307420840d00385d48034000c0358015806842c550f824500200c400791825400c0e1408034103681c2e44035500d61307410018246508010560344e604d074502007a22007903647e1040d20040d0381032001d0340020355400602030741030301c00c0085c444030742e030041107400003860244841501c05034010001000e901d00881c841061004c00000c3d24400350054000340314482d1180002560b90603942015030004910340d03031610719403c3c0450009c0c0039103002d00c090a041c609020f070540c003400c59603000b07004207982008994046400c02c0790885502051941205414a980d940208049000780c45000410107940c4100075060b0280c188036032041e8181c90100f0100c500c4070044e4002c05601c080e00c4007902a0740141030070480d182c0041c0003174601c03443c001c001c46902c0301800c81e00b000302e20300321a540440c100301c10300803440c016001d030094600c0100081102e402c10004150000c02c2456001e40303d40c4040240400300500b840000702a141e0b1960031400c01c1e15 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 766598012 1250 766596762 766596773
    0xc011b08010617010504090302010b100e0a0f030308060906010207150e0909060106050304110109030b0412080c031501181a1201060c110112110406050a080a09111c020d0809100309 79
    0x1c1846924440d0747c0e01c3c407003032082500039008003550003002441010640024a40644010203042882c3c1c0328042003039020a01180841004007980d4050360303a00c24955401c0203220a400015020505510a00da00060260740c10651000740060319654410881d1510003440741c1d245000d400c040213608694011312816603c078042e6a48590008440d4030b040c9403040040e108070f444d50308050010701c403140400c8280800750a2810b001d0300745661380b0b15955500c03020540d0600003980c0c0004a44251101d04020307601c00d0242e0b42c0b1041c002100c10501580da03402c6019600c407c0c01004499030000f04d03003d002c1c400210280c0c0d0040c0b6242c2440f00101000d6900c4a44034010700301428144440511450b4412100380c0c4809800d80600144d02d56641c1c6510001c0c180360855024600011040400150084120300404000c40d50148404c0d0001c40d030b4104101c3c04040c01d07491a8000c110310401c280c05681c0f03100303240c00e080d030242510a50310300350388050120108092068100b814180b401c4440011b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 766599262 1250 766598012 766598057
    0x309070501141905131d18010606021e030c1504121706060d18050319090b04060c21181e05190302040906050915040c030b0703020c011b080106 63
    0x100b603182c11941d40030b481541c0841300c0c42c590000c1e4040c032290700c8500f42803070010080078092503400187c2c3e001900b031810007500361000b034015080140c010100c1e15811164411807888411a40429641400c0070300c000d4510b850102c1c41590340105001c024801881402c402140c1074408604d090841e80004100b808503504001d0000c500074400021401a0102c190703000c14070303a0580360390841d031100c6981006940e236007203000300b10700d02c100c401040b07815540a1065802240c600304059400d1a141910980c0d0340591110140d40c0d4241030120205d02c8149400400100d509580310342044165504202e414140283c000d94510f40b01441d03400519041c0081704401c8440490f80d03810701d12003040a04c5400c0a2030340c0000d421506001c517030f00030440550805da00c80c4030604200d40b9600707102c103c0040e9001060701c000c3c3c100403c1050520200b4000300b005580001641000340c5410031329401942122180e005101c10040310703113224901e0759404803149004001a00d040c00c3c071881c0a15243c0c0c0c079103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 766600512 1250 766599262 766599307
    0x3280507180e0c030606070b04051b040204050f0d08070f05031321020f040f3615020a091a1903020310050904170c0d020f010507081f030602030907050114 68
    0x90040001183c80d5100007c807086280e1002c0200054103192504c1070392419403607800d03202544500342d003c5c03031428035209840864000800300300d2044400e2041c0944928400026a1400810400c40300400c0704030f4441e041e40d92040000f15960280c0740e401c05c441800d9030700144071300780100d40c5d20b0b181d0048441e117041c5402d40441d803d985c0d80c400e041c006401409009180c6003a50304211025a40541c05000c882c50725004820805002e9400f0f9030403c10031160f040c0081ca00030781c1016600c04103c10390301500d00c24a050514501c65610740d6001c400541212010441551001804820048521140c400f400341141019819070820710400700301c0d9441400b90350b0042541d44e00050038001200151030100300c02c1d0074425512044548016228840034111602610a54641032080c4105102e40d61007602e903a07880d41525252216042c40030401c411a032081d207250000d0100108541c0d10080d409241200c00400c491881c000001d01940d2a505542050190901044990426090000409 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 766601762 1250 766600512 766600531
    0x4080d081803270301061e06090506070209071103120c030a0b0922110a0303050a1b03090b030408070b0c03060103240e0c04030c080102030a11071101030203280507180e 74
    0x1c1819101180c01094558800d500020200d0300a080101c7c1c850030550a80e4180d0366400582d0362200203210880c0308600c4005c0d04014100005000184240c440007101c44c142405d90b460200b4505c0d1051489100346c59a404940e8004140150382c880c5100320b5002c5d080c00d85018040389400c0300780c5c248070384848000111840500200c0300c204910b0321010701068038004e10032940c150320782c18010201e400180303841010a10540401455001046001082903495501d0000c150700f82041d5204580000d00100d0704010180400740c0081c0c14403841a22804080020302c2d120b00e044000181a14204480e4400c00c028441e00308625200240c0c4200540c1c45100300784c0d5081d141c8116000030f034480c0d070340060010507004101065044c81074009600402440e40103022104d413003102e2098a201e0b40c44002c1c8040910240f10030254020b8025607404404d21401e43d201c2201001ca51000a00381645055115562410417100c01d401c42c81000082c8004045400708a0500380500411100581104139 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 766603012 1250 766601762 766601827
    0x1b030a1a06010c050f0703030809030f0d15030614090c0a08030711011b0b2a0d0c02120c0a170307050d090816120801170c130204080d081803 62
    0x440c0e4040d9038124580c1e40d1003401c490101745002a0151228014007003213000490035008100b140314000306070360190048602c03403894141600652802002c003513205003100c040e046030020111714a072054040503d50703220014200d240900b4081d041422181d505032048401e44402c1c4109a00007040c0e802c4560f0049501410b05081c0380140d88040e2180408455080b085028600300300403001d0850007035102800d861b15a14200d402c0031030700d11442c0006c81080c0b00c1070060b88044c0c803013500400da02c005140161801c46401c20102030b03031544810a21900c81e81b0000480c01040140c0b0b80c520030315405c1c401030508500700702200501c03130310541014202d2030b9141c820180a0000c484200e40711501c50301841040541c89107440103c50351000a01070118400400004590202c02141c4006810302805021090025001c004540c82d1440064441641c280000301d54468100400100340e04140c950100c03a103401d861143c1d4101110441109541080c41383c8030340003001c20f410300003012081403d1030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 766604262 1250 766603012 766603021
    0x11a030d09090506040e030a020f0f19031d03010c020714090601080f090f030d0606080708090d120f06060507021908031c09060501060905010f05030903091c08030103051b030a1a 78
    0x10040c200f007200c81b0031140000038000300d050350000b4008240c03503d02402d9135a030040041c0800d88407460540c00741052a03000b1040030009101c0c1030386086620a00500d860601c2d4144042070031114107402c404050785c0608403e0005803041150b980256904030352140351840c2000008001081c050070174152400301c6004514840c809000e0545071001d00d030300302c98840c812a407c810103008188928404940c000005c52921445007181e03d1144604400609503084d86180445080d940e00b15055034141c0c0e41e0000303105100d45400303000000d00560345c805440c0c0d100750040120000403008850790880d500707141009114070204c141d83c1c40140800d120000d01d00303c01c014101900015400825140c500710020804070307001381030720054038000e98502d90040310307452050310745100566440c980c030384c4140710301d050324644000c00601d0005054110107a840941d520740000350030a82080b10640c000202c906200c03505400c20751241102103004050ba000c0644500c28001241c2010003081a15407000070b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 766605512 1250 766604262 766604269
    0x60506010c23011113300b060909032a011103041a13050c060336012018120a060606030c05071505100510020114060910180f0509011a030d09090506 65
    0x10b040f0b0f00d0312000c04030303403680f07151a047d403d0800849607188603049180c0030807c9640c0010654200300c0d60203c1d16411a802000060565010704183c0540b6640b21000080c43c101e490b0040e40c01584075071258100350b01d2501c003140c1050401030090045d5100030103803002003403000400701c0c41220280c4890303a69886143c2d0400c40014105121003051080e48802c02c112000c114406411041c4c0b80000c00105030459200038501101e00c1d48070320340a00c21311102c6120740038600482841a0000e0950100c13050089005092072a216400d4a05680d1400200000340c1c050081003040380d402d2400710703e820741a54072401d5014102e0044038034160343502d0000741124017181c808009080020316a80e0618280305000340648031050a003d9440541c0011460509000524038020b1100b40e0121900e54102042c403064400e1030b105405041e07844648171103d0103200c0c0300f098001c1d20741800206800d40b0001455018045000c2043c0c0a0f40c8803810020580c0c2d80b0540c52807d8410881010825460b00d0000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 766606762 1250 766605512 766605569
    0x406110309090103080c0705091e0a02040305010e0607140412110a0b0d022d03162607020f07140f03030405060c0304050a15020a060506010c23011113 66
    0x51a400460440010050201d170402820f10a52640700715070303030162540c05100700329400f540e10740784d0803c501210101c020141c46410b903010320103400c01802c060303580d100c0c02e00356158503680c03100d0394102900b400035040c1d10030600203c1e020b890101504e06490301010340ea05c060400b02c080c02d441d28001e00031807140d440200c80001402c0c03004070301d501e80e111800000002c1d801203c0018600601ea9079000340c2c440c0d2200c4030f4201250252042c0d0a59460901004e03d00c00b001c000c0504002c1c001c140c1c00c61600c00d400100c4080c1031003810700700e0742d40b90200001e45800c408040d0fa203003540c002c0a04010702d08201c2004c030740701542922010108000c400c0485d255018540100b0b90180010984407071649001010300219142114143d402958810443c13603d80d6000c40d0000068000d4000e1f10007080d038542045070004810b140440d13001010782c44889200107140e01c0807031483c2c00300c9414503008100f400340721003c040414240e4544203160301d600c60441307410b01c1900c40c0f0510305601003c091035488603 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 766608012 1250 766606762 766606777
    0xb1c0509031206180a020316180504021e040f0e0105010c020a1a07150f27030513180c270e071403090f10020307170a0e0708010f0e010c0504061103 65
    0xb004d0b0386092640808010350001c483c40240792201d295150b0500d03116207003a10b0290340c074104205010b030070801444040d6112440980050121008010040890710020001408002e06924115090000481c1c5014041c0e00517410402c0450503800540d03201d00c1c1040440d01c4010b4980510002e190701c1b1000381c061000c0241120001c2403804800001e0f640100300c10307601c0b10314200101e01c081c0250303e0030f0841c140480b0403e441018018000030380a4002060f800c82c5070702c10044d041e0b03928544114440c80c81804250200c1d250010980704941000019044511030341403101c0034482448401504041032050f6580a42c0d1080842c0d603650107200381540240d5240f51582da0b0f49403161040c1c2d83c40c0a02c58404455100f6a5407034210442a171087ea070041a02d940c4d411002d85100d070840e051110060065046d4903036500f85404011000c1000c0700c0280350401c00032a240e20003503490001c981c1d140c407916255904041c525002c1590000c101d800f80d401ca420001a80c0c47c803903030564a103024094 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 766609262 1250 766608012 766608049
    0x31c0516020f100305060f0114220302040903050d270201080414010612120918050402040e0f0a060b0306010e0708041b0303090302030d090b0f0c10060b1c0509031206 73
    0x20800e452213503d03401082c41aa03094580081022000f4011154400d12850302410f1100c144201e40c41110044c08814508801e84101000c0985a03000601201c0704032008401051b0700080702069200e0718003400c0121941b102041c0326111980c0c54050601400210007810020780c000000d007003020810281441d0041c030700003040032035151860f11001343c10105054034030038501d04c840403845101d940e000058a242611049004556841c000c0140c04050b100300e0340705495083c05480f00508218a145e0442d48030010280c0c82c2c400d0070050100c9003c80381c500e010fa04400c0042c080d4949481e41d41e90031081c0c0e0b2070550665612414006880410141c4403a80080028000410b0607445000d00781502c0c000c60548104114891060350b802019106003520204244001411614000040c2191884030415a0350a0800b080d0b51411101660411100c00c20085802010700c40240c0d4084d0848420b90360412440c20810402940c17806290104a0009442400980d20341c83d4440c44014888041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 766610512 1250 766609262 766609279
    0x30405060f0706051807090c020d08370f0605060a0c030507050111030601030b0607110609040f0e07061403010f030f020a0b12070f0c081911030705010605031c0516020f 74
    0x1000c050181d6031038101c1c205603078411b2050215603606184a01c5043d218160001c0641c030000300300640d0600750041240c01607244000040c0d0681d02100d1101e40300030340322140030368615000c0081c8021104e100f400c400029142079428042900c0c0c030383c100c52501d13042c0d06050005038000d00e0200e615100c1c446c00140385500b45205c145d194000e44003d10300a043c2600e017804164003910900c0314501800f4805040386151215044440c01c2203c001c00794450081d0002c140d000194103008140c403022000070b0040d6212003400c0080561180917591440c119480e164a1545451001e5181c003441c6c0c0406044040b0ba007a42e0350440d5201c1450500514500002c5512034440d25582405441c0c22544031010038252580d00400c54030547c45000201c0d0720450a50a001650125a10240614003210b003072040c0100c41e100306407010005030000c14410030010401c3c074100820b1504250f001d010410101c20124060b0388855007140580d0b407803a00d590212900400a800041e400d01e5044030102d4214022 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 766611762 1250 766610512 766610521
    0xc030c0a030c06180503070605041b080601050a1712090604090501091a0a120f050a020a1e060519031e0501260f0a0f05010618050406050906060102030405060f070605 73
    0x2802c08881034003c03942000b84030884a03400884801002d00140150810400700e40019000e83c44541c01c540a039400a07400800064040b80d203807115003103d1210740c0f1100c010020f501e0249001000b038240d2007084451001643c0f034259aa98030752f03852154030540480e500140f501c031001590020140e104081c0301650b5185409001010100a4042510007181e00c4041034286003000008442e003682e2855a5001c7c0341d03c40c458a07444003c0700310b80324000c0081c420007688d5440a0034000d0200d43c2e0314480c0003403026400103940b1005500801c184102441405080c200c91580b80400f01c6980c01d0119000f40072101041854402c80c84224040746010b00100d81c81c21427080403a201480389409104050b4012441e80e41c2c0c20502000b40441e9010750724100c0050025511628400d108400105055860ba400141d0080e0035100000d00c1d160760300204003d10205000310346e00100c3c0e01c0040c00c400c2c1406030000792684a54051f0038001c601c0003c20308521031014003180c81c0c0c941c00c04000c02c1203090 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 766613012 1250 766611762 766611767
    0xf030c03111219020d080712020403080c01050f0a1a010507021801060305060102150105060d151503020a1b0b0a02031b04080d17010608040609060221040b1e0406020c030c0a03 77
    0x92100c0c9140c3e0b0300036034140300107500000c0c0c80c1300c0d11403280d103480c1415a00d4070300403a03c051462501d492075035001d000c0040018a45c9010342005610300001041e1032810f150080030a10300181a416064142080c07482c100301ca0082c010a505000c0c078169560350641c3c00441c8007030200a51604a59103154000505103500d603001d540204002d80c241d03001081d16140308085c40b1420b00407258083d07400c01511038071500e81d600004107018000c03108810159100d00450f01d640786003545001017900018001314656110b8969181908804d84941800c2e0050319030021040f0010a00080d2607400804548000d407000f00e9041d2000c9a41e43d072950390b945440019840d02c503c5002d84000c100f0034003550440444902c02c4e241603500304c2d9a045115650b6496010250503045000d45045a003041454103031041a160360301c41d030035110100c0720f4074180f43c81e0402028000500c19505500c101c80960a2502c24030249504075800042c003580311026110800d0941c840c0910490440c422801c100c001c042c1c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 766614262 1250 766613012 766613017
    0x80d0c0206011203080105090414061006090b070b0604110d091104051015030903030f0f050f09120a051803150414061015090506030c091c0f030c031112 67
    0x1405603003036600c140d980c0d0194190154900780003e003c5800640140003500f04454540c2d03210380a600c2240c200403181c0555810800306454504000140800c140161a00881c070741d1b0040c94402425480d050581c2c8072820209400b07070116101c1c50b210305c0240c000c0e001007000c1d9840d0186295040118102c6868201d0001006034650750140d030528001502141400c01014112503440849800a00020000300c000f00504a021401d00d0307601c1070115400700c0b03e403203041c014940691001481d03080114000120381070051620025620420008801d03002d101c01f581c000451a0a000d42c840c8d010010340e10340c2a048a5001e50144500c9014400a04ca000d0449001c0c50040304c14403201c12410760026140d00f800c40780d209003680401403c2144010742e04217480e1883c1c0c64a4817214240c0c41d440007581c654415542240d0084010481a02e00e241c41c07a10074500000c2c1004001498007580e80c0e081e4251040c0c00702074284050703085288107140c020515404040c010106903510b18014422200094 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 766615512 1250 766614262 766614281
    0xa09061a03010e0a21051e07110a0b04060507210816030b01090b0307110601091b0306030b1305070305151b0a02210403051e010c0813020f0d080d 64
    0xc2d801c00c0d40b85046218003141d2151102e40040b4800708418548410040c1008902800070070131201b040080902045003440c1c03003032001010100e075030710319080c10a4680104140a0a4450b0003220010010003100000f110212041c030b007461a10340c8800e04249068071040108192034210b010380360041075500a00581c4599900c142a03000d0b8910342000720115081c0348011404117081e03050034030507000c0d100060b551007601450038115401c050116242040b41c281e1240341c0d0103840c0d605a150744034181c64201c0b18610b41c0e24040002c1e03860b548584c25071000203494041044410090315061003000d000d008080e40d040000c54500001505185942e10350480341d26a1043c0c0318071642804076183c2048924200099000386080c0003648982400100e03550080b0768400c1003040000f00048043c807041413607030320b40c03e003034800c0f40d4100406a0a5441c1a40544100030140042080050800d1030721101c240d0191802038040c0c03000004a842c0c0340c1d0f0300b10003400845020940c081c2e80100358014182c80c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 766616762 1250 766615512 766615519
    0x90f0807020114190309110d030c020103060b0a08011703041d010503150601080a05090f0a0305180d120c030512010e072c0904050c060408030a02060603030403020d0602030a09061a 79
    0x8616450070042c0d000d000b0403072601e89020300c1c5031324040e01d1403003508030040302da01802540d41100d442000240f0b010410020840100380a00e90440640d030301441000d00401807981554500740c4504002425071a050080c8010100e50b01c1e086a140a070030415207002c0c10354800031006200407402c0d040d00c403401c244100c0d48039202381d814607501d5818440f24a80030380300c1a1289212500c0d0803000720042d00000340040500e200d2440d48c00c41e5140200700810401e8000d0b01e403039580e03a110321003500342400e510208902810b490744030840003540e00e1701201001c0d6001e103407a4003011168070782250310303100f8100c40e4040322100c0c5002207030a0039521811405110192160b41880c40c03200042441403410914a013242c441e03a840b0007040d4144810480e038000c1c85801662408040d0b40d00180f00c1d60029004010594000304007400401d030100070294100c0000c40045003030503d581d002507020314817040014600303a008004600246134a800030303180150f0000c014000d46e10624070b0901c040c0b8a0380c0c0d0701c2d4071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 766618012 1250 766616762 766616777
    0x2041d0a0f020f0306090414011b021b01080c0a0e0d0809010f0e13180203010c020604020306130b1b1b061b0310090c050d150e070f21090f08070201 65
    0x195076814400c480351100c0000d002410b543e03992003001100e0030028416115043c1d01da2044030200000e1141803010000c40700d0740d60b04585d100c0c10092500c2070807051014070480706100f03440a80e8108040951014003440c0c0341b555001003010803102c0742d0b64400c10981254401e030700303e0200320313001d805881c1c404030a0340d606a0704891158115005030003c202181c111700300e21101c16002d811500611403180e000040d070b840f05481d9901280c2150600e00300034005800c4082071208520b420300150b40c10006c100408035281c0280d4031100034010018106042106040d020151081c0003d4207031591002c0b42d141248911244811140c0c50f40c00c119141480703400d9001350400070b83c07810000d6a0250100d0219044000c0c10404480c0007004085007c0e010f000c8203101d00640101c66000d02800000a01450b50342d4525001e280f52140c00c0141c0007000380310203507529569156212003552140c40340055a0108142c0086030303136009100180024001201d0b6000d00800e00c21410b00602c681ca200707a07115030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 766619262 1250 766618012 766618031
    0x5070b101d0f0103140309030a060510050303030108030d05060f0d06091103030a0516020409020d0f030306060c200a090c02030301050a06020c010c080306010e04021b010c081302090a02041d0a 84
    0x1c0440a0031156496001078040052010560400aa410503803807502100d242428800010f4500030010008566007500d400412240303c8420500034000d190941c020740c119410f24a205440e402100d89a0b481903a85e8400144607a407000c0074400124006051140d440038a400c1c00c2c0043d20100d4019078140c4100180c2c42d125080020403140804141da44282c01e00c0c1c1000c41424200154007810385e80151100504805a981d4850401d0b055110380440790600c03100d854064107960181c0d0210302445418400740001c2103039161000d810007070040c214050020b103c2c0c000b61049031035400103000e4510741001c090a50340c00000a506803070085411082c80e030350300c1208903556060b04100c10700003440e16000000051611015642001c41410480b100010a10114040f604002010204289602001e0380000c0b03080c0324284100500d46404081132401c0600c00e090032501e141d009005402c0c800029042d03682d10750584010f4601d41e50a44454005c000c0c0f03c040c807840658141c80c405180c0007800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 766620512 1250 766619262 766619309
    0x12030e010c0906051638070206040b0105090402040603150b0a170706140f0a03050411010315061b120c0c080604150f0209090f01141e040c05070b10 65
    0x10011a19580c0e941407401e85c0d034031601940c8072588542159800d41c0b03540d900b80040b11440520709a2503120030443d0300c5000076030102107507080140030707030302590080410b00022540c111405815030f4800d41c3c3c029401d403120b2011a00820a0b41c0c4090100c140c100352008004402e504035025000c41124424034254448648030041400064554040d0384030b90802c02c029801900700c1858501d11402146c00e08403150444200d80c2d00c10000b81c00003d0352401000104043c15104c00d40358034003031a007000004519108409520500d0064206111742242500501c1d49190300c482e1000790300c0010000c842c2e0003e50054025405840d003200c64015000d0085211070000484612542d00b240d080c072071441e1300b0b09c0f80d100106925123032000919003c10000071142c48100b100c0c3c3c0241c0001c076a0074490341c034141c4052803200b03824200600c9100c1c800308458a406841c10315602503c01100c00280051020710151083c0c412024003c00d03941c50305040000c207404403a5044102c413840040c1d05005015410003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 766621762 1250 766620512 766620527
    0xa03150b01080108101508100501060306080c010c030e0f0d060e01110f041e0b070c2610021312150c050301030f110303040b0f090a06090501050307030e0a12030e010c 73
    0x28107150b9400f00704000040005c2c0c4d0019002003421725850178480d42ca504c0860300b000300821a41d0402d5071213100402c05507916200d2031f8014400740d000b5200914107200000d1103013900f81d40113010810a1a050f407100d5030f40f0150b40c004100f0042200c0401c150628046000e8550808408019460074102480c8111090222030381c1c0050700c2a21440c2506007d41050180800e0124040f01403240170003040b8940301c03d00a01a144c081e080002e005407030441440071840c110980406082042d1071101200d0741c0c006000309045104807001750f01c3d118504003408460885a00c104e1550016125006c20311400540301e0000c0780007941c0c1030055a0084800b9189444280300c0109803210700400b02c0c0100d600150313928034003540181900c2c64290b4402d41000c0d01e400078106403028070720004180c00b4514240b900380c00205114100f02086528000000c1e1550100505180c103054644807440030a2006101da000340990104100b100c1d06030b400310007401000018041c001d150b1a1201100189000340709 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 766623012 1250 766621762 766621769
    0x20a06051c020c101e1a0d080f0d0908030403141c1805010507020f15090303130507030f030302040323030301060f030f0507020d02160506030c07110a03150b010801 72
    0x10544007a41002480ca0081d406407202d50000e0103403107500200b003007060190010501100325440030a94140802c60100c0f81e22240b401882103c0c40c0d90596262203103403000c80303951f80185069440d061881c080d188188103981d0401700b242c0c9040348003c10060072070302a501881c002c0c1c0d02c00e0350814004144056512980c03d9504402803402141d0707282600c0c0d604105e4186001c5154540f66800c582e5030a42912401c0e10b0303040240e0060703000302100300420000c0c0c103080d000981c03d10030107040c400050741d140c0c84013801c41001d0030b44282040d41400b8080007001e0003994040e90341c0c1d003180356604000b8020b4103e800300300c52015100c0025a900e400c1e2034003607505c41c0003684c091450b5900e8202c00342d5544203000c07401c006050729031000c110110075134480c00d8454000740e0050a03092000fa40003e091032440180310300c83e0180c4507010300003034842400740e039445000088090f0756050386060446450202c80b5a0035488010700c0c901004004201c84801807a5544a10a10001000c81d0056640e074a0901 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 766624262 1250 766623012 766623037
    0x1902010209150c01150f080f0102070804030204110f0d060e01050f0907050a03150311030c1206010e100323010e0f0a021e0a0909030f0807022d010603050703020a0605 73
    0x30354061110042c40e0042c000c002906000284a031171084190b01205916806007a80e4080c04074200907501060010300041c0d41d100c2c00071031610f0590b64582c80c440c001c1d400040d028035543e02001d042c4210030703012902080e4240c0c0213181c82d1406004040c01920850241c01c60000a1900000e50350400c62410744980c5002000c0910030f5440c04070884194106910034001c06489400800c101300d441c02c0c4510141d80a600b00c1d141c600c4485061500c1c00507031020850180c490011240e90a000228042c0d0559110000e00303103064403600030301c201e504070942028082040c5207081050381c1c40b12006481070400148028080110078048880c0ca425001000910a8000c0c41c9080c00501d030948a44035411000c0303014012000072813011a4010310b05410940f2040c1e9900d50940901d900600078240795142c0e40b92211b4a490500313002512060f07590345101c4020a0b03006514101001c8a2402c203283d1921402002640e0303036801c005527164060300c400e071301561081000cc5a540d05c10421100c0840c042d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 766625512 1250 766624262 766624279
    0x70f142b022701120b1513140d0c0b07110a081501090c090605090a1d0403092304150801050916080106080d11012306191a090f060d021902010209 64
    0x140320701d801611705000e0b860392050380c0d0805004981a1140a001450385951100d04028100038070380340709582d0074403090701c42c4217608500c1d400200d6648554003079030300f00e01c01c898841c1018a084460f00580e02001540044803c90200d00c0100014229001007414034401c0702d140d81c0c440c85030003200c0341c5c2c6440e071001030010340090103040d00034002810301c402c01500031b103902a5a240080040d624507004204081c1101d802e20082c07650042540003c0d04e034070301c4600a54980300340101c8051211301d807454013640d11048560030b881500301103140100741c103500070300c0030b45010310035161205120b035141200c203c0101c402040c11841481036400307071000d0f20010000c082105400340c90301c1042244090301e664a8403036140014040c141502a07480780712402d41810b0410504000c0c40c41d21380b422a48204e456140e00b0009181e43c8441181c604406541d820b070b0b16020240855a14601c1841454101c0000205403034015050b500400d12a080094a0b003010b0380c1042e0b0803400d0307105000402e680301001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 766626762 1250 766625512 766625537
    0x40308060f1c02060903030c011b02030c0d030f0b0307030c0501120630140109120804050601210f0f1b0b030a02030a0b04091a070f142b022701 63
    0x90001001109000074440c03805c0c000c000c00040e285600501207402180d444169092002044060f40c046040c1c29001a50030000030102181c3d4030050310220204160b1680700c4d12003d90313200e078000c428150000e81525247ca8070f034242051003650074400c1600040f0b10032000201e211280c4960400c0d0342d02da5018000e0300704001d0140c12000c0001500ec94441481121000016240440000001c4160380045480651405c0440030031001da003031a810f2061f10010040011404100c45054030356242040c1010701d128124880c40e001040c074028400308450070000148070806210251240c0302c1c1c002c6041404180814071805090ce114070044003100b400032614005140c5c001d564040c2c2c03c7c1c4800108042583d0000d003c0da050410259000c01c0500c041901c003074101d00c1c8007584003c0c01c0c01c6c40700c000503200c14010b05440305051401c0d462140887e00560a13800148010a0f0400c0c01e044180b8691402502e080294454903800030a400e00c0e80043c040c503140c1c0520300c116880140c4500c00c20005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 766628012 1250 766626762 766626799
    0x90f051f0201180b010303200d03091106040602012004050a1703192708030d09050a020406260601060f080403270e0a0b060715090605010e040308060f 66
    0x10991031a815075480e0410300d00145410200d044160380641d60b107402552440c00c0181460484911001d80b4002000c1018518000001c00c811944041e00e40066003943d45d0420b0700c00b018000541d00c1d80000f001500240381da0341500400c1ea1041e044002c941034414a402c6294148107a01ca01600200301c14010480500031500c01d0100306144000c4c0c91900c620680700012241c400f2441c80080b80340040344204ca00065a02c14507140f0a001a20040a04080c021903907405064040c0c40060b4491600000300301d010300c8200c030071a5002c2c0040c080c0e80e0300c85480e6543c0030400b0121046203e0440ca50200d441c80c0011f40504840990300d5900720122103c01c12a080f101c01401a001d1000400c2140050100300c0e5045502c29104400c0042290178800c8250514501030106079126061004000095840c04200c904881e404003040150a420480701009001c0081d0060f154614140000075800444072040340f0440c425565005941d942804020044000304000d41d04102110804000e048 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 766629262 1250 766628012 766628059
    0x20a03060f12170c03030705180d0b13081908011d0408040303080c0c10020c101506050714010509030d0b0616021009050913020a08030a020d050d060302060703090501090f05 76
    0x48101c0f4442e241128521055143d50b00031b6480300c0000343c0000703800010000c4444131a1102c4022100901240d1264603a83c0d820000a000d0701c94001d4225618410000307a007044400c0b02c4001c02c120780d9040c10000019190807024803404002e10114502483c0b440e000020f1540314a51100d0154101750458404a4a2440003402520801b008005c44411014100002d000d4862800c201503641e00c0c1c0205001d00b4500d25030303002c80d00281803001040602d0700704221603061711100c0c94855110100e41c10311803a03000c5402c2080c1810f502c4c2c80248407007141c1c044018086601c0108062000381340d1001400060701c103408211054024103010100140b500e00040092010245860602e1644030400501029000d44007002807000c6450301d0f20460500c218100001c1c4031000c061424500b1019029449100d680340c40740400c80300044240d41c0c045564451302c0650740140115454a00a14010381100040d004250119590140002e410716006c0b400e6001d41704003400c40c00e0301d0540f0058a01518 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 766630512 1250 766629262 766629293
    0x807050301090b01050d02120103060e070b221a091906021b060c0304061805150d0b0d0807060203090f1b040203060f15030109050601050304030c111909020a03060f12 73
    0x4c010001006c01e01c0d040d0000d44980c405070001d5540c154590300d80b007403c855551070045481e400c0300204021141d1800103035010110140030201901001c03e00f0441e1262298009140e170481008000c00381510391800790110701d40507148e0560310207030700341c0e0301044681c1e92251100583c86110a008003686580050081d03030809400c840c20b0031004c00c01c0a003036410036040440051421030400d40b0180d108844600100b4040e00c2000702e06c1010304a401c60b030701c01c60040e160001d443c6da400000a80360110b21284064120340d40b6a19503c052806030065407042d10600c213148a00d01041c1e8001f0000704442c0d4141020511101d6050051014031003e50001401d26034028680c5002a032240c4950100321a0550341c03490590303896041a10480031502c000d080f150400200b84104000680c11002c0c3e03e003050780001159020000060000381025000644c124041c6200100020194440d8000d403c950b040d03500d00317200c615100d8420718000c51291094031203000d01d01c1c3e88000401c0b92450b00e540700 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 766631762 1250 766630512 766630517
    0x7120810120f0803010b070213020301144f05060f01120b100f080708070c1103010e0a060f0b012c01090305030c0d030f1803111609060f060807050301090b01 69
    0x100d20325a2203514054000746c0c0141162400024800c0071440d20b0407600c102d000c18a0021419541454170701510038200360566802083e030308041c10510007030703560840300c203a885154000b0040840740f001060403440d00f0a140f441d445011990440c903100307000c3d0328480d05c8041c1c0240464101200112400c64050400d080c5180d0750f00d00c0f4901e25141e26001c0003380c9015150403108800ea2580200900f80042400007002a002c05001c2c07002d52100010700c840d504000030034580c480c1d0000017401091003a20b214194031451b0b5140c1c0c2048426005034119100c820400c001f0109413200640304416090981c107100345181c03005042c039052819071084044e006141003116030381c4a68405140d44d210440035269a4407081e0348981c201d50501509180d02038400040c840f01c3c640c0e0039540c0d02c00c4081c00e80201403222104003000c0304841001070003070f800040120b803000942d0351007100c8010700484c001d001d50368500c507601080d1a409490414041c10341540c9040c60b5030300e8150342d14003c1100b004800d04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 766633012 1250 766631762 766631783
    0x90e0d0212160b0c04030b0c0a0906140d0f0608060603011a090a0608070905041101030605060d0507020c06120f07020303072a0209090309010315141e0405010602030712081012 77
    0x441d10b949146407213020241c809598513400c0d800d083d080494028491000c40604000e0100c0565000d1004000c0311603506100e00880d201c90012407490107403a418184a41c98030222045201c2c4030f0300a10115103001c029070700103803120360616082c0e500001c1da01100d1000c1400e04a0709013066880294440c6802c1c50010703a00f511b80b0a4203040480c590b05c070498047d00d8000340070a00c0621404203602407800d00301040018601001309405000703907501d43c5402c0e90742c4e0000868a5001340b1a07802c1101e0000d044aa80307072040385607440703034000070740e0170301419004000040d00083c00001243e004081548404035110651414502c400c0300c4641c50180c0031540d19084030058641011541c002d0b4030500c00703140c4401c0340c01c000508032085407207422240420910204150240c601403100c615078142c0e00f03580419645520000b1602c02c003003283c0e80091901d4000030300541d01001030080c0358890420000b840c00501c81c01c56403404103541700c84034502032402c1001552040394a8541c440c1c8254420003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 766634262 1250 766633012 766633057
    0x30b04231302060304050604051c08280c0c0308010b0f040e0406180b0906060306060a0b0d0b0d0602121302060a0309212001150b0c0312010609090e0d0212 68
    0xd0f140c0c0c00a13281212a50700c080180800c2007410f00c100009502d451071303076084214200100034243e0308003602e1401c04003a070081032640080b85100380d201c03a54500c5401d226880350744078020320002c00600c1c2a400610340200114070b02c0c1c0044220b8000d00320001d0350a003070a0800b002da050200c000340c021100a507440b0401101c08401002155240d03004054103d010310f00410154200320004014034030a8010404000040e511001500c09a444272820740c1e449000d142c9440c00103100308440541d10120b08400072007003042d260001c140c800c00d00e0092045540702c0f1305200c0020082c41500950001d410b0016020702403090b44050680c42c091030005151800ca010051801c0e2807000c405d0000445400c18602c01043da2000d04c10010082802001750500c200f5501c0b070b079403c03d40120840c5a400207142840f0200c20010744002c000e4580b10300820b540d407180701609a8460340b00b070720845410201a11410100410510701301c09441d00604501105001042032540c0004c61552188039120b00a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 766635512 1250 766634262 766634269
    0x915030b0f063120040312020c060c0c09040303020702040504110a06020a020f100908030408010e0606060903030316030e0d09091410030f03090b0a020a03030b04231302 74
    0x160003004492801c44160074898144881890142c40e4400c0200030380b58600845510702c110503420703c11039403000500a841c00094001c0503000c02c1c00a5070340c000800d0100030b0000e0701c6456000ba020b00e80880f403802c031054040c000c0d039000315162040103402071200c00f04541031029610b94482d10030b24005140040c07a42c00501100c000703031000e85903040b070100c41040314142041004054080c0f0b000608070707041d06500140e0a440000d902c40c0c000d00074400b10390711040c010900c24010b004424142e0b43c681d6150603550f4020f00341042d005e10325209080c0400c1d4a8101b40f8100d50034484086c01640c95651201d07803480c00540420a0101016500c124200e01c01e1014070040308600b4084c1c0e902000c951600703260000741c420584082e00030034030200070700c90004503c511500c116030784451511560b00c0d40e41403d84548202ea4400c1d440c2110004281c14620780c0401c01c194401d00c070f82ca04101108040d01408116842125102c80b0750f0020401c070003c0c40e490515045c0d00000c000d000c60700c54252940030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 766636762 1250 766635512 766635533
    0x30903140717031206010e0a0902070602210a0612030f230c01061e0f2303010603030c050d0908030405040b19030c0e0f0708010b07060e07080c120303010e01091503 72
    0x46600b16007000c84c0c240c807000011031405400c0002482c3c0b2075200319011000910300384481c42141d580d03646c006036060802c404c2c4d405a403200b40140d00155001404041403180303071017044440da07407401e00e007510200710154540e40440c489501550740ca07015013641c032400c0c0d036461090040c1d000342a044181001c050700e900401041c40c2509080080f869518058220888440180d0340da003541c00384200510242c80141c0141040b11105036071103c0c14140220003203071100002d00f0b07290301075080003808001c1c10340003910a00d00a2148040310050b40c844a0203d841504c41c1c0142c40c0c1540041204004d0780c078041c0c004000ca610000c2003414070045c8400032001400196004a440030441c080030821040801c140742e41c8003c8401c1150840d02d44000c004040c510f050003003240d50726001c00e0320400d01000d584011103090640089510240c0c8030724a0755594124444100d10618132851454410b01000c81913904948a40144e50710907405c02c1c0400010700b105044804441d5041403000011480301c122 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 766638012 1250 766636762 766636799
    0x108121c0c27150516081e0d0506210a0201140d02030103150c0f0f05070c0806340c120203220503070e16030504080405030102040b0306030d09030309031407 69
    0x4080d00641c0c54450003d100080310302a081c03d101050214000001600c031450001540c8003800c030396120300c540007000181d904480d21003105000864010030008596000c0740c0640000c4450012002409048201c80301040030705141c5038105c40f40b131340015401003440c1251070f03d64114041c28403803055401c5040360402d0f80251003041d8140006803045006120300c07500c10825181034110b5001d40e140240c02481d02500120800c00005104c030140410b0401002c0640284000d03540c503418181c103051036010b07074150038550a00c42a0780c042003440b500d40150320b500d800c40d103494220202c26213504510749030090801d0150f001c1005190a051040b84210500c25808038900010906141c241458a102a000060b0310702e09a000c0c01000041540310a1900c4600d290110710b50f5503501d8680c60500640d4081a0150f002141c04a111403c0c0009144185400c1e401ca65954107442c10456012050f8840a40440c620f00028408255440d101145048400007100d06007a69401e99024640c074500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 766639262 1250 766638012 766638077
    0x2101b08090a1e031b090204030302010f0605060c120f07050610030b07080c0d0c020703020a0b0d0e0601050a0303050703020a0c0f061805030304060e040902090f0108121c0c 76
    0xd14045186041c0b2100c402400d00c060b10040600c441d0b2007a00035143d480d0001408210b01440c03040700d048504400400982005001503403156500c0c03030040d0203000f40452555a16007007410108050924005856422103140d009258896112008116540c41115481c0f00c0000402c02140840c0082051030b02416010b406040024a141009055580050801e40401180c1014015103c080700c0664601d034000ca0000030f038150780114240c2c80c00c0c28a9100942210000c100041c1512042c0c01030005041049011b010780030701010504c0d04c50009004055203d02511018404a4405e0014040142c401d0040b0b80d075210080c1c42c3c51900c0c0d9500d900140c1c0806005000303100e0b00741d10503104c0a958982c030314860302c020304000c0000d841c0c4c0218001c00c0f04003c004e9088050a568681020710160780141506603181405400000b60500034040c1115074403034074500c107035039914072022209080306041c18405421a040c5283d8003510440403048200411011010403103000305401030307031808868 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 766640512 1250 766639262 766639267
    0x1c1e050d0e1e010212040212030706060e090c010c020a1a07060911100e09060907030908030a0c0e030a03020d03020711030607111e07090923150a0c050702101b08 71
    0x1e264600d90ba410041280c060b90041c01580d1941c0da9100da4a0380280e070480d600c9a0780704401e501a40ba60058510181904c2d08000c0c0c0015035540c0f0070b84003402004024207496915100d8401900d11240d0018025009800001c0130850b02181d28109c41d01c510b28061210710701901503c0f100301761150004151410352030817050591616015803080c00200c11801c1101ca18450000002c2102e080146024043c000983c0012440b601ca9401020035a600c4498140c40741085040d01004002c050040f0000c01e6006002c01e06914000440042c025490703401007047c41c146070012006908101011615804009a0307882071b03582c24012244145c00660b18918500d01c2c0c9100036142210842d001100301c0405101d607212400003058940030f40d0080350b804540729407280f0b8020074030341c0007021603640b901c00301e80c040c4080b0001180c8080038040300301c10b14019840302050041110981007030100455000c208240050621a0b1a04444505403c04014107450078401b5002c0e1690701803702d0303456200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 766641762 1250 766640512 766640533
    0x91203030a052202120f1b0f04060f061b0f0f110906010c0212030405030d0c03021b0a050f13022d07022b1704081c1e050d0e 55
    0x18812194402c1c070301126095103201c410b041200500f0b440308082c2c01450100c030003240f80c4000300006001e40a4046c1110040c286007040341031096a520210b0f0300c030f802100655034641c40c1601480b81924014004d14500510780b190130b444407402c1c80c00c107281c41012860386c60041070000c030312102c101c1c1c0a016041c00100492070100055444126440d10401030201442400c0c1d074003d5012078003690650700d01d0520030644000303600d075009681c00395506100360f003800c50110741c0c030140300c050f8940310390202d0b407900e8807019030620380c984200314442e08011000410030407442c00d02e04207c00c010b0054180c0c4090140840e1a4003a680980303120440020584200c50f500781c1d602264840c4c40e009207282a0074409036038000384a601c0c450785401380e401c03250403000d03101d807003544842c42d22650300c02c1c440031100e0b090380d03581041c5030401c0c810003006025080c03103c2c2801d8212044c4480c4401d040d641e031121100039000c02c0a070146020400020800184580c000c000d9040c400d44007040341c0900101900c05d81c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 766643012 1250 766641762 766641781
    0xe01081b31030804270c030b010809030301050d0807080c010f060f06050316111203011509092d0605060c150105010c080906090d300e03070905090309120303 69
    0x282485001d51099401d808202180ca81420b903000d44044c0d000c201030b070b51035030080c2a044151030310101c1700742458940400081c54040c0c0c0481142102030720358004544d03c0d04941c80d00d1780800d02c0b03450b4200d0282c130035070000504400001c00382103218400b01c43c1826088101c690031580d600c168000381035600c8005020300c0c0e446150802c0245110f1600600c0d504d8980901c0b09804d020607044820f00c141d0349402001d895040c8419400700c02c2c681001c503120760b920307420400c1d50032500c5504008600801c03c0820707401d005020344070903c0480d2084240c0c12200410034040c0228020903085455070f5a20042020b5031340e01e004043d00c1c6000e800800e851403102d007407940541e4041e4041070501030480300b1140040c1d4108181d89003480115603c1d40c59200c0000401e15224441000602c01d4108110784092a808900318018103800f41400c0d031304644000509075409103a0b402c0c00c6c0c0c1e060744101810040c0d1242030304001d900c24031803000e0741d0811402c80c1c0412800c000d43d0002c030300180c10110401c0405403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 766644262 1250 766643012 766643077
    0x8010303080a0204030309180e100b01030f0c050306010f18030c031b0501020a06090f0b07050d0c05090d1103010e0303091c080c070206031e090307060506040203070e01081b 76
    0x65070b620114034051030340e83e0280c100d03503c80c03003500204803896501c18200381c05907007d40d4500000d079050300c205008280c00703070000700000d440c180c0c0400e192400490410310b403403182c421600503070b45501703140d5143c2000548012004502030360810290049090300c5a6034cd62441d03000b544070b912422a81303404c515110041d00c0e0088240101044214003c011903a400100c0200071908a440042e0700e40e114141000d03407404e404005000701c600c0390300f40702c4520b03845002000c81c4204003404021070ba411017011211441110909588154141060300214107100721070244950010300005491b00f0001c003490654004a400c074a494121808407509451401c0031405130303440720300e000c00c0c81c0d1420b018080414001c0d080040d0181c00040b002880c5801c0d25002d07034041800d20501c50f5010318102542581c0d0f940001c2e01102d0190900000c0307441d60038903009807400b070303c01512040a2200080d00450360040000c0c40700d80a034190105400c5003019590003854a11040103110790b091414002a04011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 766645512 1250 766644262 766644271
    0x20604121e030804030813050607050408100e100b031c201903030f15090b011103070f060207021507060b0f030d0f0f09051305040303050f010e0411040216030801030308 74
    0x4244000076100043d900a900b641e01035458104051503071030314a104402400c0c200310081c070921517401408038880c1c1110240048500040481c0c119a0300c550040090b161006e1001c00c442d4407a080c00300c80c020f4103400030700301094058112041c0c168040c900982c050091707007140c00030481c0740b035600d00341d000580c0d40703804a141480c0040040340d02603440c14050b4840b0b41c0303001d010550703190f14040244082e500400e0090317240180400c2d207603450710840f030000d0003900c5049010904140805e0b49082002c0f0030783d544d65401a80561080d90f464880402961000720708913413180c0d0724407100102082c4080501040d40c0a0580010031428031010301c4400d4174002c0c0b030305100340d10180c01d2079090b40c0c2c4085a2000d5003520301d0300c4031195210042c06d50384210030b50041030b4000c0c060800c44000390620360101d8407582c000d5406018584074a03800205400003806031000c0140700700700140116030034035004010154040d03c01482c100c0d04106400107007034a24130850000303044c82c0c01003040c580d0295189400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 766646762 1250 766645512 766645553
    0x6030b061f05072301050709080d1119031416020f09060603242e050304120503040309030c080c01030506010e0f0910120b101203141602060412 63
    0x412001410207086401640c03070044c000222400c07040d0a0715540d18200081d070900c5002070040b405c1c0502c001d003140c1d840340254131040c0300382c03120390304682d1007401d1402004a010000d007130f03803400001c40503886882110741a000d0104c40d100c20310030180b60500400d070700d000400c8514145180361041002001240046a00c96040c24003800400e03924501240d4000102400c52403145444c408501e0030110104012948090035500c0c0381910644103007410211015019504a910081d14080c0d4050200390350140c4603c58003440c00d04114005d1008680040c042d080952565607680d8410600207040e8100704400d400540d0480a80e50301402510b8004a007400c1c2a40030b9003140d008100d40f072510003001c1e4811489180420115107004209602402035122000c0f140111414000c001c1241528044d40c0403c0026002a009010441c42010036605a4503034007402500054002690010040b00c0802040c24aa400060707403030400420040844141c90384e0124007d05141c89841c1c12051030740070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 766648012 1250 766646762 766646809
    0x70f06080609180304080c04050108010510060c03090b0f0a030506030624010e091015110604060b1c140705013e0106121103010e0d030509010f06030b06 67
    0x5500c0d08085100e902103410795085049585604103a40c84008005007401d25000c0013901041404c80840c2e141d00401c42502c05100030303662042000d00300c0750100c41607620543e00c0641446060b20501030303055281e0207481c280c4501a1a8444030390700350312000c0300356030b003d600103450414030f60503000701584280204c0250801d40b4000400c46482e400a4039003141000c07442000107543ea020b0000543e0020307010b4002116460f03c0022240c86860754006e00d5103d041c0940151660f61060850200105000002d0040c5444139650600909980c2601607800000e24002d5001915000e40c40c0801c18000d41c1d0540007000f5418240342448034035003120b0704201440210b0207881001402c15101035595441100340510664003d401c02c2d40101518400e035400c01000003281101000f603c0d0415001c2e88815841e00040030030103080750442c2544036001e8002c0414601d81900075400194405048000850004c80113030a020840d903c9800031a0300f01996010300406045c0045050401001c062113a05c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 766649262 1250 766648012 766648019
    0x6050f012310030c020f10020309010e0d020309010f11030c0105011a07080f0a05130801020d0606030c021e0708070810050601030902130f0207120e0f0306100e040218010b0c070f 78
    0x604041032807540000f8903441300caa000d8540c1c803c12501c01d1032540c13002514030300ca8a010491000c1d41c0143e410207069824980c0d01c51282101141c42ca42200071500254a080d580c08011b440c41d5204000040600144006815417100c0074001000c00c1c4032411f00000d050740c10814010008600c2001c03005480c40d080c44400001480c0c4400c1340e0004040b0700c041b075100c411040b8212647d01c503004a848000070704420008079494150090034010006c0c1e8014015180c441a040301150104040071005a224034610b1a140d44450308128004d6105003d0300e5038161500105850724910350b02003809a88071307403000320101185102d07030b41d042002481c1c24010a4402d8000480c10840000810307a5030b561440c2c0e0814403d40c942c1101c80c1e60344d0000d0503c400051224000d441505448401401668107952084a0385000314000381302c0c02194080e5100d2901f40902090580c1c002032017241c00404200e070b0000380d080101c00e9903008020560f0110359541c550494142801829405403400042110040c0b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 766650512 1250 766649262 766649269
    0x302070b220b040503090d2405060112020304020a080102030907050a1401050f0c1006060c02090a0504150902011107141801180908070c060504090612080d1806050f0123 74
    0xc603551504103054040b00d8855040550862140f440c100c3d51103051000c0c047c1c00c011440030000c05400910361011a61014150b0728030035a40100d505a000549200d009001e501c181d03800740d034110340082c0c082800e49481d642c1703440c220703071003500e084a160740045010403035803400007095000340c50303107080c004001c0c9141c4c0c00280050013401410013900d240441d4481c0031001c00c000102200300880b0301800001d5555601800d010443d4800b0790050204070000340c240e1109006407070080340c0c010400861020382803800c1c030040c080b02da012410802c2c1014035064244080201001415004010454140031901007102980581c000001c480403a03034010403821024549401001c080302201040320285890100c40510840100030301410220f0004074136241d0001c0500103079210048104a01619503400319512070740240018040c45081000302d1a07882e168110030402080210004482c89c440e42d5a10b080c0c49003220000c010a0b40e000040010048040502a501c603c480c0130003008079006011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 766651762 1250 766650512 766650571
    0xf1a0a0f15082a070618050a020103020307020c15120603060415150b0a0201050108071a0906181203070605070f0e150f0d0603060b041103010317070b070302070b 71
    0x1e0740240a001c0300007070b405010100c034a003c29644005520031000c0a0142e24480e60000d50b02940c002e850012140c220701d80302c441089407030f5040070082842c02003550046020703500013029081180103400c1011490784400e6410721400b0b80700114503803070b00c02c0300c4922500d1200081000340f10b90b01c45030034072002c1804042003021003580040d0100780750400d120380d010b480c1201e80c403c280b103440014500d04090b0f4194095416189030702c041e5559259600c1d50b10071540014038413001841000c001e44030700c1d49083c9000700320801c200260081c1c00d0460030006240000111820101d40d000040c0b44010020a071017900d9201c81141800ca40e0304400c150003c08402400c0b10183c06000010b81502c050011441a110001812900fa555821076007840300003400140c482202d00310308101d060105894640101001c2e84000c98216003160f02e1170b25020304031380d5800188a804d42c820080a0081005a11181e2144015071401350b55010945846000c00c03200500712080c0100c5282c08900c3e01220396078 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 766653012 1250 766651762 766651799
    0x41503051c1407060908120f01060203030108030a0509241c06150c0201031d0d0e0a031a040c0e04060605010e0405010f170f0a050a030f050a080414010f1a0a0f 70
    0x30b0311500c6003040c0c50018010940f003d4041c000e10b201054030300c29403e943c01103501c036400e0f81504940c1641c1c0c682042c2d0b0340340028007644655800a0085040080c0302c1c0b406400d4605005200310b00c5c00b01110360485440081d0306042205807000912a40c0c100c0030f480e03541102c144802d0041100614080380840c0c0c0703030440c241c000100b012250050003507a200b90800c280e08102101c3d40320311000d5107103d06a5509580c4d0407403012400c0c80c010500c0901d8a040d2000c2200d80002c842e50080080c10700c13146500d04000c100300c41030500d8000c04a400181c0d000d4040c811440703141c000078107900b041c00141544100824282c41141000010700c03540e03003900d02c420200d41e84120039412040f140d6450b40c0c10704142c010074412500c83c0c000c0c154180f280000b5100950380c06030311100c84808140740100d07820311074100001c2c046440322000c90002541e1500c40b111054652000003458082c803c441c900b900c25a901c1341d1005a44400340f03003800d1a00300c1096009040034034511901c0e40c40c0101c0c00c1c400900710388 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 766654262 1250 766653012 766653047
    0x635010b0d1a211612140f070e073621170705010c170c07050a1101090302060c010b0111030a090b030402121f0b0d0f0b25030903180b0d0f0209041503051c 68
    0x10110340010f0080c801480c226058041a44403072140384a00c0a01102644c0809000241c402000030158520cd19400700c1c01741c1170748401051344440d101da2403038010f200e4450318241c01c10401c07400440c0b02882100408001030790b0700d080c0004c0c0f0510b1314140182c0500070500d080c0041140c00005100098541841c0307138850254001d800e02c0c10010b03501c41083e80e1002c0e41180d000075594085140660005091030801d072a006c07914036000f005290381e80518046031010035141801406800111805550b000b4030041c10792183c0b95070a500a8188000018004d01114101a000b540a10103001b0110102d0040e02e002c0c2c0041c895803103030080e400c680c00c0003906590340900421040341280303440c00340100654030081c1c0a00800c644c01001000205000d80c000703003514030040e070a40218211801212401d103080340c146450104004000d10b16072a990f0910340d030820100c44031303494600464108844140c00104003d10b142400340c02c006031800c2c924181c02005030400c00d240c0c0c010012098401158 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 766655512 1250 766654262 766654289
    0xf061003050c041a070203060f0112080f1605060f010501022404080705010204030b01140a050a23041e0f060635010b0d1a211612140f07 60
    0x11000301da6600c19504604c403401207500c0c1801c98191440000c010003407003541101c03826070341c08070022280042800350145514054100c540070802d03542c06070049140000c0c140e85420f00e4082c4440800180c070004a410350403240c10400301c4820808401d0042c8420f0000e030260b195001c04204e80442c031410030100c5d1900c44000b01d8184400401030303480b4180e008008540c2c554590400c161911024800d0004451440cd2056400d081150503001142c1c1c0142880200c40d05240c003401c01041d201c0c0003413480e81007800c403903d07807513036a406403408a10992910b68001c007200d000c41300654001c55040c1c2c03051801c00008101c4a60300c0740c10081c1d490b0100b00711034a0070122a001e60003941c4000c0e80e4240e800d00b0b00002040c1890840c00500c084e00d0b114000b0840038100c200c1c0080e140e8241950143d020340d2403120021054007099100d92054110004d03a08000880002c282c10511540c010001ea070700041c1d82c0d0000c0000914800c580101e040008120f240c03c1100d582e030b903c0ca41401080a44001c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 766656762 1250 766655512 766655521
    0xb060d0305070b0c120726040809090a0209102c0604030c0602070f0603090210140405040515040c021c0f031415010f0e0d0f0305090306041a0f06100305 67
    0x9103042c0d486072940099280700c2c41c20411030030b1180c0c0d0841030910b080c081d00d0740046172050b0b00414a400f40b0440700400c604c03107100740100d0104444c000070320a460000d82004802c02680d6400340d26441840b03011001620b07280000240021500c11400030300a100c03000300400d41c0345001040c0f0722400d0307017152201801d240461003c40c0e13a90040c0d03440100300d45004903010400b203170045a00815191440e6203101065500e09044059401520307000c0d4020380030007118a0003921034901e41da0a1501001c46a14240e03403400440c086030822281089981c9014074a10007519150240f071200004620092003c0c0444c0150040070b41c0c4405142018041d40e0130340500694004e40090304440703030782000d200c41440c0c4000c41200d0305070100c1450b03000802140e1485035060054480455440d03019201c41c1d040c050507a220f10030304540140c00d5040c044280140c0c1003170340e020841c5074800c0348940c501d440801480e004a030100c0d1000b500f50011032024004100280c0c96000030390901c24441d00d00401d56446 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 766658012 1250 766656762 766656767
    0x807030b06030a081206090a23100b0a1809091707110d0f020a17071205070b1c2f0730021b06091009050405040609020310090b060d03 59
    0x900d60f0010b00c3c0c50008140c05600500d41c11500d48a0601907504202943c0d600355118211031000e01780c224199900c07803050f81100e0010100c40d41c001040104921400d032601324800081c0c014842c3c150000b200180740a001550f1003980400521042e40c060001450a030380b111503584176141741c0a1a0340c40451a03005108801064030081c02001d403410f081003042e41881c0030300c201204030503401410307860400550602b003d0845482d00000c1c2026125890800908c0010000810016221171280d400003150b004c0d0307084028245c0790400031201d00e018407003c1840081d65558616800071241101c0228032441000c10401c4c3e00c07503100c42d00076a0f02c003004e01d04813024424102c20400f94182014a20504100c428281400030160f0b400710740520071860220700c103003c098a42150018000d008801103402c2400300343d16092036a0034420586a15000454210740046030182c40441e1a000da4a0035420141311461101401c0300080c000e00c1584e4403a001c07040d2003c5c1c07205014200e5041603106052 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 766659262 1250 766658012 766658023
    0x10b120d080a0b060a080702240c0901031b03050612010203060609040209061207030b12060610030507050f0a020109140303250509120d030b0108100e070e130e01150807030b0603 78
    0x1000901355919142c400303034018005001110b8500240c40b507050881c80098401070494940d02c168511280d480e0ba51003404034a0360040d40b441810b040c0c03101c00500030206048141c140354425654001824902101080300214038901022810792041081c8a00c80c1ca80c5030484042c59030a680c090f94428000021039038512070401c8001d00c1c0a11002442052941504920000602114141034164044c0300340e0b510340074241c03586640302e2800700f60000b800340683c02483e4484c0d0107080840c10b00c44280302400c140e500c03441c40f01005075564002074040020420741d1074031040100005505525100d014051261500c03030090020a1610525000f091b00c102c0c105c506002010340900300c00c011341e8046640d602030840220022a0030511080380320751003014228072591366500034078a650301d0907200c401203a0300079118404100e11a007500e041e98940341d400800090140308001340352136050180700e007150030305449a80b1b007420040e010014440001030308001c3d80d410114800d895121000000e140c107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 766660512 1250 766659262 766659281
    0x4081902010f0b270a0e060106020304030c06050a051605070f0306140c1c0902151c0506030f0a02011101140c07060c02030f030109150f080c03010b120d080a 69
    0x5100004419440e810b4214200310000c0e40000c0c00412a200f00b00210707583c650150240340b900c041004400400c003d0070943d007101c180000000c80c0c0d4050301580b420507409801005c003503440040d00b00104020030a100004040d507142560900340d4500004040e0f2089181c0d0140081a80311185e00b03004080c80320000400c010703240032402c107942e0707e8001c000e459994041018100703500001550034420000322199440c442203100e01c035101e220401c00080025060a80c3c100000302d1081641072121001002e958034265228400c0d0300c50080c80800b0f540c0000c00700da01130b401c080c4000705413100004811a220768242043d0040f07018581c4070b01c0c01010500640e5000e0040803080c40704071006400105080c1d8050142400345c02180302e4141c5e568410600c00c904003901c100010005801c0e9580031070300f40c240306801d4000b501d60707410308a01c0300100d6400220054001205004043c9024850b45030707548425200c4281151044080703540341c02d02400d015040c8604540022028000c661060800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 766661762 1250 766660512 766660537
    0x60e0606030601021615030b030c030a0b0c0f0d050412021f200a050a11060103240209041a46030c090c0923060c0f0a1109010f0303170408 61
    0x5141d6031b48112808240105000c80460b16002625502d800e001c00c10b0410f02e50040c000f0000300440c0e0380c40301c00801c0000e252070b2500b442441340041840f6413000510b100c4009135004546c90806042000200000312074130801d56001004180310140a4484103d0000404800080712005d850484611900e20b101c01c090703400000070881c0c081ca4004014001070811030740c41251450641040743d0761b07490b080c04040c002d008800b082c600003580c074502010640070758200160401e400b03d80410300380c030714400b40801c441c4a000060780301420481c035000d040d201080c110200380d0000d00807000840c1500c0c028440301300d504103c0c80704148883d001c030b5070081d607110107074020080e900c400a2006214800659002400c8004002900010006c400d0707640003185a1091418600000b000035542c4034a4440312075000f48881c184800c0380034820800c0b468065180034000e00c101108000440c20305805c00403070120401400d20209a0000902041c1ca80160348a00e945c0ca403410001d809001c0c03184c50414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 766663012 1250 766661762 766661803
    0x20c0105010b04031202060108100b150a030f0c0c0b0a15080706050c060606090102030a1107050406090501090b030f0a0609052e05150d0b06040e03070c03030210060e060603060102 79
    0xc401d880320b8000c2c4101c9010f164043c0301001d2051003281c507a0402c0c0300346541c550001043d0341e40218107034055401d45000500e00700410b841c582d02900d450700300707040706400301e42e86041c105002e00690003002503902d01e40c42c019511a205680305680703064080c103804001943d65421065071103411300300c50007406404040300d99880e40d0725001011640b000106020901441001c5011801c0542c01d441961505170080c50600c0f0341150200d419100030102c1c01704c14411400c00140a481d1840b820020b00080f0001040a605015085003610720340c0d40c0480c0a54005c020f11102d56401041a0000d1944008040340300c00300c50030301c6131030304001094005020a600511740391000501110525145803071100740302d070365101000c00210801d800082500046145120b00010302409840740c5e00000041c0005a030b4011000c586155800415048a81950501081c014036404010a0100004014041c0035560910100e481e840e0b0018220a00448000c40480c2841e8020300c0440070406881c1d00401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 766664262 1250 766663012 766663019
    0x70f060902180702070e0c0f18060d0f1109010801120303140c0403060509070e0a24091509090816020d140601060e030105010803160201050706020c0d080a0e0703080c01020c010501 79
    0x503402c010580d041d102505c42c42400280300103200341040d2040410510407410900b84078000e14950f8000c2054500035100c011900850365103880c00b070712100400e5100010081c40000814088600c0c85c140e054244c60240304500d041d0307038020482c90541d1038903048000200c8051030700342d0190000702c2c00307480048180d030304000c4c0000c8145c0182c0100e1740219030511454481c00c68242d2a400e10340600e105076000070001a0518804c0d40103201c2c606210b090441c4603585072407000c0c9001c800d03a04441c44e156103400740301c0c034070b0800024641d001d860008002c22151101e940c170b4458602c40c110300c240d10340d0419100f480c03d40d0307600700340c004107241c104500705500410130030701d161101824041d88002c100c0c0381d032000d60b01c3e00341441114160703034209000714940110705084042c59001c5500c101c1c1002020080d20300015014000f4110702c04244000b803071800300110001d058900e0081c43d08050501d801032000c004200041d055048980201140d5a5000041c08650191041800b168517541c2042d0002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 766665512 1250 766664262 766664299
    0x12080a050c120702131b0503070c0209040803090f1614130f0b130e0307110d0f0c23091609090905060a1b1d0109030c060f0f020303010506070f060902 66
    0x703010f0700f803084070140481d40b42510140101d07805917107050340100c800c1181a144078080c4e0f000755005401c2e418040b40b10390580c0d000810440040710211542c00c000f1092048181040140d0303545d03079201401410f000060f0380c80d01080d542c81881088101000300f4540030190711400340ca8100e2030740d5010107000400b20085103601a100c07045020303004407a01100d10100741800e21500c0f03460032212000d03503d002041e486010100030303500c900691126441c0300400c000ba02501c06004542d21910104800300c5c6031140030007441110031104001c00080a100d600d40ba5203000f24103038004d50042e000c0910301c0d4190400ca07000040c03a081200ca40b0701e0b0203542c0301400300000e802d07841006545418031000340d0082c030244088068913202000301e040c83d8060a0301420710240880c14207010b00d81100c1c00e0740e580e203c1c464200d07441e52141c000b0846201a010503a82d1100851007035000c140011461540b410021401c10711030b1800152000d42080800702c02c00c10280c200750703605c3c0d40003043c03610304c042914242d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 766666762 1250 766665512 766665517
    0x21c140a0e03060c031512120a0c03020105060a180e0a0c1205070b0f04051002010f0504060501150908030d09021302040627050117060f040c110111030112080a050c12 73
    0x1602c030b48240c1c40000c21080720202103070300c9146200d076085401010b55045c0440345180305803001c99170144106d145c82c001010406840090f2166403000b905070054100a403c4810180c030301030141160f29024449810154a50626100c900d1070010340c2589a24615080100c503c400526002a0328000108507040340d26140f0110b00071320075681c02d5a92029044450710a20802616600d401d100400c150325011141c0b06a0340740900012511581010100044640031903049510f82d5650300188810001c0035080d1034948501d0600c5043c0b1400c2c50801940c80c003800c0081d000003615200403208540701da82c03000420f404085c5041d5241c3c2e480f00b034068244100041c81c20b0003003140b0700d1030030040c50312850b10308201c4006850740600101004141c51091a00a2800b030300401841c4110034152128441c004081d61035a803211403c0485210190079560907080b50720600c00103200501034120030680140420340d004404683d2421400e2041c0ca1074010300c120500d40303008401c01d1800740f40da00e000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 766668012 1250 766666762 766666787
    0xf11012c0709050103050d0806030a08040806040b06030307030206061005070f06020c0d090b0d091719020d0e0132040f060f05180f030c040e010e1c021c140a 69
    0x755a042500e4041400032203009100150082d440340d101084498060710020740c00c10005811340306041c0b502d440d4850f079a07100340d005400340c2c1c1c01031080000703002e10385402076004502200558941011510001d42d907480c0545014480c3e04044903c4401502804c102d80c42d0b0366101d019001c0040090801c6802900240355826040c020360059046a0740b264640318156001c1c0071219080014400c40000104804c0030211801c00d0101e00700702ea46180d04004c2c012650300c2c880c2001084aa0400c0242002100106c00c1c051022111040c9400e0f80c01501d9000054000a002e00400f51014859103500e01c1210195601200014001c0354400344031b05101c09840c055141d05450740d040d0315003203a05115051400f0704c100382581d5020f840d45090205108040401800c9400520b158000103044960381d01d4030020f6a9511182c2c4103031180107008450044110440d8003011c8200180080c1d12907001c15000308248005c0c0340403680c141e0040c041c82d84512090b0382c13407986800760074001401c0c80c0c48020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 766669262 1250 766668012 766668101
    0x1706121002182220040e040620040653010b09010507151e05060a0602070e0a0f050708091011040504090606030605070302041e05010f1101 61
    0x2c0300e20b101400c0104095040c400c0085104103141e960b025a10b005212070b88000300000440782280c00300b001c0d144040e00140c400600460002e082c0b07464490101c2e0380c607604501c54441030741810402d180c05201902d0440e2058140b18051103e00b11401e1080840900005000d030f00396002d0703d0b0070140b0b0340102e4144030314464034032007000359241c03820019078024460b4805016041141e155103500c10000361514034842d02d04218640e05507800002920840110031946081e4072072031410007001030146603085002940c0d900f04003420310800079160003690055030030611030a40840ca0309000d07940320b81c002180300c440c1085103040018004140100276101e602d028803800c0c0314000908114800c0b034055a8003e6892841d05141c842484041c1080300800d03646140d4841000000c01c0a40c01014416031040e42e005944500b0106903186139429180601207a5400031000e00c4966040280781e26000b405041c04120341210003200d40c090301c000c070300700d503280e41400200b00748004448514511200190 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 766670512 1250 766669262 766669297
    0x9070f0602060f0103060c200c01020c04060b0901030213080604030518060a021c03060e011202010f140301030f020a081e0613020d020405040305121306060b04061706121002 76
    0x10101240d40c0c19040d1244603e21021100400014a0b6a8000c00780038040781408009005018180c400e00711000f15442d00640011504080310342c0d0500025030342074011502082080d0500030b05d6501070140310480b90615500041105d21403281305442c000624112040b01c204e440c1c0b900c0c0044c03054024031601c81080d045031000c000ca81c82d140060322580c2001e6801810b50618040d001440140250300080501d42d070b030040420a58041034040b4080c0c1000000c1e841c0b904040c0c400100400c00c1c40904004000d01d04841c00d80400c400b40071241125001450100f079089240001104040350303a018201d18031440001a01030004081040d0f898140007041e40c220b17640c2d441f000743c443d02e220f2800030b41c07140710000030034010324080d80701c42d800500914040e03052035544103014010f884155804444c40501118070f0080040c00d014140140c1080c00000342083d140c40310280500805504e18000070b00d8000c00540c558441c40b406503035603842c0604035500c8504000420000b984001070348035011445 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 766671762 1250 766670512 766670519
    0x30b070c0f06050a0b030f0c030d0c050615040f02032e0b16082a071e0b18091f050d030c12020c0303040f0e07030b0102031803010f0509070f 62
    0x194400503005400c10391412076646940c2e41e500003000000d010b0302110359642281e80e81520100000507000790010018100346030344030105440c00d40394102041c1040441c40c0040c001030804150f043d00082082e0201d2450030415001402a01000d5000ba00c15440882003022030a0940a12004c1150300103680601030304052880d00900d209018010080d40c08120058601d039022006c2282a405184540d00f05030030b62141d00c1c0811290070700b13918641284481141181d10601c01e050007004050303940e05040c0381c401011024a00c1d03600c01e4000200d008a42040c00443c0010581c8031030000130041003651800e0b407642d02c030100044800710300002c071003000030603203041100c0089141500341d2030360952907115a8881120600c81d85004085010700380c0184080e4500f0030141000d4101130100e801c50b0703420b05603051840380c1e008210000701414100801c0303603641c01004640d6560040d000b00e000e2071035054080b0740505001c0f00c14055041c584010841c141d00086200400e5528900340084210354 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 766673012 1250 766671762 766671767
    0x11205040206090d080d02360a1202130c05040302150a1409040207150507020d090e0105041e111b0c01080106030509072303060c1c0513200306010f0605041a130f030b07 74
    0x1d201c609140c200324610070038005440cac803450318004a44020010400c002d0a1000b90b001d6941540c0c1d08000701c2c5c0c3c00f003001c0c011403510010244081d1440c00d40ca900306000c686005062031420ba00c504540500028841841d448940440e590300e0740207036210040d0030303061002100808048541c60014090074203a05982445000ca4104035040c03da0350f40325990800040000406007516100c8480025460000001026002d013800f561030080016460f144122841d10310a01c003c00e9011242c2c115221074071171070703030040c0c2624191445403800103822b542e0005a42d140003841d41242e03002d070b81c1540e4001c0440120034090f0b120343c0000c1c0c0541d9550313121031040007402d004881c4c40000990003d444140c0305000d030f50220341c1c809402c0943c0d00285120751200c2c030644800594614600ba03034800354414904003005001d004000ca080c0e0030041d01d2074600028410b0045010f40b070030403018451841c180f02d103140143c0b40f041e0035400302074030300135660201c0680149480c401111703101e1341c00f000a400d2030b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 766674262 1250 766673012 766673107
    0x91c0c05010f090602060a15080d17010b12182e0606080105150c01060b22060801080a0b15030d0f030b030c0a091e050a0605011205040206090d080d02 66
    0x444d01d40003441152a103403000f0300902a250361000c1c00c181400300020b481b0400b0440d420b038410007610ba80c060794200d80c2c07500c50380440581006184079030070002c4000320740300c2c0c1c02d005522070b0320607100d5040c9001018000382065100ba0240c07090000c4601d60070708100c4c4440e0703640d001d80d4094104005403956a41d0588a0a20074841d0701d40c03002403002030b816043c040c5e4005008440300b501c000901c083d1204100743c45504198001b055803200b0180c090040380c1c7c004003070300242c036030f60401450701d6152104030f568440c0c0b0703400700800c142c90380c00106020302c121000044c10b003000101903803c58141c0d0500100060301d0300400000090a00f114040103040110321391111100c0038040c08401030401c180e85010300306c50408851640ca110059011103005485414014191100c0101d00f003803610000405000442e000300d20203501d4101400016603541c001c80e10f01d01801c1e43c01c0504001e0300d042035010350042c00c10000da8280000795014034035403030a02e10311240c62079203d4004903034161030b040900320303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 766675512 1250 766674262 766674269
    0xc0c080a02032709010315021c05010305100501080c040e0c0d050312180a02061b0d0519030605060702210102030403260403020601060810031e030929091c0c05010f09 73
    0x2d040006201194152442c9100207002d1f540143c071304010b07580403520781d142e09032160600580d0342c0010b00800205106142c04100300d9101480607504108201d522141c03800c2500780304a43d500003012480c5020b00003004400b000030078880154070030741809500c0e0b60080144246250490b00010f4058050780e5019801001c110b000f00143c035899400c3c17000d55802a070040100c100b540c5c060f2803034548204588942c0e100c6954a09440e10f40b100004022141c80905140500d41441d10034091070315403005490301c03142c044079458020359101001e81e50420f04090301e4116540000b0410060540196a85041070158034044080e060f60080f41c1c2000c1c03c0070b6400400682211004101d07451203200700e61340080964400c43c2c1c000da500c0c1d66001049081018012641c1494120708003490b400062400003000715103042000b00b0101074a1002c4004e40005441a241c00490500016210640e940b02d403c1c0f511001c06002c8109800c01c2444030016110b03050000e02d46005910310700348610a29000c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 766676762 1250 766675512 766675519
    0x1804030203090f060409090c0806071713060b031203040506130206030402011d060d0e0d050a020d050c1501080102191805040905120403150c09050609040c0c080a020327 74
    0x140080ea00400c1290068028255130020080c00302180c040b00034401d0103034403071088003c0308903a440c1803180703418410002e00d00c030184461010b5808242c05103020096100302c00214084010901d0f03e80700008001c1445c0d05a05442102030340010910204001d50055000e9000c8550360741c5c81e10f1002072115200100290817000c140007090055010300c01984c0062898848030512031a000b0215600d40c00c10b0134027103a25911000040a468414403404640c0081440c0032442c110b0101c1000e580c58100684200400c5000180504290002d1003403100c0580f01203036812265941703800e02d034040d400452030f503004480081e4a4a41c02030290032403803d5010b042084402407443c1c0070810000b0030582006460901880080c0d01282031024014000f0303510402483e410240710141d9007003215403104e0080e003400380d0964244100d0741e444040d038140501c1207402150703041240804441400c9000c2c0c0041c000740000c80c103282c5464001c03014200d2080d94181c03860300381f044600c5100c144c0c14103440d050741 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 766678012 1250 766676762 766676767
    0x31104030f03110a0803271203042301110409050603010c0e041e090f1406090304090c020a0210120f020f0703200613021003090c09050a1413021804030203 68
    0x40d00803680e105800b590003080c0c50282c03946456031070742c0c1d9108640307d541c80c03400707030081c0f03000c0d140c9003c8004002002c143c020014103803640800852440080c1c0040c01c100230080c64010140c046400c2040c101c2200002404850a03c03074102140d034200d4003807200501d041000240071130505101c0d00d03548498981c0c0b048140307006403003800010100c00c07182082c04200208044150600740c00f455010b40d100e8109180c0500c45410011080081503007102901d401000034808520000000d80b01503540400d800160409412030980c9443ea01500080d04a01b00301c440120050b088042c4000030203541f481804044045d1700c0240483c0315507000a42c041c0000c2c010312002c2031103a080b8404251286085004203851448051700e00325046450094034040c2d8940c003021410481c0c481d20810899083c20701460000e0f68403e00c041c00d0306e000301d21a41c0d0b91030000400c40328180d042a02c8010a000d6215018100f48940d00f548817200362050f030085005400b2155180e01034a0050701c00c0b501540a5070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 766679262 1250 766678012 766678043
    0x915010c020f04020409060b041d0f040b0709051804060501060309031e180e060102150f04030804030207050604090e01050108031c09020a09060e091608120c010615020d03110403 78
    0xd00007505440c42c3c0d00030b0360a100100c1d0504051080f1005098001e130280e803554600302d804003030390b40540d04007201c403028402803180c000f00c0b02d210590019480040000c10303a440c1e040440746402250b11441d44084031070f11001181c0d0301001920b02482c02501c052000d40e80342c0b0b405800b0f984c0c803031000070700081325041c3d07440c200401e241312101210481d14024a004002c040000e0808059420640b245000c110070300c03610350f8040211070904181010171302841e207009205219802e00c02000075060041c41400034081500c02e0045a016010040c403590712103881e02100b10003000f56a16141d0250b103040300100c1c0d042000400d0312280750444010010384040440868041d01011000300e8102c00901c0c408940301c0c4141c01080060b00480903103910303914185050524020107550303419041c00214005001d003550200e10110400041001a903460702c48181d818010403481d0b10a40301d441140401d001059404a4004600344003070303405000042990000136424030691000070f00f152141c00900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 766680512 1250 766679262 766679269
    0x10090c0203040b1c2406020109020a0506030a112101050603011a0c0a0c03030309110f060901031d0703050a122111070f030f110c0a0905191a0915010c02 67
    0x100400c2c021007070310003c0e44c941441a0b030151440840c0c03140e503008a88a514400d00c100401110007003580744002e01140546802141035200d887c01640c0c0601070020014000c20b40c25003210042c10805d0999503550a40603200060000400d12000340400c0c2007000010685496402e0b01e040c0c500c2d0160b44200103d000c1c20310030a031350056142c140580501c00020700441c14050707100c40150f000c7d03180070950b0006031404075010207014000c1032141400e60034107120354640c2002e4a08180013828002000001010f24800403103c100e81c030507042c0b1550801108204022808664180c0b08a82d0700d0f00d03001141c40d0590302c0c0f4000310840c00000c50000343c2d8070099000758200340740998906003c20301d440c81d50f445241d1000384116090b008600c82e04d01414029910079116811070303560303801400d05104540700080170b4520301d1058082249e103030070105400c0c0002d0128445424401c0c0403c018641000c403c42e070020703036044c8100d0700c104899400668810140d00d0f240c40001c005035201c003602c41040c3d081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 766681762 1250 766680512 766680517
    0x6061905071a060a2306030403111507030507081b09010509060d090320030d0b010c051515030a02010804120306120515071b03121e020702030d020d1b0503070b04060510090c0203040b 80
    0xa0f0208201525818ac8810301805440c1c018004144944c01c035103040c00003c2c09680000e004481002100010020101008014220501e1004050f545d50303007850001207a0134011400090b600030300008003070725080c5c410b511040d070140c4607403242000305420849101030881c880d4082e200030b800821007081203d400f90f00580e106501418001080041c41d03d91505e0a01c80303850007014070302000d007400504140c003841281000821002010b20b41c0050340028000d82c000f07000103064064035485070782d4140c00b0fa0000e0003d401d14080d040e401a100d81049a9030311500300e850b400e030b04440741c04240c61502c6940800780061041002e49001821a9000c40307419100480c0c254106540e90803503110603000401021500d48000340150b254420750040505007401c03c484001554410400440f01940000000b03100f11441848202e1405880c14490700b140f00d1000010129031903031007008100112a427000b801350076860f0f020207401d034507010000115071a508500b00564418031040040301e403074000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 766683012 1250 766681762 766681771
    0x1109131e050433091b0503070f0324020a02150703050f0403120e031b07050d0506060d0614072d02070510030605040c0503070f030506061905071a060a230603 69
    0x141c05031041c07500f5000012500d54410494200c41c00782c518000ca0943c2c60103032409003d08070007900042d45800b440e1703550501244001001c0d00c0f08510f0052007420000c00c41e04c0d4007200070700190f50307800400d00000e44842c06c07000750741f84c0107400e07401284085101c0d2103200d104007003644c000283d03511951400d0303c803480c00c003c4241600703449105280040c0010320281102071a00707a048400548003e030214288611904101d0264a100756954040381001078403c0d00f2907000c0e184404031106a090440241400c0c030003110410f00101d0510a00e030368040c145440c81174079000380900264490307200000d010112149400180c0c026041400039140150030041c001205013400103015603254046800d4400c01542031001c034401004001d045c0f6000a07010010702d40c80e00d030400803803607c43c000071070f64042d01844100001040d104030301081e005408a84000307410500c9d0380c4184240c034024000106c02161014001d0790252000511130f100781200105107064101c0c01802070000300103111061700000c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 766684262 1250 766683012 766683083
    0xe04020702120f10020f03180a200f01020a050a020f12060103060501090c050301030b010605071734021503060316330507061109131e0504 61
    0xc44000107030740d424441500400100042e00c42d80700044120380c2404010600c000e0580d00402070b1481002d2031000702c07503020920b4400515800048070340709240c5180c030000104101b0040d403c014011480000413000c1c1c041c100c54075011b072244c400c01280c84101d442ca000380389070320102c1d1110040c9081d6141050031000500305103029802100c6c00740c5000003c1c1d00c16142075607501c2c0103004a159034060100342040e0b030b007402d5281d94075503980c914501205200b000200b103c041000c00130401c050f00808a4034100a0000391203181c4440180208003036610344090000e06d02909180744054910702e08803140c0c005104500c4c0e03020003d50200b8941c0003c0500b6414029280c280000342c8000001c0c1000d070800105203420100c4551004030345039000c0c00118540d40e0400c0b00501d80950142c125210f05034092008150f2a0300886502064050081c0380d540c4454010060342d91407246a000b882c01ca14507100c480c0e0030000402020003100d40a69000d03043e06c0c42c860240310740c06c0031200340c04420002d20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 766685512 1250 766684262 766684267
    0x1b18190e01110903070b120a0c0e12300a050c0f070821030c09040903090f08030d1a0901050d051207060506040c0e1e0d0209010324020a0c030e0402 65
    0x2102542180c88540c0000d50303105000c80c1c24100d07820704021101c003034500c0300e0115140021841c00c0b0781144030008e0491506585511103201c00764829401044a42c1d00134040b040784282d06840192555101e40c581850318040441001824401180d5041124051402c8501d0924120000c81e071030b5010742540c0c03501c2d00c40c0401d140c01814040100300c00502240c03000d40b12490078987c66004410103400840c2c847c06042c010310000303045488c102c0c0d00a040444001410106519080c0d80c00d070002d600c45c41c04104001400129007101000074102160740c4c030820081a0400038100310300c080031044a0360400120700051190b406c004002100041c0181d0032150032685d040d800440035400a48211000d079290f00901c101800c0c0342c0130b9003000300300383d050100401001601003505960100341074907024a62505c48a02900c4900e1241c0c0410340140200f511507851382400d02c0324104014070454001d28803c100a0311031501d00c20344402202c02d9403580803409043e181265500641e9600561041d0308 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 766686762 1250 766685512 766685531
    0x30a14160e06070b012405070209071b060e0f0c010203041406090109031407051806010e040b12030c0a0c0f0b04030201030203070302041e09051302010e0613080a03021b1819 76
    0x444e58038001d018588040c43c130f4070968440d401400c815001e140c0c00748079040c00054016580c403c42d05074414a54540340c99102c560600d50203000035036400140c485440c2c07080d00c072049140030032107032135111001007221901c1e1084001240ea034855407040c1800048040d0f0041038514044000701b2480710140f401000c0b103901c80d212020140301c2180c5408103548883c104000c1410f09289220220b188a440d625143c42e106001805082425034164030650340c956000d41d580c1d0b90803000c3d61384002d140049070f450303ca54000060f960100341c6410b03a510800b12500090f511540c0d000300f02030310144880e4a0510f86160300540203504060500c509140c2c00780000300c4e1559903131110075090b0445465201d0a10703e00b1052002f2610090460058140c003015242c2c0541d0708034501030b14500083e14201e0b41c2c4c3c1071581e0140029080c5030800741d902c0c0220f0507880e00303040c3d000841102c114030042c0c1040d6840c500200304699920b800021701f10482603a80050426042402c4540303180756281c41c0824038804 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 766688012 1250 766686762 766686773
    0xb1e010311030f0717122d1314040b190306050403052b05091b0d080903070b041410080c0901020a0c080106090501090204060c170f0d02030a14160e0607 67
    0x50f04202c2a6004900701316072450400c100e850300210814440510b40724030b801d40041c1c030603902c1120405c00d0450350b608502047c042c4007203d000080450b161742d00d654440c0e001800014281a100744100d00303103180b10a45140c42c104460640d20b4002c0031900e540d03e19035031940074200c02407054081c09004c0c08034420090815495860300e0301c000c40740707503042481c03032502100316000581401c910f80c3c4194469280c01039003100076006c84000715614943d01d1281e01e880d0340d580c41540314640c0c0500951400251502014006c1c2068444404d0380345a030707001100c03c1c01201480350503800700050254003c40c0219400c0001001844010f106480d604032081d1a190107003082036024804a030f6444030308000e0f1400c43e00c1200c0c05042e003e0b45c107500d0140717896802480042d103514080e1220901c2803031045440c2d2802c04a4006c028249511038072407010005074002500116015400c413401c0c000d000c50010000cc851520070902c02447c1d0900303400100b01207441030b003441081500014100080400f00d07c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 766689262 1250 766688012 766688023
    0x140304060b01110615130f150503190206042d0b030a060e1302010305190e1b030a03080a1e0f0509070602240a02070602070506040b1e010311030f 64
    0x24040e00011031115581c10004140b0b102c001400d8900f900110700380040d040f6500d84045d0310290446590810004c48080c0310010031148001c480614a40383c4154511025004014200c0302c0840559441201c074500002c104104000000d5001c1d00800061110307000c402482040ca901c80440003400c0c144c03d000d0a45014078981061040c080301100b041006100b50041a02800d80701c4c0308400c8a0070b2010b80d10400b00110f8a001f414140c0300c1b0001039580082d114407001015580c8014040280454281900c525003002c0003000c1c5940a8254003c605001038100e600c82d6140d580e0a1561b0b854840c1d041c01400340b0030004a07008078007690700d142c0d02c8543c000c41d004c0961300a00094a07040c4006402d1500c061640100150f40094440c1c00f030314200d610845c011510035982680f469910208810001e201d804002010644081502400c0c0310000400c0d0b03101d98412103400400c0d89440180e4902d004010646007003016107640140300091109500300c3c1c4052005e0100c0f815080070009250900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 766690512 1250 766689262 766689271
    0xe06030403140c0a110a030f0b1e07210606020d0e2d090109230703140103050a03110f0304050d15140f0105040207020a0303110a0206040f080f0309030304151403 71
    0xd030f000c0f01d444020f110107200c5a5244285c2211b154502d40d2035a031790088100c8801c00003400300c80d1160000789004000480489541010001d038600610f4041c4000d08500c02d207050540c40034a503070a903044052480d00c01d007070641c0c0340c1d500184601007001d40c04842281c8251034880e0484850041010350111051600d503403181e15100303186241107070100740814410160320000103541130030b08406004254201058044282a800c0c40035640c51aa05401403c220601e009000d400140008280580400e04d404038a2203951403041501085242a0342c5005209007000140c10401040206141401190030118480d41351010328198900c4440300b02c0c0c410f400d1124000b11402d0401c00e0341c2d0744900d80c960140000f11011400c101c03440d004154044098000141400b81214030380c04203000401031580c0003580144034507680c544800845026200034483c4034000e1040c03440c20840c200c0088195400e242001d8000c40c205498000001010202600f80c20309200f610340102140142120055118 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 766691762 1250 766690512 766690537
    0xd0602160201033611090c0a020c180c0a020705030f070503062202040b061606020c0c030f030703200102070f02090c03090c06090f09090105040209060603070e0603040314 75
    0x20400600014058036482180190b41044013101407104001013124042c4036059030002c800c9003003040ca040320075640c070b03080302c81d0340320385c3c2001045074480d0f242c0010300f205842a13003a11104001c00003070101c03c41030545102c0e403238000203001038000a48840900900409441241e0b1110ba0b5000800d045c2540961011950340100c00b0612160504004450b0401800800035924903424414210046842c5000911490b00d52060b08410341e280740c261108a011140c07195000380311444d21000039804400007000314000d03010140b00514001c24024841004140603519003607041d9000c0b25056405655600c84881020281031885000d201400929124000020303c01a003801000010400141182400301d0200104100b0041c0403c0c6400c0c41c04041d03801d280c60300114000242c1224103440031b160004000c40800148c0304054021a00580c003d85a140b09500c0da0014070006220445400d000b14003100b100d0070a6003451401540d01901900d001c90a001e5081d4454440703a20080c0d0040b02c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 766693012 1250 766691762 766691797
    0x2090d050d08090f061609030506270d210e1005071b1e06061208030a05010b0a0f081024120209150f0403080a110118020108060f0d0602 60
    0x9100d500880d01e41e4001c038040c0c005280e46441c004081740d0b1140300500140e2130f220701c001503a164a00980f02d0340003455104040d03c0381490072030004480002d00c1c541c014011090781404010289020990105498a0360b848042c0d0040c0104500590621100000d4166036600000080d218040c050300424608003000030881e400c0070f0100425608546c0701003070310160340e00500c40028a01801c680b202d200c50525540b0340c081c150420000030b103801d82c00b260388800441c03071200c10413034800003c0d071160703000400400050741c85400060701801160341c1304012074007411000c81e0b62b50290f00547d903c6a88001144c00030f81e21101c90304019514011043e01030307180b00c00c40000161f00807091030070071800b4130b208604010300d180010311118100481c400200350009080d4889900c0c0c102200e0240d80c01486040d5505241d1800070200103030418405100d52820030400c12034004000d0050304950140c2d01c140c003548071030040261501d03200f1700700b50f880074900d420000000c0150014bc454908444402d04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 766694262 1250 766693012 766693033
    0xe09041703070c111816020f1009150908120c16030c050607080912090604032001081302030d08070512040b0108070e100911160c1d040f080d02090d05 66
    0x300d9000c90440c00c1441442c003120002c006681d070104e1180d0111203044005001d0070100016070408202c101c03202d000e4001c8609c0540090699000315454610544810a002182800d00012180c0c41c19005040250411050428403102d4280642182ca4401c0c1d81d0729140700350004040302110f100c1c00701c000c120710050520500c0400c0c0b081c154442c1090402240da032034040806134452040080f1040e00400c08a070b91070031629401c060718051540040702305d1140c12580c000c3c1a20302c100c5442140000d0300100001c01e448040107237640c0d15940035006241d6540309480c19502c2420041406040120034401c400c54a00f0240d950b03409140038a030b1411855040641c86820682c2c0344e00000134030f0b4410710601c42c03203509451080c2e00312990031200290072071030f500041450703114803004070580e900d02202d0309080c42180c044003400c5866224926031894160804214042d0080350040c0c02d0444d62a10900403a01840c001e12103144a0440180352208540000d19440d040540a0320f080c2d00030301c0d04c2c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 766695512 1250 766694262 766694273
    0x8040b1c0b030303042103140c0301090606020708030d050c0f0712080702010c17061c14190f060507030b0a0e0114040504170901120203180106150e09041703070c 71
    0x1000301a0094001d586586003d071510141b00c91082c0208948000074190507855602c2940504c0542c00c1e001c1c87e01045041c42c0302e9859240e0000c3c0035621856190800000748070b4000a940e10486020501542c1490307041d1040400416000717111342c020b000c1c100a00303e03039a14514014205d161040c8210b110007110144e005016001c001c200e5425a8500340810784040c0d04800712440545411807001c00c50b0341c5410200d03940d0341e0145484520030f83e01c00819810801c43c00095507002009508460066241044210060100700e00141c502000d071b4258501180c039a40040c1d81c400c0c868200402d2140c062400b007040c4d41000d5104100f20118a40184480e2282c80e6050010b41000c990622003410640c550703050401c00c002d0902c107c803900142a041ca070f4001e00110007509444203003192246403164000030340c01100d07002c9565652800700d0101c1c008207050b0b080c2d03c03610070b2543d408070003072080f0003032280101020b0016034002d14000b1031080000c0c100c10003588074801c0e81e9101c00f40c822551608 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 766696762 1250 766695512 766695521
    0x14010308130e0c04030602070501020403080325091d0601030b13020a0207091413110406030c03021c03050f070501091e0318180f0902040603111509060301030f08040b1c 74
    0xd10b034030b014040d00b40080ca00400e019602640d0f0480001030755400325240107402481258002003240c0008405c01071030444001c0300c1c40581c42c402c0344c09030002240c0b0703904a4000481e40505c0d0251543d2035a0401c2c115400c80b01c0650111040c1400240500700a001034811036014482c4281c680d00090900001541444000010400d40c2c03824054103604403104c038081d001c020300c9021540840e241c0c480c14400d41c0d00101d0341005000d40304029180c1c41c1c1c2008a0155903502007230340035a180010a074040c0244580028648c0e4041d03540c1400c00d1071082503090141c1c08100309031810740d01c4111290101c0d00050200c042060b080a1003420003049140c050701034502c0482c940e000e80d60304038080091030f02c00359022090740b86090002624030710080d0040010a80d0420194100345440008010000102107000c0528022144003151203414a82d110403071041002058119038103200400010f100f09034241c0304180714006150400e6102e03c3d01c0011908811402000e4060550114280c141c242c1708 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 766698012 1250 766696762 766696769
    0x15050108040210080415150302090906060120030d02040902181806010503180a0b0402030f03090d0807020a150206010302010306050a050607260c1e06100b030a1401030813 75
    0x80c411040c0c98660000342c10404080558028041c042c4000b8040003090b00203034520500c041d0040081900d01400381e11984494041240200c15110100d00c403044c002a51507c140c20503910480b0200315260340b617a0265001e00d151400348401d01c01521408214000350000d00029000181c40d001d0394201c0c3e05500030307401c0b20580241200c0f0380324180c0720240c0720f00b83d80c0a030003800c0842d502d4a800807540312480080807141d60798025000d42004100b403400001e130207107000f10212807060914103802500d038460380c0205640f04030034216140000381c600f400380005d24001040343e18010380c3c45202b0151403801c500020010f0300520014402c540e05882901e015100544c1d00c0e141c042e04000100b2141e126880001d0215402c050900703000d002c030004c0b403007244c04003050b4440c0c55240d00c00b009540d03030020502c0ca00411040140a2a990000082e01c1c0c0c801d40748000c9000e40d09282c251300b0584c65201806625406403a804510f0215050580060096200c0c0140c642d95582110300c4904034801c640 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 766699262 1250 766698012 766698017
    0x150f18090712200d020a0207050406300506070908121804020904060302130b15030702060c0c03070221010c0f02120c0307050105070302041503020a12020901020c090406150501 77
    0x14180001c6a90020020720a02010305000541d0307400f4006003820f40040c40300708540040d00003110118020560040e00705c03400301c0c0d022100813039195001c10017038500c24010030054041203901000410100700003203544004c40c4280300b01c031481c01c1d180c070350404108907886804103405040c100320300403040044c2e008848036800103904100641c1d00b00f0100b9860a10398a1003540c010a58800d2039556500100c0190341c020909024040c400d401080580140b10f0274a102d260404050171943c1103d6003200c2c442c01e02d51340648513541d00e1302030f103211940002d00e000c03c1501c014801400180c4421085840d40740406841044103181190b1041c20358511000c6641000120301139544195000600311440c408840d07141030302c41d004500e0603071450003001c401401540c07c0c401803041c0d20350540d00620584040144e15854901c002000b50705070311560034801c002441e041c030458a40301031540030f0452007405205403201d04911400041011209840030384407107584c2e4000303104031120941d4480083c1002e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 766700512 1250 766699262 766699279
    0x315270f230c0103050403051b0c10091406070816030801050909010213030213140c1806130332011a0a0503070e0c0c0307030c0c060329150f18 63
    0x6410640c590444044083c14941c0712404241014090001e541e4510700c0c031029504028082e0f1140c60380c03540864035441c02a10b08018046100c0c0c800d80059013a81c0c0040084440c10304034400303000142e8400a001e4604c840d05000c07440501016219100d02c190082c0c1e1a1405541000100a400c0740064040700450b0b20400c115003a103040704000f03004490b01181c89000f08600c0300c2c2c119014200b50542c501811041d001040f8001d000600134143d80c8000ca080d444194a200007404014031801c1045160200706950410000d0540d2441a00c84183c00d980050f407150000c109403004000c200d8540680d0351a5614044003141c1c2400420031140111446565240f402011079207806250060b04044c04c0c035071000454081911088a1003003060404a96407100c240c2002004161032035004c031040502281e000a0543c801c4c0900c0c80c901541240c0300b030711031588050a014000c0320940503600300c1c000f001c4140c40302403480040e100d1140c0203481c06603640b03850320142c041031801c3d0940d14800c4200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 766701762 1250 766700512 766700573
    0x60c0201080408031312081009180f03122c03070b01090504060b10050319020301050a03030c2a06020105100f141f05070b0c03090303130c0b19180315270f 68
    0x20304c0aca0440642d00040320041d52409030408846141e80b0000380c8020605140c03000e60031a00d40900c0760703a098595000483c040307031b0003c515a12031040c1840640a0f5200300014040380c2130962100e50040c0c031800d000100684940081001d0604071032030b640210780d001c4200840c14004410600500c80c900c20308515640c185030020340d0644003800041c04010840240f1820094400d00c03068600100f004440c5440c0402440e44562507414041d1000550900c3c01045184480804000c21384040998240425003480c98041109503040c602c564070000c08010b0004050342c0811501100010342e480d02e81d41c0a1304d042c032480c4964040c048a00c40f090400422003255804000c0c0c0390018102c0403105128400c5041003040d5603103541088111079400648507034420b01c204100c003550111503c50010204503c514991800094840034003060390140d2800714603a07180d888005001c40b0071040c00984ca03450034042a250414000407120184116200c909010b800210100341c3c03111041c9098a43c0344 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 766703012 1250 766701762 766701791
    0x50904050624070c080102120610081311180106120b0d0c140d12170f09070603020f0c1903020f031606021602100810060c0201080408031312081009 65
    0x86150103014990106210f82040b8408010f54000d204c65070007991112545100441004402e45005c2e2052441c0311100c1c04040c01040f0302d074440d0001705000c07580042e0507280e4002090f001c007030382a44404107203444405c100c84e1068040c0a02002d03900c8184000340c0d0515001120042e02609120320f20400c540800204078205540540700d00d2118607009021900c0800c1c1182500b031030040c40482d4905542e00c4081c1e102c220321405100c001904800c0703445144001070784d5102030790145140d80040000b8020325004c0c0d0000c00442104154503490015412840343c10300002021035003c0c0708901c0c400005240d41001314080448054000d54601030b0f006100d00020119480000e0000e0740104042e06000301301c51000301d00c150040d103155030104c00520002c0c020003040745c800740d015030002c0000c645107204110050220f5810785400700c0f180c03559102d030380503504000d10000c191328074403c88030000b421013040d41c40c4500050301c4101482c10401282100890546c11020b43c1034a00f908001400c0e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 766704262 1250 766703012 766703059
    0x60b0306040209010c1703060f04091112071a07060c0f020303010312050d0204031a100605071e140d020f24060f1207050102010605040c0e1507120509040506 69
    0x44101d80050355894500b005039181407420b24003402c0b810b4400c0880e1850044040214441c280c21250400300003800000c0104844001c6005890205214a01c0c109400c010b03001d4001041c0600840304c03466514505910b401701c0c0040010354601c0c0114940302040044d01030b4400d60482810320580c400e01c0b900000f0f660740014030000c3c1c40d070600d088201c042d1600880c22030301f00c0d0010b140d05660303868980c101440c00b005000241070526a00d140050b00002100301450191507140d41e40c0c42c90a410b03900c9007002454125103403a0441090b49000000840c1e08042d000d0b510300c0340c005007043e0700c0c2003c0080c0c02d0501c000c564203ea50450b008a4003c1541c6e00c0c1c401c1e00582603840100750a0316020f000c10303003028400020a0f0090055501c21a94802c0003514508070f4001740d00a0140c40e450780180004e440d281403401011454441c40200f642c90700d080189004422540c1150810005ea04c9008000c0c02410081d008208000784040b1207080c80c2c01030a40c800002e80d0850110b0502001c0a80d021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 766705512 1250 766704262 766704271
    0x20d11010b03190f08030c03061c03020d0309080c0f0604140c010e0103020c01140a1a1806040209130216140303090d11030d090c080c0a0b040e04020619080415060b03 73
    0x20220808004020b09580c00c4c401003600014815220320709007083c01c4d80c944c01038555a1041c010b070b145401084541c21704c4a01e0503603140d4041d000b80c02c1ca09c1c9080e00544140d00084038480e8061020410030b00f005c00c401c140c0d54941000500c15810702d801d00c0c008400080005103800e8021070010100f030b98202003080d05941081c42c005983d401002021801031548541c8545039818400620003002481d42109803c4110207050300c4030b41499104215411031784284080c029241c960008007140b82660192250709005412581c060300c0345080340c0201e9014824082038041803111403824042c0450303185144a00e00c4000310300d58209070512079a621244107009040100340030b2100400d850034000d58210348844041440080182e1038544818011401552054840d540400c8218903149040c08211280c5051092415003454002c1010782e100a0040e40c0084d005c00483c4d5030040c0b80516848000441ea6502d0258281858984001403504020342c075450305044060242c0c0381000e040b203401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 766706762 1250 766705512 766705543
    0x100905090c040509040b07020f031204080703030902090a1a09070e0f0a0503100e012d05070201060314010912050f16021809030c0c1012021810020d11010b03 69
    0x55558448801c0180c03155801c000c0e0040610300a1004018261142078000c640030703006e43e403c0e8280c141c2216624000c003084108044030318001b09021400c800000d0007164040d00d008100301c0d5041e0040340003040140c0303541c144140c1d42c078203034800c2d0304d80480d51407620101100c0d00c00c50b50510020041c020310302c1d2041c06201e50310b0072240c8442c1d030b0740340c0ca1040002c15020781511198401c00d04000020409210b4680c0302e075080480407500400314040c0000170124030818405092102c5554000622008000100790b6688038404404100001840c40552840c0c400109503070415291841a080d4402c0c03000003885401c2c001900c0462400c01940e0b51a046200581d8901c829400092070582200b1001c40c6021040010f1041055001c0008c0040e1018407084a00c4001030400b400600702c0482e001200048860204c91110b9081d40c0003400c0c0007213030201c0c01c908042c0450000781034106048545002da40407002d50710540b0742010011190040400080003174207000030220303407280c0551031203500c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 766708012 1250 766706762 766706779
    0x71e0c030504270c030b010e0307050a030b0c1c020a12061a0c01020909040503130f0b0f090f040c02011e0504051917030906070e0d32030c01050411100905 68
    0x3403520a0f00c03c004443c14948030709200108410703001500800c100001940061500d183c40152420001050012603901420419140b891511920580d000280020300d0600c010002c1c107000b80c0400050100b12480800016074404507200082c0550580182092009040501c1007114030a9408101025030720207020715520310049880500909c2a4000b0507488510b4805110900c50300102518a4100b00c0c0f52400c40c0d1130700ca218022001c0100d118600300030500f0400d0744d64208501c1c01801079101c0161040d0308051041001030709a501c00800000180e5507078202644403030803860451a2702d180060b003000b00c4d040030340721540c41c1d030b0342240d031401030301c81007101c0c1810030166180760300100d1050150581c5901700001495290402610305800003803056a103801c29280a910b84c020b0564060201c201c00541c0071140c00708400130707802e40b00c100a891208030b90302407001c0c402005008281c40000445145c2403803d4104d4941d80c240090103140c039080075884058009280d8030591384215071681c5c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 766709262 1250 766708012 766708049
    0xf0601061d0d060e011820120a0b040303060b16200616050d0809190203032208010f06050a1406190c1103010513020d0c0806071e0c030504 61
    0x4166140110301c150700b00d219140c0c0c0c4002e2003119403008045480c0f0100a101490200010005d08000b008014011400790071403a415040c103400f544072500405455a5010b440307c150141c1001d80301d00060703d81780e0002041004044d0b252180c0405040452007a506107000301961414043d01d052008101c40c55962404140c03207080640b0701d01002e00100034541d608101e2480c0c1e9006615408200c40c207208a4200040050003910361510a9581074010034852503442510b900c44280235106030380600040041075104c030301c8210041c0d001d0207803280220300680340c030181908590602100311043c40c9070410030b1007159101307a0703c0b00843e82d491002122901c03420001605610a04411302c0d0010500c056001030640c1005100355158020000900c50f100788106060a0314421103600003e009802514001032400300320f03000c20b95001c0c0032030900b140d071201c0000d4900402510f41c41c02003241d82141c81030200130724401110350145480c007421002020755001c1e005000b140035050645051413281e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 766710512 1250 766709262 766709297
    0x21f120510090e0a11090f0f07090b0a0c020f060f030414330a0605132a110706031a0d060b03100506120102030f010512100510090e0f060106 62
    0x301030003040504203e4610a008100d584e02407141c022100c46402c00d03580d03c000d1030101185403080013a101000c0269903000124101c11200410200620056070800301e10b0007031005c09403101c5c040075200d0a480d403000d80100046088040d41d11480303403408000f2035480e05000b10039645c005a000c0140404250007503030302400c081c1c410081140c00c50b08090031030308405030109450b01d03c6842e1010004c01d40c60340041001900d0050143d150440020a0641c40607101030b4419041c00c42c44004442c102c032030489031000084080c510500c0002c40c8031a001038040b4081c031000e00101a242410040c4803510074400d40d408143c0c1300504d02c91906040d11000340861034001f50344e003410041c1680c800d0990300010000400060b02c45600941104210103031003101442224007400f032410a14045030311301420056240d181c42e00c2140c0b1030144100149400e403440c0903042c01038a5184002c04c003a070503c401d0030211100181069290703400040346840c241c00c0445d5460650300d582c90200c0c561446d40c00074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 766711762 1250 766710512 766710541
    0xa0f0201020a140a03080a050601140f0f03090309010806220510031a100501020a0203030d020310050d05060604050a1a12030f0408160816170703020604080604021f1205 74
    0x16003003040161010402c80004a80400d0041c0700b6100c000300d64a4a1f42d0920890b13008807503103400301d0940040045c0f013003000405040c8030200d00c9410703841c00d07021480700300041c0c0082c0c1e40d54450b6400850031f191300350b1b00028500d078803803001e41e00200b151400320000c00c2d0818480200a903000d40d00c1010605a41311200c01c6030195030000c0c611900c007800408104e04c2c0e080125510344202001120204a1350303c00300c1c0c0603040c507400600039030812802120f100020751010b04056010b078010300700003606403242403d107203006010300068955450101c040c00180d510091407159506d10701008140820f00c41811001e405c1703015102465041a2040c80ca403a40c480e00080328107010000c90001020b49001840707180e41505003410904813a03448107401e80d41e038190601150f001060103000d0042c0d8070903180e200149000303c0200c8401c56a00c0e0040340c0c156000d60480070b4180c00c91410401503090405003100ca4400c400c3c40b800c1004240c8000408690309640d50702915521a000300e80300d060292803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 766713012 1250 766711762 766711783
    0x303020409020f07061a010c08031f0303111002070209040305070204141014060c0d050c070e150418031d010314070c14070b09010509040f0c26090a0f020102 69
    0x1421036075182c05143d03942c0c1503000104100c440130704003141c4030580501120640e5842606841e4030820b846150358502098100600c0844015100d021448200c0709003002a0000d502070389483e912050740100107820301504001501881d801040340c03d0042e119010340d183d200d501403901da52950036510004000d400b6008210000e0301c451818040d07400b0041200c08210303021118003600507241403007030000342d02580e07101e00413b821001004a12602038001803181c400c02c8416a0600e503241c801800152600703862140d40001900218000c509103403255034111003e01084aa15030442d550040a28900140480b0441c03104c43c3c103802c0c00d9009811104000489003011b03100c6203865000240704d030603080010b981030001c6841c0303018485400301c1e01405032079a6400080c40c1402e444010f6525900c1503420300c0d0426a500d00b035118440291044030000e41052f9240d82500701c1d88525002c50401101c0f4189110305a2403d005000d5070006d105a40d8070390000042d00702e03022900050341010702d031b5007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 766714262 1250 766713012 766713029
    0x4062a0812040f15020904060602120304060b0a0b07150f0b09012c0f0618010e06190b120a0e0706091205010204050303040909030f140307081b0c0c030c06030402130903030204 77
    0x521301c40c0079081ca50090a0b007240d050307908000003030340c070f5a049a56032054000011035060400c04140854a03d0704000d0342d100000e051003666907a00e9070603c41c1075022403001e81c0c1c0c100c09007204e03840b0a900b40c0149403150030100d0741070203c001e403000040c5184106101c0e9034442503001d03840d40d0b6416549400c030307440c0705550b00b030301080c034a00440031424007035084500d180306145002c00008401c7d6443c14035070503115000110358540d5911000c1c03102e49040005854100c1100b01c01c002031003000c0500030207950101501c21003481c103141c0c9445007034403081c2c0c030f00100c03d800c0030109209065000300701c030003101c050103240003c40b070441c20424024411034110b40c0c0c150100280215910400e508070040042c46650703002c01d110070311442250fa0305001600070610b10001c00225072028403a001c1643c10801c001ca5201e000000d000748a92180d00030804421207804c01e140e00340b074910701448200d6202c1800d0b94a1307481c61615500040d5100058065510041d80c1d44401e0004c1c0351090b8199000f500c01038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 766715512 1250 766714262 766714283
    0x308160216080102041e0b03011a0d2c12090103020d14072003040e0c0904060f0807260c011d041503120c0209060d0303090804062a0812040f 62
    0x680c285800703035000e0f005400382003004071b24043d0913403048500c150403036100d90f000a0441e42804002c10030071901e4900d100c0801c2c01031180741c0d00d02015203d030700c988000000e0003145400710701c200070041c0d000300e510752182c98000c222003131520a070711030484040c9042442c005a44084501c12000181181d20011826a08104c00c1260300d507045601820030081c06120200d0501d04518026941e2085019a030301c0a240d00000c2104042460098100610001d0000c1000d1b603d4a8203280c0c03201d43d940c0140f08a0348001e104004484414101504000c20085110320303031500d0700b11003641c030307011304018504120b00701000090441d40e80354500c5031110024418041c5105045040d5200d007414001034070200c0c032030944d0882c0c5500503408140c41c10b40c00340c20641650341e04801c000030051428815811b00d9150103c500000e071800300184080e280301d403541d0900c090780c2019000320221241c0b1030420f8124060302c4e00089400303503050b0f03444814442d414940b0b80c1c2d10782c501070003003c04080000b82030401d031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 766716762 1250 766715512 766715519
    0xe0105070f08030f1305030f0d0b0d2f151303140a12031811030a020303070b0709050a03150510050d0c1a0406080f04080702090a09020414040308160216 67
    0x41d000030f5014a201e1001c810300c0385c4400303100d045c604040c180d00a10780d83c4100b20300c0c44034101582c00340c40c0c4400c14000000e01c070400ea8010130341307071113040d0002c5648162020003054000064002c410390041c03075042e40402e0491010206501c503000320700407404c650002c01c124240d0a801112000035560011320003120940e108000d44d0ba81c0c0720002c00300c4030f1a080b0351004046603c2885a16034000303001301840c0400d002500c03048840720039201540d81501030b4a48030343c09600e081004160302031117120b0f1403550703262000b4000d00b43c90040e0485403080c010304070200003282e980d01c22017088840340800000d0799225034181040c0010950311458000c1009a20201030000c083c0001003100d803295036840480c80d280440708010f124500446000c102294046003048032140c5406902900c1400b10900d00440ca8000030302400040718030119407038507074140c94214201801200300b44030007649080c095007080d03030b805882480024900c3c0200001080c84502c0b17140700700b1030200100c4c020403420303075000e44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 766718012 1250 766716762 766716773
    0x905040f21171e04020a08010c0210051f0b0d02130806060a240c05030706050103081b0a120c0c031506030c050607020303091002160f06020c0117070e0105070f 70
    0x10880e644001c1401c526018111116150805100702040d1501c60100081010301c0f14010401800c03ea80109000c800450029030910900340c4072440e40e00281107031030305030080340145e071001044040002c41c6002150070000c001348400040d40d0540b1400e644841900e10410000c1c0078044007000f04690318000000d04050204465000f80030542c3c04060080c1c071040e41110101c2c01c03844080701400740a1000e06800c0c8902e96482e00305201d070080d680345c645152210004c2e10400e0700199641040000c550602c992141d02100035490035602600c500c000d5034a42002d0748402c0c174170406c00d12640d201400300b040403001c2c40901070360b4002c022410894290b500d060083c0a240070480e061840090040760307070318045040c0e4003070580c000c000394546441f8100f440003903558402a0410340c4940c00c231405001380401a61300150021900e080030300307864850001c0c40c10701402c41c00d5050210000d000d504401c001d007a8941c0c44962410a00c40a07540c2e1401240e91f80705114024152803250300b4420100413 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 766719262 1250 766718012 766718063
    0x1208030721020702092401050f040b0f03070207090612080c030c0d02010506030c01020a152301081c0e0f0913080d0617070b0301090513060f06030c1409010905040f 72
    0x90007954030041395501c4500c141440c0000e0300319102401500c06c0780707045942c0f042d00200032032010364aaa0341400c0d6a01011059604030b0821040000d0010040094440c0d04110060083c00d1501003407000502d48040c2c41d440041c01640134000075800100b281e10342501304202c5600d200c0100c01c44c0c4044c1c081942c024002c06050b01c1d03080c882d000742d0701040655880060701d4503000b13070441701000940b0091b4a00300c005050341c00e98014420003840c100f5107502e0104903214001c00040c1c0c0605284444804210481505094418203000b005500c005040d1581003903c80c1d045015110550681c030342460300242d5540d0300e80c00134a6450002141c4c003607100c25800a4003200e503600b800d21114602c0c1e66031103849514601582401c1681030004110117a101e820544e0425444003800c280704450ba207d01c0203807040340440700040c0741ca4107410401c108105c0c00c1000105450011005004215000107440c3c1c0c2e018880c160744180c075000030038280300e1190394024009601a1515110161003c80315403086c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 766720512 1250 766719262 766719277
    0x17030417211906080d1b0f0209040b16140304031206050301020a03060e06030d05070602160821060103020c100b04022215020115051e030718060f120803072102 70
    0x1a420120005804840091002c48001042d00c1b2000200c5a050808241000301d4105a0383d1002e00000b217070250301d0b4004428001c80c0200305d000524500104024241603c00300324004108640074441d80940c581c009580c1c10550600d0101504c030360080d20000584015002a640b5520020342910b46940680c40034048901800d02910560786000415440f0781649200e140412020003c441c002440c3d40d00400181c4400710001032158040e03211101281c110760b5140c00c01c1c452440021861040b004080b0303602050918040d444c040044203134a85420105000214080d128007803900d0680e240c8d01a41c080c03006090302100746444e008003082c0d041c405031140f207122040c0100c4142042e4810300502c11b10300424042508c482e45000d090000069a003020341d6184a00121070580c995014001440206929108001300398201d072256070071038110b0f40c056070200704010801c024181d100502901c0f504e41080c4c1c0711b030f1030340e96103181a580301603030141c0390f2800e40ea48400782c80480d09a60140188 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 766721762 1250 766720512 766720561
    0x14031503070b0a09030b04060f021209061302010f23071b0b030103020603040b130b04080a020f06040c0611190f15020c121b15041703041721 62
    0x446680e0b00d02ca2507944a60350001c00000d401e0350040c40422102001240c0046c0310340b80004001c03500300440400c036000b400c4025211304c0350f0000c0c0b040d5402c0400400350056221110300a10442503800603052642c135103e41024080c6840541d401c81030707402e050154081c00c41d4103140d6180780d07a20b440c1120b2003056030a0318143c11041c2003c1000024002035a05a81e0b012382810310710307121a1948881d18034014048042e200309240b10100007002422400d0142d80311b040e4032602c3d0116040040d040240000c0014085d03400401008085850305200b18102d803600d05010381c0804080503a0ba0a114003240c0907203004040110181c01c010710a601c0b55800d46c0100d00303004901603d170b1a05001d9200350007078050340d50301070000b0801c2c842c50b5000074030040c10070303440e0510060400000c0604081041d80500c646855642c100018800741c4008011022046540d039403440c07500740c0c0c50615919003828a00d65102004c109044a2680e003c00031810003403160070403405152103081700c01d400407102e1402e4034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 766723012 1250 766721762 766721773
    0x40303090f0602070302060d091a01182d091a070810030f11190f090e0d05030a05091e0c13020f040e1306020c1c170c090114031503 58
    0x15140e090003548025509940d0190031085d1550302000810740180c0031b2031240540d100389403800a20048840f4140a2614104941c0740d85040449030600c100700520080d2a810109012200380d281903e00f0340146598818030092585200410700a100722103009100c4010030164440102101c000349100b076880e80d503a00d0580d81c40880c41280e154080c84010002c40c404403c500024180d00600c080e00c10028140400100783c602c44a048105c59501504117174200700402d01402c90b850190440a9041c1c0c0002c2000151403000241280700040942e400d0300d54540105220000c140b01910041c01c860b80d9011003010748175901902d905566910910490b201854030b200c0302414001c0e50001e125480d00203040074508500b44200440090400004a40341e140c0880010014030207480e8400d080c100902d0044240c056090341740784e01041c40c0f8240480180c1c11580310701c094004c140d0042404107190344030f002e40c40068821041015080303c100002000300104055110189010528110200c80 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 766724262 1250 766723012 766723019
    0x121201090b01210f020a03021809010506070f0510050c0c0f0c060d0b010c0507090c1202030f0c0f0705070806060a05010513050603090f010203100306060e061e03030405120304030309 80
    0xd0886400003240350201c1e02144548580341c2040151011202841c1c0010074140c0250000500300d80c00425180c012941c0841d843d004000c2241c01c04035090016104002c0650505000450038001c4d032000134944c403801e09643e020040c0c1032003002d10305401803034184007a0a00340040107640d040944a85603030710aa40c2045520400002d00201000d03003d8031161522180a20740405495079030221030600c039589040c180010700821a0400a02000100284241c407101c0002d00d456000181c8490250040c4280407640c00040d00440e00401d034815016a01d1545641d4011180158440980310707010309040043c1c01100459003c0c4150012a005480d4136241c1005580300e0140810404014412660601103420054011a084502103044441001c0090203c82c2a41e00482c0c130041c2e05240c0c03120400c00c1107014001c031405812002c61504040ca46407011a8200039000c41070111048010803001c01a02c080c401c44000e40006401c3c0900c0819440005030f40394020720080340003a00181000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 766725512 1250 766724262 766724279
    0x9020406350c0307141c110c071e0308032a0c060610110604060e0c120604060504030504080f281a09070e152409130e121201 55
    0x1144039040411201c0300e180c030340105118140e04014018414040d5100324040d50b00b40d4080038204083c41200c0c0c1d05e041c0080c081c0b6100c2a00e0b40502d048020040034800c0100c00400400d5840545d0390b8030705181c4012001800080304c100aa90019151031030010034806042c000007040d2107140c507400c1c50f00000f1489008012054840c0402143d03041d001100404c403545000048502880c0c00342c81c2101c0070008e0b056255040a500ba1805c0301c099541d60304540c1e240c9020b001e041d045000445074541c509050b406459200c480082009111030740d520002402c03d03005000b034502070801402142e0120a4009041d035442403144405004c41849590782c4001c0700d100e00410b816181d010681303102000300400b1307981c1d98840280c21100c40307006845000c5689440041428403030402070100b00721405103141401060103580043c0c582a8080f100c0119540c66428102c403415403082c0c480c00e40038803c400e12a4020300400b90220440e008407014168100c850601500c40341c805108000c026903656050b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 766726618 1106 766725512 766725587
    0x110c0d09060206070c020109090f0e07080a05210a05030403110a0605151801060c11040504060b01180501020a17120c0a091d1b0409020406 61
    0x40080940c1001550b80004d02ca05000d8107907681ca40000300407040320b0242110058031032160a410404950094400c60800419600000e450703800050f114050b0b94030540b2603220365032140841c50200e200803d410703080311032020b02e011800741050b0b03a99000144240d0501c4a81e42e8906000d1105214039101144030b80c1001825103003145000d1036581e1b400c08518015104c0c5910700003005040755086040d01c100d400c01d540500035610303003161850b510306910780d00507013040180000c12189402202c0c4024007621840c3c0c0740115110b1400a6415034481d8a0050b44030b0881500801d202241c05000548010083d9240c130401d40e1034070a1503541a2003080d002000003680c1c007401c41e409034440000d814050800360195400a07440000d4100c0079101002c1409040406420f0700610b40480c2e009020011040d52110703543c0d0b4010301000d450b00c4504055803100d5840c4d0b540818555107 = true := by decide +kernel

theorem cover : BRFrame.Cov 766546762 766726618 := by
  have h0 := BRFrame.cov_init 766546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 766546762 ≤ n) (h2 : n < 766726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
