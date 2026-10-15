-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4820
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:50:47.330511+00:00
-- url     : https://prove2.me/submissions/c3fc6b6a-6ebc-47fb-908d-6d0c388001c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 866726618 ≤ n < 866906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 866727868 1250 866726618 866726639
    0xc06080a14091903091d070e09070806151c0f0605240d0f09150b0d0b060907051b0a03031109060304060b0a0503010204091406030c090a0e1507180f050a 67
    0x3c41a0103882d06207001038694094280e42280400250f100c401c1c1d40c3c0130000080d502844802078580c2c142c078040e50f10305100c2130180c41c0d0100a80858400c01503001d80d141564440403d83e428031001e101c0ba0888001c41424031001450090300c441180350030048041580d00340200c90442e0aa0003003034042200640308244d8250350041200010f00c4c58443c1c009400302c680078001d0302205d5004020031040c04044800100c22500c450a2960150319486041c501265483c1c2c00c007a4007440649441019940e038180c225200e1042c109500d50419040da0003294005000845c01941d51090f1000c000d9209000301c1102240500504143e001c0000c00000300041c22603002000d20503806080000e069445100090036070f00560080c0d03282541c1d441c1d030755008001c60882d1030f40004095024089060134240403c0058400400100748692103000d0204041070401604a1102c0d602e00034410f02e0174850070050400c1e406000c01d0b24030030600080400c41038017071030700c02040f5003004010844ccc06180080550 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 866729118 1250 866727868 866727913
    0x30803072703060515040e030a0c080c0f0f0d14030601050d0f0c050a030510080c010f05040f060905130e070512070807032109120204020d090c06080a1409 68
    0x2003070202512550600c1c554240803010195200e14004195481c11001c1c4588076010300c20050700c80c0d4200780902c00346c20400700032900c0841c1603242004000720b403402e1000c8107200301002c0380e40604c00c0036204c00441c4d4021455003008261074041d075848a009820448a280340144003400461080011400e558040c00080c0300442c3c003054042854043c0c404006e0480d080403880601040300002c42424855052083d00c0e4443d68040307048042ca420442000e0741da140142c401d40c1408900360b0700c118800e0107034060324002c025840e1039070030701a10b41d0f100401020842c885c0f50701489840100c442d00f12070790b0145852400e002c000502c4541e10b002d08101c3e100c03070302c92040d0384680030f40c00001c261820103000a0010b0340c0502c00b40a5641d801ca12a9050503041d540c01400b0041c43c01c106000ba0b026600d040c08080da011580036880312205540400201140400101011500e02000a01c29004089284600d100c00002c000f003110b10f0482c8515084100d4030307030a041c4c002410141c603d0340c040c140d04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 866730368 1250 866729118 866729147
    0x50a030b01020c0405090c010905120a032a06020a030e0c030d050a030204030803010806010f12030e06030408040933050a05060a020f0304090e0723240d06090e030403080307 76
    0x143d001d9072075103000c0b0382120410344204100340c02078140c400495030003104000042106980b80b0301c003138102a6460380c5031152940000c0c10848584a0b41d24402e000322200500e1180401403040212981c0c030f007480c02540b00b0181400443e040c801c2d0060441d401240441916502a0140506c0203c0100880e143d0340010b28207014141e00340404000300d002280558040c000c120002c11907541406070051104155510a03840c2c0340915064400103071b0b1160003039105c04001e0b103c271604c3c1e80702c520f01801c443c042d903002614070501e0714410300000d07400304802100b4024000704107100c0140c002c40c0c181c10703003425015003904505c41000400803814a0002003160f184244150340c040e0020703401d142e0650b8002c0c0e001501d541d07250303085c0c200030307181c1440b201004012829420342500246c40c420882c1c840312075056807051482e00a0030305446900c5101e40303004c0381d90070007441e03445c41d601d0703101d20003005280501d0b05c00d58603100366410070f18800421181613036007060555046640302c080843c1c1074030040d07400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 866731618 1250 866730368 866730373
    0x30105060901080711031b07240509010c0f0f02090c031b07020d12021e06012105010b03030f041a120c031b030f0f09070302010f14070c080703050609010c050a030b0102 74
    0x103003001c5e90a00c0074116071105c0040e00300758401c3c0b00003054901501c0350411502e8010580c0010510080c640c49100c040c015811b0907604c030004c1c200140c40500bc00e0502900404c1030b40b05003010050102c1030f20400324030886280710f00d5250400c0e032104602003100c141c05960303842490410343c48004405040f40510080c030501ca05101c80e03482c2e80b01194290311a0015a21050b031514002c8001c0d070001c08255031b6400100481e6150040300680002203942d085440b050560442c4180142900403061003080a0202c0b9a201d80504904250364854452540307140c0c1201c000c50717a040103c0080701c07400741c80603002981680b11400c0f03134096684094503902515041056000c3d203d01104090341c428540e400d480c15031403402d84803000343c862000f052503456801c400800d0006030703000304559814055911340a015400e88420540c00d901c03842001030040548540c0c005000a40000c0c001c00340c1c0d00c1101943c0d40c0784c0781c540c3c0803404d132240c850101000c5281881a0b07035059109601540d00d07034205104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 866732868 1250 866731618 866731637
    0x15150f07050a08030f0a0209150c010905120415081519031403030708060405070c031d09100302030c0307061e03060e0a0603120c0305030c13032a06050301050609010807 74
    0xc509141c45000c51003103c0550002c002c110008080344421680503050035029440c1452030000105006000c900166082c0400724200e80904400d44c000c034080c90703100c8120b40354071110f0082c585603900284107542e00e242000e42c3d0340a20034802c80b0342c0f6010302c2050482c5c1d0503c444080800c4505001103079038104140e15003100002044183c261052401000c402540d6a4101804002c21140000b01494015810001880441070348403130074400350341d0107160512001802880e400d440a054040043c2d001030302105124020041e0103440d000c40e4400c604450284205100381078681e4490f00c921004103a4001200040324140c0194617a00e285528001030785036100d000e04c40c4800b6060f42c080418030350b00c8105104000d038810740c040200b0628107110303084081c81e80c0c0c0282244002441340c0b01c07078040440e0302c418121104c074540d809154070041c401401c4820000030010004144902c1815082408c000a600c50003041220706a030b00c043c0c420740c07520456900640c0d4240c00540b0040c100040b094 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 866734118 1250 866732868 866732873
    0x30906040b0a2928030303051b0a0e041821030b03061603141e09030306130b0d120206190b06040b090307052107090e0a030f180e0f15150f07 62
    0x1603c0440301c9443c134050070354107401d500340142254402445039103801540418810040100029202c44002d140360013400c403071305a004a8050401c1807007407958211480c801d04c0400807551a1500384410070a90b01c9510700116200700c0584050860154042d0040b8000c1811510b045040d074404a0440c240031a104e40740c5445007000031811241041e280744d0449800f4000e10700d2010311508500b1b070000540c21410a5400242040009214402482d56130f9003a80c030207032191203104404582050002c07824010000006e5200c500403210103a00062082071310040d1003442c81100b0040401602040c1400d040c08501e2015034456a0701c0e6506200d01080003400c0c0d5281050740c0703030240c0078914007004000e5420744140b6000301c03034102c40720090410314007102400000400001094040c940701c80e9000310207031b06607070030b50034054003080040c5450310218140c040e000c84140a031101502a801c1d503a00e05030040310440c1030828aa9011400303900d1804561540740250043d111100902440d008159 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 866735368 1250 866734118 866734159
    0x1615180f1a0c091008010305030922020328090b0609070e030709020c190b06330405010905190e0916031401060e0103320102030906040b0a29 62
    0x100e442c0d0000082c0065460641d00b4a00c112000010603802c0803181941140d8400391240980c125150281d0301012070151100c2c0e940d1170032550300141010855503402d041009107030341164020b6200c0d048030503a003442070400d0180f00300108a6000302c401c04854070340c2000c00011020241a000812840b00c141d04416501804150010f06406100694442c820840242445007014541c030301003150440304000724401d405007540c401e0044800c51440207a5890b11003404181001075402c01009411501079080c5881c000d0003a2130302603d409a0095880c4100180c9100d14010030b0300c0e40c44002810410000c0c914a0181c10000c082d080c1e810564020751800a60368543e40150303854024408000da00b16420311a01000e00b20034449480a507055845120f075103090380c2d00b5102c4081c1030610900b60880390f12454120340301524020765583c00d00c41d070100e03900d483c15181036505600c40004101c4040c0d02d4881c41f400c00c43d510728400500d0101e005040c040000c1c10b00d00e02c0e00b000d01103180e02241ca009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 866736618 1250 866735368 866735371
    0x60209030610030c0f050d0f06140c0d05060d0f0201182c06030106031208091e0606030c100c060b06040306140109110f03041b0801021615180f1a 64
    0xe80401480c464910305007042041d800e9030184194116241c02030240f47ca0320306d940280d43e90450202d291034070007441d0540c010090381d01095400c0621400380020303207000b503000b403841d43d510400c24082502c1d030204202e40701140720360050080c58400406070040d4081da031000c0c60021000381c903000a9035200d40b0710215541404440b070002106c412400b190365440050306070030120a030000c000365400e5aa4009005c108121060148188030000514210040284108080c04119041041e9580c0140c1666800d0141c0c0d04511034018641c0d91070b040d040000c001d600e0b2518564400c003200c0d86586a2000130091085036942000c0200b1001c0003003403590064a404250342000e08104d50314203014039003110752400024441c52005c04c001d041100f4450140c0b5089a040079005c1c0111341e402c1d41d540c1447c6d903940c2c0300741d0565002140c105101e59a180180380068002c1d10440c540c40c041c0854901201d0382030300e50368415009178004101090301030300c1c0c452000d4461420702540f00251126403103030860 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 866737868 1250 866736618 866736631
    0x2040f0e0f0a140a03090501120e0712050d0314061507050d08061804080f0912010f0219051303030f05070507080601050a09090c170c09010902130f14010c0602090306 73
    0xc44240c401c00c00800d40c3d008100302041c1d10103442c450101d82e03001031107900d05202c1c0c60b041004c031014072105d0341107a60060040c150680206e4120650700d0781c0c00820350381c0301c420545060003503004030080e95019000750f00038041c18428064281d9680020440c80350003401c0c29280c054070621621b8001803080109020030703811a10b841d1310614003802084074000705500005040000c0000b44000a00414292195052203420700b585504071040851440c00440080320100c0d800c100c2c00745100411903005105450b9181d428860640202a00390742510650040e0104900707010010404a0b2040b440220f1414484c0740c101d01e8400c80f41c844503d0210710b81c0100340940c2006004100903d840d810500050100784030901c07450035561144c1c85504424410302200313081c13801180401040600500c000300e28001c0086126585440c442c0001303421080c040c83c1d010f034002c0000f01d42100c52211006c01c5842d2404a144010f012000441d0000712500c0111100c80d002d0101c3d65140d5428841188070301c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 866739118 1250 866737868 866737873
    0x180b0c0313030b041e05060a090f081215040608251a0301061b050d20030d050612010603170f0f03090303041a10120f050102030f010f08030301060c02040f0e0f 70
    0x70241409204494085c540c1006182c4c1000648000703440490381c0e03a84080d40d06000507084001d82004c40c454045100001e082d07540008610b41440500200b5902a00c400c0c504000503c15203805c0c0303c101c4005002d44a001d90041d4104000c040852800312a5103404004c0991110343c0d41c480d204464840041c51050741001100502c0059407122800c0d448884c1807168000d43c543c5516001e0300c4480c0c1c050050300700502d8515051111940c1d60301300e000440032208a0307613100ca481010038010138041d50b100b81300e961000112600800140203e2003a243c00800305c150304105400700080540c0700d0f050394540310340c082c40400d0b40300286034080c41c401c5541001540d583e2400303280100100f0741181004140001403418048211314068168040d0f40f40312540c1320500d1041e00b03180c3c00c03000405074014115030001080000d03002d003a038040c5040300c0380007050040d201e45500c1419117900090007214005260290042d025160075000806c566100c414000f940f07203000070000317042000000e000310855 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 866740368 1250 866739118 866739121
    0x2011e091e080d0507020d1d030705030f030c0610050307150c0f060c031410090c0212070c32040b0f19180e030307030207021c05060a0606180b0c0313030b 68
    0xa02c070f280500c0360310a400740301034040354002802c058800707070385030702c60f141c003000c01d048a1040e548080002c000500001403c0300c00980707840d8074482e41e0780c2c40000c00c1080c0d03000d40004511101010083c1c541950300081c083d0050f1410030b2000301c042540702480104101d036460b001004a2501008410364900942012034914500c070005815524801c048500710a00c034010406145200700380801541c45c55000414140107480c81240f50845034400c5013585030000510301c080050072a030700c1c0d0464480c00d400c00b05028042403500c10400d00d1040e00c1c404004d265190008503c0e19602c50381d208180140a00280900d04010801224450740c0c070036910885c0310030920100034000315081e007441d03a400040c0001100084000d450b4000900f0850a0680201e400401c541c0d40043d0700b003880500c0d0010b40d030b000c107030390900650310801030342c55105940ca4840c0c042500c43c8907003c00c0c85901c505d038000466080c54180383c0495030b805a01110b046003c207001d10081d40c581240320300c0045001c1c07941d652a0303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 866741618 1250 866740368 866740387
    0x70515090a0c0e1e0604110c0102071a0c0304030c14010c232b1407050702130212040f06020c0f0a05070e06180405070b120906010602011e091e08 64
    0x80e40b8640080b1009184502002401030601c0800c104104480c44128101d0321801c02060103801031000ca120341701e02c003082501c401c150541c00780c88a2402052200000c419807901899000002c0e900302d51010001c00000300032034007969034112020701c42c00440b00e0b03064901446d107085030f0051403480006440d0750800111a603048800034075810381c50515918010805240c00c2c500c2101134102e000e540c01145030b484c0c2c0b44445921014810543d960310030134520f00000300802c00d0b032003010704900c2024a881103020100c220700c03d8851101c0d13101035101c0385444a449100000c0203880e002c88074580c00b00700043c10103000f8440e4100306408c0340010b001072240f91424a04192540d00103000000d400000c000b010755400d1403020b01c0d18902801025240c42d50309005080c0040b94200301e5203000009610002540c4000c051885484200c00380c402d242d0725414100e007600e003d00000010a8084640c9610006495202c202032512440781d400d03c3c5800005140040d1085000503542d0b0180400e29102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 866742868 1250 866741618 866741633
    0x1810080612030a091a0f0712080703090803040303020702210114010e04050723031c03050a1118010e1008160503010609090207081c0f06050a08030a05070515090a 71
    0x8078080c0350080c50414070010001040800540300740798545035025601c08100000008440d2158003c0d004156a1a4170b03052003100500c3c0041d440e80020410400621218441e12824001c144d000034054034649580e00c1c2103020350041642660b11134404440f04083c02c02c0322008072026018440042000404850194440c1c641640107201c11600f4208100000d0404944182551940a40e440050300d43c403480c0d407403146680042503014811039204004650030080411000c0c0200e07a07040c81281c2d1400016001d4501e901060005554240013240040341f403070385019502031041c5450503140d80c000d00001d00b03040e1420b24080114804405000c40302c0520390700001c0301e4001c0d00707046145501d00207008140c003159100d228070a5034003150607400c01a4403012138078041e6034050714803960480695a00010030042c501e00003a01d24112000440c0d0400400c0c41c012190224013642c140120010199155031202d00c00300c40d64000c0341500342012050540d124010900000140140b902c1840c02c0f15 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 866744118 1250 866742868 866742889
    0x4051f0b030f0303060a0905130c0f0e0c070210080a0e010f0e060c040e04020904210809010e070506041404060308070302010903030b0904080306040e031e120f130818100806 76
    0x203105403c10810010580c41c2c2c0020041103a0702e140d00028140d03a034484070461580082380040c10403a85407400a0401d001102c0b00c030664254800f207181301d0301c4d241320820143c41250002904000c1000091090038000d03000150700291420b40400c40181d81e001d41c82c01c4030180d0a603110f140e03907101c1448040e81400c12400754890700c0c1403007042c600340c00c0c50380002004d078000344002d200341341c07580000c0c040160b00e100a0074821051036000110403440080030304941c030308840e008150361804074440585d00000440d5811504013134449841d02c0d040050000d00003071024080f82d00140c0307902001000421f414000c101080c003d81c0000b84540c124034005056850100b003d034401c007000010300000c2005142100e8200d80100d40000e540e000503800103040d80290350200000c003110001031402c090004004104a175181c2c4e0014134103544490f00b070500c20806581a003401e00b03001c800311001a203074100030036016002c80c034151410751604001400d00540070212100094249042c40074904181740e605 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 866745368 1250 866744118 866744143
    0x4080a0b0405070e0609013003170901290301090215040e01050406050109050d031e0908120f0a11070801020a05091206010503030a0c060603020901121502040602031204051f0b03 78
    0x8440b45c186030001a0b82c1c51018000c291402010350601400c00d9060340c011800e4195140450302c410000e400c0181c5120250340000c0081c2ca08000003034048030b0180714500c1c052000744159003190030300007061452021032001c5141c241d0343c3c40b4404409039480080750440082210540c955590070008401c403801d8040c1e101500950424406100513a0006d002400385c80c000e450504007000b4605080b6400341540d0107400b280a500080e00c420b2a9114850b682618008400c4420701104404200035600c50f01880c0c0760100d1051140c2d00b1030385d100c0c1d140e51580d181c2c0c00003140c040607240d900302c0d030032a070101e404d24002c00d41c0004d04000b01e042c1071203890300241088003d07003a258035003004a6224802e122a1100f08a40003c9110400c01c2ca0340c03150b405140c000d03110102d20741e1944081ea82a40e40a00d060b9460040000f40c44140c0b10103000300c1e03054411036400346041030045d107044042010301920480343c0e40201c01001045000142c021008000305c03c501103840d80d2144189801c2c10329000da203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 866746618 1250 866745368 866745389
    0xc0f02030a05040b0708070b0901020921060c0f04081b010f03180303021b0703080d051012020105130b030901060501080112020a05060c0c030a052503031e0504080a0b040507 76
    0x1091080b034201c402d460844401103038040c0d4403400e52404451611800030018610b9811001380040f5044c1540074003403141c400c0e183c840c59400000808aa801303403410740e2518544c0031000003050860400301501000905800b13540c242600c030400e044c20880d8031610782c4c0100d00386980c1c046440da13204080f05d10500860500b000011038800240305109a0502d002c4c040c0b5030002035000103040d5005030f41304c80b60090010380e80e9494581c1750168095002c403102044c0301d4148004a02100b400c109030500315896a036101010095035401550f40d80c0081d00c02240302e1580d5031000034000c444000440c46500410000071700d8a00f0032002401002c41130300200b05080520510740f00580320450800207130b440481b10705480f240004002c03803401b02440c42c8c0580600850710404100140061744c02c50141e514280f5189c01c002c42400708024400a104c06000034051041403c210181d111200e031405041d46811480d060711840f10520f03040c8030b98801c0307544400010800044c02818403041c4c010b030443d40780 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 866747868 1250 866746618 866746627
    0x21f0c050a0c02011e091a0a02210706050c131410030f200d0506090610081308030721060f0315090c0e06010206090607091a07050106090c0f0203 64
    0x100280218000d4109201100e140b040c1507a0058403503010ba60b024600d042c207806452800141000d116108000c401320301c0ca007008462404c140c0641394940d500c0c0c3c1c000c03e1002220041040810408007000b86104010854140420154001c440c814860700391065583d90540e9541c0341c0744001c1ea80180c0c83c1e0008004640500d07a1402a0201c0d180c40318038000c600600d90007000e0000b0545410307082006018410b0f0001d0800e9510007414080e40c01a6040126940780b60510500c01c0085800c142c0c050252540006c00c140180807040d00440c0003003d01102c01384903514000b0326801520030f20042036143c00d0840402c00d00103a40080800d0b855170501c807181c600317100d1690710f200c0760100502d0317070245a804021900a075807200d040107401100702c0030140d0f507031012a48502d10948106006014900024180800010f1014001c04407503840d420101c0ca01241c242d00170f2000c01c0c3e4895003410030804440442c60902900001d840362100c0004c4c1c018810101800b514206c07030000056400611 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 866749118 1250 866747868 866747891
    0x70b060306010303081612020408011b030b060a0507050a052a0f031c12050114040e0a030c060b130509010e162304021b06090c01050705030d020a0201090210021f 71
    0x101c046402a20825201b10118128241500c0ca40e00c03140203450b060f0b1012400180c084815044540e08000c0707100165241004c1000c120203803444070340318a822400400400e22003c1c4280014030300c0500807401d1710f41c0400140e41e11420b00c040b90f42e05042c007810000b41300c03104501012040003505000c84d00100d44403250340100307449220245000c52070114034902461030f1400ba08a031518503540f03e00400ca25a1903040880e140d10700305100714040d03441c01d0b801e030020081c0020843e40070754054855000040c2d21703980b0000a0718000e402581c01c44205000d80d0300307401590180900454104c0008035400f52220360152130880204160b600c21094014200142c0880301c0d138604400004003076946c408a55140490080e11030100442c40700d03921541c00c141d109e0f00104584d0b0045000c84142c515020f00c8100442c1e40c2c0c00f400002504a0304200104036981140750700400c500c4015000221b40c0b44910f0300020030700204c003121100583c0110504461314180c031080322201a1402004004282288 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 866750368 1250 866749118 866749127
    0x609011e1202190e2a03040219121103160b0d051b030112110307052b14030304060c08070509120a0b0a0e0610120b040c0f0b070b060306010303 63
    0x91186901c0010010745580954807600341d007560681a210b0400c003a10350310700070038241030011110795445d99041408030b120703010744ca80391018104914600e2425034490f07808010440c08080031240c0352030141400041d1501100740c1c0303640503902800101c1c20100c80c010030715080504501c540b03001c41c5204041800319040710400d4408850f065000001d850340d40c0c0505c0044856002e0340c9644a080200c00010b1000000781d1410849200380e400007003908440d401c0c150340f810b0501405a00c241c1c040081403005000c00110544c4050741002240350440b1901c544070004401040088690000801c01007407080718016408410800d01e030108480c03419480090480c000c901c5400c1c411400709aa407410f40344208070308661240c000b600c420301801c1040ba1140103208a18241025000e0b070340001e80105150f000781021182c80d2000094501f0480d03883c20794070078004108541c0f5042648000c89d100f110150440083e20410130041da403101103080c81480303040024203880c03003580201d00500000c0d500c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 866751618 1250 866750368 866750429
    0x9090e03040b1209030403080414040b0907020601060c0302010b060d0903090b120a050703020c01050c0903121e13090c021614031005220f11032107020a05030d020105060901 76
    0x10501010744030b071034615013a0306505c210791028000700c3c00494042000308241502d840110800ca90401000c1060018000503590840340d00c409a00300100400000e401500311444040c8240300018100500b0303800600a0380103604207a020603918112101096088028900980303000202c443c10492800700b40000c0e060014540040d094944000c20b40703e50094041c1c4107903a00c0ba20083c0242d00d8070012240302600100e01d014400d10440040301c0d100310001045900d82c00905c0e0000d056034a0241504101d5400040746910360709500758000313443c0700c0390f01c50041084040d078041d22440301d40c928442c0c62001c198008601c1c1c40c101c0901100582e40001c0c1c42e08c80c00b034200303602041d80c9d82c035046c0798080c072842aa40340b050b50741040004030030013a6100d1152051407084162030143c003102003d1540d030b0308562054480000c01c01010f200362900107400740c50032510043c00c042c0f5541d01c9101107030074858407220703040160b07442d03c06004080c0b0707051710241e0140c0901400c0b255000e000f418039100c0d1f00038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 866752868 1250 866751618 866751637
    0xd03140f010b070309030209180601050607020904060513050304090608010c0e010e092a040504050f090a1e0c0b2a0c040f0b060301081b0108060108010302010e0d05010c09090e03040b 80
    0x80008020b000c00d40681c245d0030084d500280340b107620786000d00c0040703544803203191a040c03540544000460207103040e00c1901c901030380250203842182c1e0760741e549400070440603008400f8141980340d03403400206d0803c01400a01542d031004a101450502c3c418291043c0c840e166042c04142c1c0c1612810341d0744101402a0300200f101c030103a0540780e03020f5502170a8592014046041d1001000c0400c4d91003075070042040f07400030358041101d9a81c120740c1031100740c016669070f8402e4100700a80c0700841d11950140c1d00704c50010540d06200d0340d0395035500c01c04402a501000040340701042c0c80c0345411000c604812004480300c0a4507202661090040d00c0b010340600c42841640e81d65a0414410095484403090031005486981d603561602151543c0710f103150840140c4841e4040c2030040c95124081d0b29020340c0c0107031030b041d00590075940155400e001502d0708640002c030305582d06010070024050003680400c00d0b12140d180c0d42c1884414801e031801101e180700300750b004000400a951020040b202c2a48 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 866754118 1250 866752868 866752889
    0x40b0c03040303110f1b0a1703190912031503081c02090a030803090607030b10051c061401020d020a150b0a0f0927030801051c140d03140f01 62
    0xe40700c1c5000da00601940d5031061a141c40411030043d24440c0c0c2c0c0041103500c0d9841806051204120061640c0b03080c0c801c0024070540340d0b860100c2a140c03201025580184640f141c2900034083e085248086654580d42a80c0201044850340e0f4165058403410340e000c5c010031600d0080a0840c1c64900c0b81d482100c3d81d160980011110051189903a941960520300c00244440401652814608046c0d00140c03a80c1000380210000b090078140284582c03801c011000d45000b2000c0d000200c203890a4000107003400301c00702c4c4905c2240403a03002d0301ca1100a071070103031034003941d900b02c4800080c541042404078109551024603000c01181d800403c4402d800010100442d411000002082d900d6607190300c40a071b032160490011038000f540d6005002c40030050000e001210800841d0746142c040c6003500a03000c68408801805a810701510038958002c26084520324111580d5908409030382120307210040c2d8002ca90401c03a04ca40c90301511150f50555150490305080c041808054944103114080140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 866755368 1250 866754118 866754121
    0xe1611010b031e062404020a120e0f0601062109080708070c06080606071e03050903070902070506090102030106140304020a090203010b07030207081603030e13050103030224040b0c03 80
    0x402500280c540500207029603142103008220f4404000c0583c01c02010b40c02000300184015100c940034108160b0b404900054500081040c000294071141b4500100f1041c1308807c00c6c4000d013030050b442e40e0201c0c03100070304800c11050300940c02c240e01a0030000400c00c484004544503000d040c068860b04403030100006d000002c1d0300c0c020b00c4510039000005c201400104490040c0704903289000304490058940e01c0c00740d81c65404011072031080c0b003030040100408440003480e501100f580074044a1103400d20a281c4804080041d180c900e95901c84426603400241440820909020503904545510000d50030740d41402009400308204500140129502000040c199698000c11030000e0036000ba0840d40ca5850704101280d036030240e4000c1d0f0142c4202800040c50840015030070300740500103a03421068604503603080b52152802003106920400c6154400341c4a0010f01c0340070b0081d0300c0394008003480480900702d00100039021050420308200c29041001044290854642c044a032400c41c503034a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 866756618 1250 866755368 866755397
    0xa0e0c09091008060709060306210b07091a071e08030402130f060e162d111c08090604120804032006270a0f03140d0203100e16 56
    0x3120b42d69030110a0318491001440344598000c080e08081c1c031900d0b6030030300c00c1e1500c640030480d4100d40581210306c1d121400305141d001c20000d400250b0070484a150401130980c0e1001002680c0000c08030750202008001000300030400394010321602310340c0949514600c1c1c85151070380c0207580030003031002e8040c2c100541e0040124a15502c03011001019810400c6002d490703040d100b0600c5800c603855910503904868900303516018603020903400600012214009100400e100e030b0045080c1490b03000e00219040e00704028030700703101c80103410f0f4101c0420034440c4001301d001010800d000d00189542d42104040c4804114000d800400c40b244906107918a03444905d400c45140880c007400d9500c020040d681011080f9021980030301075228520502d10f21428001d03001007101600b0300703100139a44045a0b0000140400700d100000e24040e0518410303500841021060b590300c08149203074200c0e400820081c0343d040c0da580900151541496501d503a01d4488240300000301030940b00000d00c54140c00f04003a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 866757868 1250 866756618 866756641
    0x91a13110d050a020a090518153601060507030e010302070213090b0f0c04050d0b100e070c1b050d030e040e101a040c080a0f0209060f090a0e0c0909 65
    0xa42003000c000070482481c3c212008402500110329040002d101c00000044621b094034444080c0089800003d0068461702844004c0107006681c054202410141e1262240b843c00020340d40049a00b10b260000c0f4050b40c3d83c00380703060058000c5000d0080900040c1c01283c0d00c5a008e42c0140400c0c200181d03503d0050002402c076200182ca0300c030403103050143d0001002003c031840c5006014400b00d414080e101e00c0c0c2c0d003131035602030342c081c0c01e800201f280c4085021401c075818540d0410003900c0400c5015884e2032045400701c008880d0900403d4017001b0744070400c4501c0c40b02d2495201c01c88045c88500303047c00c2c00035070403894034400901004004000d14016030390325440711800000e044100e4142902e40781c0d0420251820754011042642048195407017401c01d4010081ca0003001c3d600c61f0b4255a441d15590000c00405401190882d42404400070680700c01e00104a01425840c0703007a221045401002504c403000d8110b655007201032403d0102c0c2000300d2098a5015400b110a0040d95890140104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 866759118 1250 866757868 866757877
    0xb0f0c011b0c0302100209030309090c090d03080711070e0105060304031701140906151605070503070e09010e1f0e011401032f030a020409020f090405030301091a1311 73
    0x241d0030803a1480d010748041e0400da00d007480034869029a20080c1c0000d42c180304900814405075015041001440e040b460308070071040d80221540402814242c0940200300600c0803628201c005c1051201802415a0000c0c0c00c48230014048009024003030a0580300c904450042c4145401001d0220101c0c0c209030042c2c2c10b1500914954400c040340e1760395501d4a00c8600e40710301c1004e0140365014017140090500b042031005145203179000c640791480040319040302c0c0c4501d642c241c0d1180202d110100e100e41e010301910005200610341654039040044685007191141c40402e043c981c0984041c9804016506103c0208800f00a00041c004040c804083c09801e121529828100c1458000320422806042d261200807404c64002140700c0d041e1110030320600149401541a402440210010318041c0c00c8100203030710180442c100807044002003048210305031022103054202100500220103075220b062640003032050740c0fa04402044000c590500d2800402066140c2c0b01c1c002420245032220480303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 866760368 1250 866759118 866759141
    0xd06091104151511070e0601140304050309181506030a0f05160f02060f01141f0201290603011203030b0d08130b040e18010b1215010506040b0f0c01 65
    0x61202050100360b0389011100790055031a814400c01e140c0c0c640c1c52281100040c001e48520080030010709041009450305402016a4100a40460802c0c107000010001c1c60045114200840d00c410481c810804581d0000c05040a50a04101000a14441c51940201002003610760550b2915400c10241c0940a0b08000f0003c09080070f040c0031440013071100c2001e41c51342983d00d9414140006a0072a11420b00707030303000703d001c1a00c480103100304072003007456106440006001c10720003501e4050512201c003460b401c00e030242c2d55030004641002c1d40ae1082d00d10768000130b54503850401001d0000742c2d690006000300d40d000701010400324101030083d4403440214500812485a1040500d4800003907032022040601c80d8091070000035601c4078000a54080d11041402e140650740e41c80c1c03940c0714045500c40038141540d241c07040622103072581418404c10f14590800b0b464034406214000c0716642040c0d12072409090108020009801c801c41aa402c06510003c0a50b407010f0a4403403901400840750f06 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 866761618 1250 866760368 866760371
    0xf090b10030f15080c030c0117010905090a06060e043e040e12070611040b0304110f09100905060303091c0609171b0c0a06140409020f0c07140d06091104 67
    0x130410700000102c80d100700390700702e045810074100480119441442c0403000c102074040d0380c00522100c24039401441e4000000b004465049100ea00e44070240d03025540502402c0d520b9000740028402c0b10412510101341d04100b5628074000812104072954000b00c802040c508641550309566072582c100038a20711151044414140c2d8480b800f0100b035020310803c94485103008040894400b07140241d80c102c1380c003101c405040d5a1103858503054070314a50406a4803d803c030080020642d10214902d008054022000e001c2c86d0618004400b201c4006e890726110358414002e072039007580c1d404516101d1038540c20014000c002d4a203001009000c0d04000101410220811904d4180c1680c020b40070b03204d103030f40b1282e00844142a0654a800c107070002150048030305202840064010800a0607000c80c20b40e20b540703042e560b10307822000c0760001606d0305004c1c040055040350540080007070f540603010046443c012910401c0c0003412414402c00020f003115240c403851800d01c07254100e0107040d4000580b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 866762868 1250 866761618 866761661
    0x309050a0507052106061c0b0115020c0102031c110d02070305031005180105121203102c010e0a18060c0305070e0102250b0d05010f090b10030f 63
    0x4001e9141c448a0081c28003482c803150400c4040b0701d510141440d0b00f440c1e40e002d0030301038440300b060001a11840000d070300000148890b241c00945119101c600a0904040343c100c00c0c80b40c450300905101407000d842e41194410300242d28481281c10001850380c083c800b000502c0e0050103030403051405040c40711445c42c0c0c40462140280750300000210311070115462582c0116842d8800c000d0300d00383c2014180051050080107121900300740c00b0b141c1400c80c0c00350803503402c2c030456003c2200540c0122a5405042e507070070740800490810b840482d50070700b015000c007060424002e0b40088000fa051088500c0343c0f40c4a00803549041140d8440d00c0c40c001201180d0112400b203081080c040d00c0300030070010011303250100007412580724807244100042d059001d0061030344003688001500c48545a00c4040c0c01444000041d56a9814020280424005400f090030b40c03501c26032040200956000f001001e00300840a0700760b03551251546060303420380c01c00064404209840310010040400a504008271a00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 866764118 1250 866762868 866762873
    0xc0519030c0b13050901150806031009050703060f050106050a0e060706240b16030c1a0115022e090f0b09070302030c06190f0203130b12090f030d0c0309050a 69
    0x80040000912010f40c540c2e14030f07078070800e00c46030041c2407041140202c901c500d1584000d100d8240d040c0c002a0003402c8594084c0501c3c4c0340012241800001c4600e50b10044003001040b410f80110142c09210702020000c0350b15042d0090018883c41c01d2030010411320502030686a0744500641c1e80d4030760000350403c580340000d54244400c000c6404881c00007180d03c500000c405d44a041142e00d15440c0c00003250350007010303940036201c403442c60f02c0c01c0b603d002d001e041c900c500492001d011802054684803003080f66a0300e910103810a02840185804d00d000b80f000380e52420024404040521012200001c108010381001401c0b6103a20a00508840c402e0060040f55800003030300c1d8054a000324151841d01050404000700751203090501c5002a0f102401056414045c1440883c010980d0064900d00030f200c403100c4c42c143c02e0640200111a60200302d45120410740c5a819600900c8a0010070705400f103109140d503207020b0703402c2d000b4041d91640180c00c01c061103604181c444c554060b088446a00591 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 866765368 1250 866764118 866764139
    0x30504081c0e0301060f091116082802071211030723060319050405120703020d09350a1406040201030b010804080904050c0f12160c0c0519030c 63
    0x356810000210b506126002902d0184907203800ca680314500700d40002e151254100c090041c2c5c401014201c0001c1c04141c200003128000001041e11600c00942d4805a2080d01da00c11a00d000314000e5103140c200d11404440c1e000030300503003520183d19809104292615080701110340901105406004084000441c0b0510340505030042c108803a11600660542c0288680ca00048814016241d0036003204600c00c03520394002a0803502800683e061610400c802d0907940d40031501c2200140d010301203a44500358002c070300201410010200c1035500108195803105101e03040c18540302000c441c4084a10503408102d140c14603580810b0684c1110707030300360200351600000c0303405030f011074101070743d40d15250301c40c46626208a6000800c1801e04d03080c1800d000c01024001d002c108083d108108417941c82e0b040308090302020040441c0c6000e03d28000d41d403074407282003c882460a02c9031509100000031026485013050ba035013134510031044801c6071032005100c032542d80040c225610102c0b001c03510580c40c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 866766618 1250 866765368 866765413
    0x20d030f0e0d080403080c09030a110105070209100e01170a02040b22020c1e0304030b070e060313060c03020c03120903040b04080f0106060234080717122503050408 72
    0x6c0d1243c818507a2004c0d0900f04610070703c40c2040d4107801030009940000c81e191103a004e460b030180f5000381041c107641d011680b0b850040d00c200c04074000801c010000307030a0300c82d0003602402004510160455084101c259925050080248119140c0e5611441d9403264084006002c5c0e078560362a650229203214040294890b00ca00c652600484100080381c0ca500d051007024050144000c0d40307005c0c0340d501d620526640c05012401042100c032450b00b1240d0352100958000c02ca004030301303002c5481034501407040350303948080d00050600501c10201c0c001400300503511030214240c01d04240780d5400320000d01b944a1a0052203041d40007090101c0d18410010398400030038030590007001504d441d40d030142d076100c0f0f101a0303134004010170404200c48005021f0b180408841c860f04140c0000303131201981c41c181a80c07a04140d01c0e040c0341c0c00d9528010b0b10200503c8028840c0c0072981e0f40751414003078110048603c1d8080c200d40c21000145a6403c041c4650b04a40c0280024825120000f08890300307025400382 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 866767868 1250 866766618 866766623
    0x100f02010f06060c0b0a0e120a0e01090303080c280309173a0c051e0304080702060c0f0607020a141b0906040902030f060a110406020d030f0e0d0804 65
    0x280c5007014511580d54810714050720019210201002e107a80c2c0c0366088000000c0c445218a034031407080e803c070440c0c1040741c4c00c9108015417142d91a2490a10010301e01f002004059040140102c004c0000c0380c3c0040070b49401000c4900620f43d0741d02c14080d00107200320900c0c42c40f60070480d50466a00420341c0b40d80302c9540207100e08610713840c410303c003200382d41d1078080c41c410041d801010562101091031080c1c00e41b903074141c034580c0000d264800020810308a4920b1100e80d00425800111b122898000c410b50403812228401801d0a504060701d0b00141b034016200001d019020004000312400380411030346070116580011144580341400b0000d4880407803400803900e81d2003880c0c240240c0c0c080494151052026402142207a9582104200c0e0380d05000d08400d400075581c030700340d0000d070b00d080c440e00b180702040340010601c60074134080030011070300f5490f02c6907280e41c0705210900550342e011602001c846c40514004c20034842e0082340b04024003400c00c1d004014481e06607207d0581c0c0e04840c05a10031030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 866769118 1250 866767868 866767871
    0x91523130b0d140f160e1f030603060b0a0614130b0c0706020d17060f0f060a050309060603010c05180a180f112a150903030108010b010c15021602100f0201 68
    0x840c4c40030310450441041d10841e000d10041e840140400c0d11070300b0454102d200003071102407490711003640648130304404034550001a0710748a041c01844814002d2000740241607400800345441c1c20300c003c1003200c0008880001c0d000002d0940021000c004031480a00214624a55140c0504070301390b985100d50f20a840140c0520072903130101d00d016807001319100f055804404510750fa40c00420440031540500943c0c455460968840300743c8400000d45100a41c98660f2966820710564003031800d103005011600c0390381016118110b03240d0100a5807440f81c0100c10010000701c103032000a041c544107402c11440080380202c544044942a0499500c0b011502801c021178071004000540920500c140454560303c0b02681110344030402021110380205607040d200c504001c8198241c50f4801503401c1d00f101d40c03006c001441100028418601c1400c0d0900b816082090743d6030b0703a40d075a0051100c654101c2c99002c03c44104030121800c10743d026544c000c1c006455600b012030090b0085609009500056 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 866770368 1250 866769118 866769121
    0x4060908070f0b070614190b0d020102120f0d110301031a0c1603030207300c030801060309030507121d030c090a020903030c0a03091523130b0d14 64
    0x803800403071024255540b0700b24040090382018501d00303056208080c1110b4840c0d0b2810800c174881d00d155a0240070311151441c610307080f20088041c205440e08a01c0c0d081c030900350041d043c001030b0f03000240b4007000c0e80d018090030340b5040a5100002180a0708108403003040c20035610340c2d9102c02810044d8140da02c43d40010804800c100c0c5954040c0f00221215407240303104001c8030301d1116001c2480c01815109181c094542410707603464841c01c008981c84001055540354100c03401d1194121258100d8040380f50404404042d61802402400180303d46410705644596003014140b00d6402c0b0781c100b030741044d400a042a07617403070020060b00040c15407e800c2000c952500b102460049000900e0002c014a441c1e040e41301c0310740301c400a5001e48403031503140c40f0403c4034041e03c00046c06000051802134964400729464502d4a92888000300480390401400180c061803080c004000314028107920300d001c6881e4506040600d60b03c40460f00440e61009000c18400c910298941040101810600c4c107013019 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 866771618 1250 866770368 866770379
    0xa050103121e05092b02031e060403030b0109030b15010206070f0903080a0c0506010b090906060c1f060f09021b060f1f05040603030e01020c091009150515040609 71
    0x5400465154200300320b09051500c948282c002d04400980240342d01c48907240c803070000c3d950440c40380c80d6402c42c0584204840a51500b44081c100e040028080301058502e0780c0340341e41c0c07100b5000308000d040c1a07548070098840e034481c1c0c01010107103901150800190611500222a0703d0460544070300510400000528841c030031803171298241c101c0c1e120300c021a070842d5201026600000362500c1004a5440440d010420402946000f42185500302e0707550f0f04880140080d216006001c280103002c00c0001d545c0c20358000407288403900320044042d20450041d071680001d494554002c0c4240d16002d030f80402e800880c0d9000b800101c1c40d0071207002c4c10051030015503031500e00480304240c00f00280c00004041030918442005104000101c88001c281c80301d0000c0e0440c2c0464205034005404080c003800340c1d5804003e9059a5081200c038102d59107400c1854099020043c0603000d8111345074890000c030200300b5964000503000080c034404c00c00ba40d0002142c050f4200b4441c4900280915500060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 866772868 1250 866771618 866771627
    0x120b0705070b070221090307091805070303111212040b04051528050c09010c21080106030e1626010c0c1505010b04050f0d0c0320010207080a030818060a05010312 71
    0x1c1b4000c0c0900a054450714221040c03004001200400e04001da0901d102070004800b48220f4001d58800e0319012424041d0070300c803528200b241e000082d2030070000c1040b140c11004441e2000d500981c45543e009459079686011810300c291510344080c05420001409408400311906119114620244c00050382c924003050090310000c1d60581c240b4001000000f00311752141c071858501c00c2c06503120301c14681a003a00848100002180980000c500c0c9005001295140c081c0d1040080060014090704400d181c4014010420344a0f5501e8a606209078148030000312401d820304040c440000c0008118644029140f0b141880044800c1d0130f10009218a4203824414103060b540040003807810281000c06011103c080340c2c2030640e0101c45502000b00041c030754891840514450442c91032851030500411440b00c101140e158155045200240008140019008a03003500b5141035880c0f87c0f5035020380102403141c1c0d00050500e004100411400c00810b800460481f88100c0384a10320781180d600454 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 866774118 1250 866772868 866772877
    0xb030a140c030a0b011107090c030e210a110307050d0f0f17060d0605130c05010f0c301701051005031b0f0c0106030b0709120b0705070b070221 63
    0x2044001c060020400b010590f501c800607130703401030400700308008164480c01e180804980c400e400b95034498a00c13040c10f030351601030b80785501e4090004103500c102c09000301e00c1221103032141202c038003c04540d0000f580e1141900c6031031b850400301540d43d40ca40300e083c02911030180c22001d0021401030048160200e02c00c04003031a1a8071304d0360380d0002e0000d035500305203050700d00501440d41c0720400700c240300d0115000e403044034022034800082c5600032407549171200440c00c2a5002c64140030120a49000c0b59401c00701444006500064016601d9501d044101c084609641e4007000b10341200c1d0004a82d0340c001c4c100000d8102c0e601304840240c8c0e40c550400003480303622041c540000300c003800030030a0984c265001400003d4074054242c24454666140030580d00082940301003603448540030000d1080300201642c21240918044d507145007005c0001c16030225054004020128000018070814800e00540320340d503902850b07c114a040c540002940e51002426440c0c030035104140304002c039840c0f0380468 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 866775368 1250 866774118 866774131
    0x3120c0a05160b0409180b09011a220b0d0602160605060a0303120b282d05010f050c06010311090f07120207050a0221060c0307140d0b04060b030a14 65
    0x11407500717040108102c00707046c1c11301b10a0104c4461654a600241d00241001d110b603100b41d00001e40c00b4510500a2120800035016074012403164a52075402c1300100400c260452128101080121403600030400c03e41074010060308181c0701141d018500c8882760b61800c4d06d10f0143c20700340081d0700c400301000349943c031520006001c2000d01a18011440554100b50005040249044203080c500704441c0c8a501035415607030b002c0120075209002041d82c2003903041407560000e0311040c2060034a146501c03660054004d180c144615014265488e62040f4200c07168001e03504180c59040d60b403440c15400ca15844425584109502030010b000c900034910f44a221300e500e40e45665082e50303400ca40320020340c400c60040d1210300a8111081c0540c80b40b031103080c07100c814010501324a841c43d504a0f41020303000341c00c50560302030030410f00c9a0706600054503018620303004070780d9170795041300c40c0c40700010b200840109030082c0c2820350011714400c940001c1c0d40f19240b441c0701403054000d0b480c07052110360401ca905 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 866776618 1250 866775368 866775389
    0x10f0207050a12020f0a08030d0c0801080a17071b0302010e0607170903030f22060903030e060d06120c06020d02150a020a03110c01050108010b0a0501080f0603120c0a0516 75
    0x10000603146804000c3c81a00240c002405c0018650208248100e01c1d00250682e6000160844c0001c015101d40c401200703c5192441e010750600b00465102c0b506010041d0201c0e080d07401030381c4448054411a0712280d40b00d002c55164545144101040309118030007a4040b0381c2c0081c120f011800c1102c11102c500d0386c005107d00e00407804121480d8190094002550540300070701041c00190315240041c940c4183c2e000a103800d4000103919240d0505903600590f0030022266403c00000f80c0140103d0041c600441c5d1103070701c43e5a02c03406140203204542c40502040c41c210001c006225800c0f039403000750340c0c1c030303900303641c128102182e0a03695071058984c500629070740d08000030000303100e650240018000030301d03001c0b03044580f1070341540b0075401c9045000f40c2a5034074801003207200424496001c842509580c410741d02860580041d0038120001e01d50084a84020700007001c81d50140040118402c07014105611148041402c6583c1c030784600c03003125103200c0c0c1880e42000c04020300d916130448102000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 866777868 1250 866776618 866776639
    0xb01140304120809011e021c02040305030301120213060b070201023d02070b0403171b030a02070c0506130603060b0301140d030201090c0e04113f060a0b010f020705 72
    0xd00700c92000c40100140703559542c8812500011081b413011b003103000988000943c42c2c450207500a150075006036080401540b040000300001400071003905e0449039244000c3c00614290300210302c10b1058880b02541107450828045001101400901342d114001e07400c80b41d640d070b0440c0c086011030811008159000c100f0320780484910038100c4d08503030136000803030025052440650b101d040c032032001d980072004603426002d0112402c1d041500251b01050080800d0540e0806900718555840041c3c01c10407101e400042d82014400702c195035200a2501800040d50348011142c018544585802003000190a090000540e03d1240064a0680d82e8007810003460384440010441b440c142ca0f04100d0655480d000c11002244004503520010f000c01d0b141d40c150391810745004070b42c0b0b20550b100d55104500000c0000e4000704100c26412110002c860306203880300c0495210303c42c2e21030409100055101d68420010810a250809080340e007007a2142c184501303036000166110f881034003c0340d07044242c680 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 866779118 1250 866777868 866777903
    0x10f0603021c0615081e0607090504050402300f060105131e02040306021b24070504030f05011a0a0b0304060c032301030507172116060b01140304 64
    0xc48000e00e00e1040d18001443d0340204ea800314501030f5a0320003042c940000300404443c2a401e01e0421048610740050002468183c0000c1d00e548580d001d09400b03070790b41d40b00081c00c54517041a80100520414540f0760805903a4a2010000c1140c2d80641074600464424103051040028190706aa1000f0007141c00c3e00068a424002001c0c2030b071040e07181080c1041c0c400c2504d08244000d0000d18018800540d0314154040c209a0441c0c10701090b90305035000d01c050071240703a400740d040701e00d80750071103040c1d07481d80c40f460f8040350700703000d2030700702920900102c9007620800405500c811140840303110194a808099810884095150710400820f14006c100140019060f40c0c400c01143e40780742000142e40d0325120300424102030142968005181150040c410320200300148002040e0194444080c100f05180032034440500d608001c1d182d104901520b6481d04c00e80d410f4490416200300ca2410306146400e10340c0182c00c0850340c0034045030303401c000300400d0302d00074045a04c01c1390003184000441403402c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 866780368 1250 866779118 866779159
    0xc03060a0e070e0708010f060923011e0e03010e07080a120306030c15020c090603030702150d090f0b0610051602030c04020309010b040b1008040803070309080703030e010f060302 78
    0x69440015800340a20103c3c1655205007464002d0801d0b5a42c241c443d810b00c0c404140200315500003030140301600c08200281c0e80560040fa44040a4108031401d03c050040180d0701441c0511207460701c6100c208c140d054559106c1c8011241c89c100f00c0c002c0c400100341c03562340e948518550042103400e400c01d00b684000718107400c910304901c5070145400640030343e903038464201d5602503800c001e1040000801c6040c807158100120440702004541d1005107080000029682e8800e0450080c0503076040303600000c16411960585115040c1d0803400d0005088501d04000c140d2400701007147c1c10142800894098104294006d001015075124070f0b14141c40300c4641309552075020802c030386c18401e41152548540b940e0014600551140c03001268078450101000180ca005040d400c0c001c1c00c010039068070703082d400748c400c030340058100c0c480d980d0300d803500c160843c0a002002c4020300130394000944c180803d80d040c1d00c4115510446402046203841862441003911060302c0040e40c45000300c6ca01c1200030b03004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 866781618 1250 866780368 866780381
    0xf080c06071401110c01050a0506010e01111c050a02070e0705030c0912011509060506120a180609051c0309020d0b0702010e062a0403120309020409080c0106170c03060a 74
    0xa8203011410020303401e20035007901c001c210b607603900030ba011170143e0801c0000d01509403ca031303005070184080c0c540344c0e000a01c800f240c44c20301410040500e51240e181007043c4411114801000c00e28142840300d070002500d1640588192030052040b0383c2d000503118620f47d0500d0080203030385d03030381440d607103c0d034a500392503030400303408940e000d490043c603440d11030002d22585001101c00e40201410300e1404400d00211051607000502524040000043c0d024443c1c3d80264030955401e80001d14160001a540ca445441c1a004000c1071400c41d0090600800040c001d043c44110011810f00d51490359044083c7c454483d0002d40040e02040501c0015040810791a40f184062000107010303070f6075918040c6040015640d1901c0185194290040312403c03203003000b0b0541002c100a498146075a8901400744c58040044041540c4d692000c0115030381d07608985101c98000c4180764440e0403c0d4500e60090541e4031074128884204030048240920200c0c0da1103035584010007410765940c4203080d0360040c006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 866782868 1250 866781618 866781623
    0x306020a0e03010903110622140a1704080105071e14090a0f090f020306010f0c0c09060603050a0606030b0102070e0c040e0103080714011404030c02040609020c01090c0f080c0607 78
    0x25200c100711140d4809200d20740c40c0300d00035603800514500c880b0f601814210080e00702d505a441550750700a0340411244104101a44051078412800c000ca80fa5814507180c164000c01c01840f2242c007034803007020b540182043e64900f10007006140c917091400d40d103030049014074070294400c00c443c0d0900a80201d20540001c500e4284d03040c681000c610008001c0b0085800c418101240110244440480c9105071885d90705031800c01c40c030b1414594006003000100b104120100207400e42c0754000c10100b5092100100f55800d400d0205981f1104090080c00046903280f200601d40003000400d40c1c0b04e40100c3d502406e040e00a401080d04004d0030f6031400310000e02c0d850030310100b000b00240f602c4090070304900940c0281c1080c3e403035610354540700105c222104d4111081da810b0180740010311038550040b81d0001c2e03060400c0001c6d4810ae2001c503000c1c08040d400b03501828404181c42c403403110190080b1070103d01ca101c20140494994104000e800120b01a07641c0343d500c60701d410101800c0c00c41c014141c4a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 866784118 1250 866782868 866782877
    0x180f1517070b0d1d062e0503030d23060603010b251b060915050703210507230d020912010207031701050405090c060d0f1109180f010306020a 62
    0x1500c070500c01055078000c3d0b540b064440e41d0b5807510240d0707141020002c0c034507602000240c031050400300d80034180e000350910b50f9240c0c00040201220503400c5054400000c10000d41503c2c2c41c0c0000141e59002000402c2c1002400f03001c00003c0c850030042c0440b06881100000d10060075642080040c658a170400d500007403000300d00000070480382e0b00e00700a032041c0c1c41c8a01e2240c0a4042207040c0e0f0543c201d01607002c03070284018104188904142c2d41c01c20000c0400310b01c1c0050300c0301c20a00301100c0340030848924260108140d00c00f00144825508030324451129a2a00b8040d0b1b4013009000c0c440590f00c85214600100510540b130700700c2d447e82c0007484c44441c000c2100c110000c2d10b2450b942280e10901003140412038200f40803a2110a081f515801070030202c2e410007403442d2a10720103440388503100342c03d44200c00020f080901d58076250302c020b410310380310307403041205a070b1142d02d01680b07621500116114440008440203c1903600c03242c24495030403000100d540e41d1071580ca6002a4108045c03041c10701 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 866785368 1250 866784118 866784133
    0xc0f08060f3f030a0503101206060812070803060d39050a0803030f0c22080f0106030203070605030a0204170c121c050705070b0301180f1517 62
    0x59440301440e186841ca0010500d00b481201003102500310320615510184110b40e00c1401c080501c04001d5621a21850611a64a0f44c07456416500135041360001156a0340c050703000c00902078103500110a990401c0101e800c80035900070406202d01070940300400c20b0300100009059403c0c01459980c0f000c1c070a030940f07008107500942c6003000f0b041c0c502441c0380f4202840c4491001e0b0b244910f1a1004290644d4000e18a50911300082c2e10ba12000308401400e900d03641c0442c0800e15140d08840c100c100d00c0030700d99540c60701e034018814040d5040c41020203600ca0030507900307103110040c0700c2d000450f58010004c24403d80b4001003600c150b0401020009015030a01000132059003510f600c101c044a01405064503580c3d110420031110851070000d6915401240d40002c1c0e41c81c000241d49000d252400c0c681d0712440e462409070301c0e007099a0803180d0f89402c040000141000d8000044038054507050b400d2000d50880c4a081c0304541c0038864400014002c200d0401880708003000c0400309190140039510103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 866786618 1250 866785368 866785399
    0xa14130f1103040b070f2c3303060d020d03030209040c21091e26030429010608090109020406031103120f2b0c0c150c0f0806 55
    0x101c541c280015100010004200001c0000c0003005650203103440c20801101100c808008040300c1070050070480340322401d842c11600d140881045010b04100402d244040303074a5486d808440045541c683c030791100b54120300140c0032083c0c02a00e10030b4001401c055900e034420740801407080004002036051650820407116035444034081c4e21542c480c181c0758011240c00a106814040e00700c03145901c90145440d14030000100084280710042642110f200c0401e00c85081c081040b46084441842945c088907a0241140b8903901031445240070306545840c05120010003603000b4241d4034841ea0f000540c2c4010b2000c2c0d40101045070308050f02f400009142400d42e030214003298107a4006896418940850019601e41000b08040030309c13085241da03080c94002d00d0283c6290081007102000320a519020103441c2406003080c0c011602c4c1d0f000244059280700ca00a4a100c1842805071280303080c00c0c0f08092441014065107030312061036030301c00c1c505421800045031144000b902c0c444d481404400d41042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 866787868 1250 866786618 866786621
    0x71106040b0c2a090103061104080601290c030d151205010e010b0a0e0103141c090302030c04020a170402030f030a020c030105130507180623030c0a14130f 68
    0xb0081c0329003004000c0143e040340e0100348a020441d071100e440404289500d05a00e40d48049411a80d1226022803072521080d02052140a44d40140d4001c0c4070701000081d40d4911003209003081d01c040c50400c1200e12504038407581510510078141d100b41d10400600c68042111f42c880c8001d50342106000001c6070f02c49101182e0120080416652a03440390740c003541803202032140c0384070104101d41e03058100345020920601280d0501c009800c03546032010f150400d52081c0b100c10220401c0e951040e450782c100c080c003d8040f0381280416030191003119141c0c1a0790400384200c603807030b0041e034640040c030302111520300400060040089070180a42000071840c0e001c01c00203080c61062310780240c202408420141800c54400403e00e100300074901407046d000c00c00c0810b440d029030300654001142c02ca24524218040d00444d4000340e01d00c61625111001e51400c07010706900841c084098540154281042180c0daa035103006140f907619022750311000c2c40c41c00d100034605065208130b010034015400c064120 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 866789118 1250 866787868 866787877
    0xb1e040305011505121f02070c0e160f0e0d050a021003141b0f031e01060c020111070602030f072108060307080303010e0f0703090210110106050301020c03071106040b 73
    0x740c0c80d0b91075610b40c5100c10180b108810180100b55150200d0301095112141d0311042e5420036002e4603143c0300c41d44008034444e0100c406468111940d40480d550f80c0c82c1c2c19503114002c90305500d00c07865070704000b0000f922036180343c1c900c81d03000e82e130b8103801c581244d0810181101c20074048a691183e90300f12070041c3c0300d01d100360034103180b541c6002540c00c19186118483c03610041c801c031000c0745240b0007440c4012141c000c0d5902c1a11035032480d81c41c0c0c0d031201d20a4005000c6030b46100c4040204000000341c00303500241401c0c3c2c8520031b0b41c0d850f2038000c0c601c0b40310769580a9805468023503001402448800386500000c0c1002c18050b80c00c41903170000a211142c40c40e00300d541034000181d81030301001200c0c01e08006200c0100303000f030000d5140d0340c90580c0341e5605110283c8201c1c0c84000d101c000c6030302c07207100350070821017036030000c04c45600d03000007a201424102c003504071010070794200440003460385418420354981c421000701a61800d920f0390f4035000c081410200081d44481d040c80041540c004110150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 866790368 1250 866789118 866789123
    0x1b01020307060f0f1a0a152106090b190510051c0203091504080301061206030623010f0b030606030405030c0601080318090105061803190c030b010f030209010b1e0403 73
    0x41e013882c03a426800a9a501c0c040300051a40c03880325001094542c611400c00f1242c8002004151000d80c2508070346180c00d8008074560440c00c03600e0904000041d0380004201c1d4024401000b08007000824803c80f00a4105d824603080407a09041069080811102440c034a00d450300ca85000c41100c0001c000182c4079030080465903001c810031800341c0d800c00c0100540100d00520580c07600e840d41e520951440140542c00401c84491030107042c0c0b03406504204095540715109001c0c0c491060300c00611a610303003400310b4800040100000d091107070308c0c10540c00d840b0b40d500c1c498030b107603141401e125007580003a200711034500c0100041c0c0403031710007070017014083c140400c05159900791441086018503401c3d05030300d12815103100100200e582c6c0c03004580080000715002c101c5401600000f81c10903600c8506a455415400150b03410020401c0d1000306807442104483d140782d1300d5a4a06a0038416400000d40003102100180b00468424024240e00c5944011510b0002d015120a8043c2e80159104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 866791618 1250 866790368 866790371
    0x712020912060f09030c10020c010b09010902090a050a1203031806050c0d0c090b0403261803070801020309151b040620010e0d120b1806180402031b01020307060f 71
    0x6100c1d442c16410090354000190130300039400c0410031000d1a89801e401400610140d50004e104458030500b074212b03440450008142200799179443c903c030b10281d800520110722800784071102090919045502c0700030341d000d8880d2081074440ba0390702500201101003032141e1440300e00701c0e9000006d909019040c41040f0000f05641c89407032070550703c0705556100a00b40e06203c5101000d100143d4407000b990308480c4c12400c44030410724500d81501a100c3c44044288010400152200e0b03c402e6132502c0e40c0c0710100a030216002036907a8801da50803804140c40c0350045802c90004255206202002d107600701000c0714a01303190f0304071540c46108541c01907010f5408900c00800a0846898506221440201500c02400408501e492454030780314082601400c0c0a8460300c04034014071f2a40c42a00c65501c00f8101c5c901c0711100700844464001c04440d914031402111750100e5a00c15501c80442c0100c4d405001806801d00c5e83d0400d0000402c1802c50710304610040c031440002c40c006004601001d03604810 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 866792868 1250 866791618 866791621
    0x4111e091203041703161e0506090105180601080705010509130c0816030e0c04020d0b0d080c0f03070308010506030612030a0c061a011d04020417010501090c1106071202091206 77
    0x400d111004c500040c91203030001d00000f1100d07403800480200c0950700038000a070382184040000403580950314047e24511507503040213510141548180d009031380183c030502e2080075000141390342c0d107030902400460381c2048000700300039402407010340a4010010040307a1071240e918840700c01c81e0030711482c0c0300010304140107204d411940c00c02644008101d030318007844071060782d80000c0d5858180c0300c071060180780d000588810900c00c0b6440071000f00e0004001000306540390038601407541000019007914040e100399046514400802c8079120b551540301c841d60303a8130b80000c1041c9900002c240035084204e501c01c454804106100400d40d0421503102d811007805070307040a60840b00d54546506201c0d1a428983c40c2ca0317070700540740340d1030790001101041c102010000890041e000b282d215071410149803070301840b0740710190880341c162080d0b00001c02076a01900c1085411032080a05500b56070810404100380307a104c0c0c6a0710303000c0c08c0d94040252903d003850b00032a2545842100c0508260002e90 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 866794118 1250 866792868 866792879
    0x14031c091805091f06052205010605190c0201021009200109141314040f0510020f04060806010c0206040906050102121809101e050f04111e09120304 65
    0xc40100c514003400000b08141d01d841081c007a50303011401100324881600c0308103400d4440c0e481c0c200c61701400700a00001c0300d1040040c0c181d0b0b19041c03000c11049056041000100740144900f0a50700340122000e0303041c01408400d40142d514500021003641107016040d2200040c4006001d406041813040403410807402c9181d2a003400c5181c820101c40c1001203280080005c080b00c3c012180f601502110041403005802c440750000300522160040380507021b000b00401c0c0300c1302000e80c06c070140c090416107880c20a8000c080d0101e126030790800c0c0304510280800c0c040d003071142c10304607030040c010b0600c005c0711780850b00010380b10741003644030640c1507440c3c2000340310b6075074140304140140581041d100d003811107180e81c0b4600740d0b07161000c0328000c9030440700041e03141c6c040c007001a0081201c2205145130f4050f213180440515200e003d4180141104001e20625042511406083c1440070000c1410301c01c0d4415483d02e800c0c003110140074010010301008441c3d54400e40c03891b0011010800a41d0341e2403611 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 866795368 1250 866794118 866794139
    0xa1e091109040e0c060f0d06080a03111608030703031e050c0d1419020c0307120302040f050931022d091009020f07050a060608060108070f14031c09 65
    0x403025000203410100481c12141c0307a0b9410756071046c0c80410040d40f00d0801c1c02c0c00030010031165000001c0e6120340121074083c0340c6c01c6040c0e8a01c03034407110240d950ba86030003100d40d0300d0700c5460f00c2581c45030303442003240c00301103480b9510005070040790054102074442086121000c0d5502654000c81000c0002000f2104a255104120010801d10405030251030484954042d500c18840c400040c0c0b900007411020f195028012901c849170303c541040031002e00c10710000c00940050150040f043c0840101182c1880c140320414424200442d0091081d1150b01286010300000d04020200c0c0131601407000040e91840d4040b929403d241d81c0140000720024240d110301c40d01480120b02032a0840b0900800304409d81c1101c090316001c18001d640c0304114125001c4038400c100c0050240d0040c1215101040b0f0310f03400802c203c030080811140107980716650b43e0f0f12a85070340315042031682c50381001c000c036042030260044d001c3c4004007131700c05084815603c07419104003918900001510311400344410144c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 866796618 1250 866795368 866795381
    0x130e0708071d0303030c070503092713110f03190501230c07080705030d0501120605070305060d0605090a02040504050f100603030f0c020a05120a030206150a1e09110904 74
    0x2901d42031041407400b140030944034030026000550640e000180001070100c100308880c540c1c100a84540445080460710380c00d854103d840800d0218800710100315102150455449500c2e04100226550700141d0200300e60540c511302c141d0740500074400b444c0c20300032046038005c44440c040c20001c10f0f00e480c0c44590320303c02c551a00b104290101c22005000c08180d64006a800455021706c006d652a415402c1903440d501611406841090414002089028804c015070031894031a03074003844540c640c49410f50690368121415900710800000d02000304070741740c00541c1c0040030441075881003040c1c0d402090607610100e505503810390010320050361420b001c205514854078038103420000d0a00356500200180340c00300303c0c8410064480310920656a603210803000038100249003031602c109005085032501d40d0b507202640580949000945416652142c5022094004008444090070065840380d89000e0010504c4d20709001240850403a0203032040071401000701c55100e46171862001084145d440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 866797868 1250 866796618 866796647
    0x1403010608010c0807050d022808070f121a03100209151615020c07061d060c19080708030702152511010207021801090b09040b0705130e070807 63
    0x94006104410f9078051109900502545000c50342d41c841000c29001134000d12610700700b0041102c00032038408540c50300146e10200103840e001c0c1d1680d101c2c03209680c521805140640440c0010700c052a01c2800340c5e02804407141c00c60001c180c07104001c3e0100f85451011680c092060b58005000c03480e610b041d210340b4185150458100d454100c08101c001c00d200001500242400711100301c00c061444250142c1d40c401c100721044881c10340d559000100b48003461110029010040070003001e02e42001822a641c10110f03000601c403011010f60b43da03401d070310340d0a0150742c806014864400040e04074001140685e080740c6c000c0c2020704010010301801580034182d03074280841140200d8210034044850b014042c014200300c1301e0103409410603806803003004070085d44040d204400000007045400c15906850194138208a040a064184910040300742c80c05001d51416500084206210700001c00310000b040458464080c1c2c0c501d04240060415180e02000c0381c0314500b004962640041d003c3c0e81c420 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 866799118 1250 866797868 866797871
    0x50f04210c0b04140d180501030606170a0b0d0c0e0708060f0d0c1a120907080615060d0204090c1713020d02030106080d052d040e130507140301060801 66
    0x8401040503000148205006240c02c01c0c010001c1d06203d54034002c28003c4802d4810381d80c205040d840020250210648844004a5240404241d651081c032a245c19101c0e540ca605d0211010107052035240e54006009481c0140c8540c5d1501040d01c1d80014600c00c14400d05019402c1030400380740c840c0400e001003550f8104036400f8100101651a0300c400064500151002011560b071410986200d0545402c0040c2915958044c8070350004000010300080001c56190061070710350a078419150750a9200c1d1011903032000c00401c4030b034940c4215214206800400c500c1c40e00d0521228042a40c005a01c032900c542c1c0d46c0c00c100f180c0184c004030a42c0250a131204041030324500400801020441084082d0184030300c01c048804548095100d540a031400c1011a103404500007001422503125034150800102c3d04d00c40d10583c420b08003620700c0ea0400c0c040c1c24a007000d0a00c84640060003000f0301c00610b07140060f4150020600030b2000c840940000848840360b010090181420f59100764400b80d600c1e07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 866800368 1250 866799118 866799173
    0xa081006092007051e0307020906030312010b181c022112090118030506061009180209060706140a0b0a030203070510090e01140411031314010e01050f04 67
    0xc000303110b40001c062011400c00b5849102900342a49480d40c654024003000c20052000d40c0105000000b0b4a103551084a0b00c220303650320304041c90740301d0290110a54156040c00014401100d5110107099a071200f81c080c48075000020780014030410398050048080c521480c400c00650070402c448200c1303024a03100506810802440c56a510f610301c1e0010130065201060414540e8442c2d00f40b4405a002080c0084e1081d48a08200c1d850314002d40b0410320030148000e41001060042c0e24000c201c502030380e2154440da40e10420100650320062005030712000c200120800641d481c8240080c0c4041071014140c54030f0030046043c04c03100c001c658648101d5000b001000140c3e0f0000b40b03e01a2681960a5401894241c4099411801c80d800000740c80342160008510300215000c000320394481254240801345000d20b11046920094550300c1200540d0390020011070046040307609070a80c810700002d41c3d010074031031140c00c454040d980c0d54059004c201c148400c0c40300a81d104038a42c11030507194040d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 866801618 1250 866800368 866800391
    0x3090a050906061c0c111f050c041509050901080f1b0a080712031d010c020f01050c12040906050a0f2309040602070624050105070606050a08100609 65
    0x914120311a581c07050700d14600003281510782000b6a00d10b07032800f80c4042c00300c0740700390440701c06080d0f80405200014804d8000d0300c2003120000d40a1109003c080f07130940100d40001c44032001c1c020003403403200c5204041000040d2480d5042d06003844140301c4da00c00d181e4a040c2420062010810303484240c40f944804043c211080010a0b9100e081e500309108440008040001c5640c00b180d5621900d410301501400051020384030b0b48a44020303102c1c0c3e4038205c0046a03030b2801ca01482030623903254001030f03120300b4400050524800d00481740d1814144103081c44040c901d1549011200d04a2880c0040049000c0022604501418000d001c0840d100c120280c10000790801840b01d5110741d03400f80d0328074000b0040c0002035650001980201421001c490f10f050300f07026000c2e520008040311031074944400e01590a40c01448042d40180910320440d5003440e2400440ea59001350200345d5220341d030350f540000c960742c66441d02c00090a54102901850280c07038070020032581b10f075000d02401c9041c560b20621 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 866802868 1250 866801618 866801629
    0x20c03070e06040b03030c0615010305250c0c0909150e1c090f0e04150504021c080d0911010807110304031e0c0b13120803040204270606060f020309 65
    0x40d90020703141a403199a418002070080e0040c40a50358050000003146c100c241d03400310b0560701c02d200303a05072044254112310044085038404c4410f21506c407004107a4001c007441e10b5180301c01d00c200f00d00d48200725034000d40303820580400742d078010305200e50755100810401c8043c141c0c000d000421010204a05440301e128181c03218440c441d0455041c015203c1029001d0103000400094051044503992040e11821101c0c0381d22400e4805441c840c51442c103102c41c05856000382e510903940500130060000c00d0388040d03c03c0041c00c0a00301d68500c0180624101c40d40706200321280c45024540100c00700165500240a441000c1c000008200b583d614075180100e00004450459501450108038a880300c10081c0111031051001031030306400100000c0ca0070003450140c002d25409000301c09a4030f42e40c050300302d10481c14082c02048410244000f4015207000ea10411401c51020105034264103c00c4e0100302031000f0002c1140e819581c4c0005000c10f95208006401c441e500340000c51616103244001a03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 866804118 1250 866802868 866802883
    0x50103112106011103040605033102100c05060f04030e01020715050319022205060a080609060a03050601090903021b03030720041503061103070909020a090e041b06020c03 75
    0x12001000c0c1c010803166403041d811100242d00542c00c2d1703600c0300d8650200800d943c3c0241d8800d0300d401c0c40c0c2000e80b00d50a804000142c04484c2c0e003414201400b0f026400d01c440320383d222151000b4490b807941d80b400400c40c107100b0503100d41020038a614440c038103441c0140190300c2004d8042d0447d4000c650910003881ca15820b0f078146542030800030b45903030361111244005288081f03106d480b0350010036039030301800d515110b916170700310b5500b20801c1c000d844106008560040256240004000743e02003801804c001d52042e400c49000b50808140a4070303501e806103405000c0e030144601580c0d40741c1c20003d040d41401902c07028446039807003c05400d08840001d6982c002c045000d44103146c0c1221410004110100d0340b03400c00b00c050802e200d2880d000c0d03811041c54007a84400d40d0000d05103045119204201c5084921601c095142c0762905070810980d0002500500e106105010b94004049000d02d0240f800c60300c910301c40d52000c001c1116281501c0c003105850751091081d503018081c601059540032a854 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 866805368 1250 866804118 866804167
    0xe0103020907030e011d01090b0109051e10080d020a0c05030705061b1e0c0a0801110406050c010b060d1d120a0f03060b0c150723070f02090c0405010311 67
    0x10901304042518180105007418444003070250070760070000d24201c19044002401d018160911b26070382c2c0d503111101581e004684030030740300b80313040c0e20307226450701d400f91141e0041e061280e0004c03031588480e01c00e4a401c1c0c02c1f801c00805a40668a818104415007450001070581034010700000c614100208065006002c91502c00351907200500003005e908102c000c011481c1d0441c44940d02120b030090940310143c04500d14011151036201040a650500a17881c05403280031004e1f240a01d002c100312105c5c0c20039510354180303540b201c0c040e03d255941c201c00703000b4031000c802000620303440e8804080c42e00401180410803030380140807040c0032030306d451040d681c0c8140c00e414510040071004070120000c1c560303500700404030b14010810310241d9000244550316a01450401a46501e882c00f00340c51005101038003904c0a1852501111810000f0340500702e6244988a01268464503600066508004852158000f040440c04008a6a250150b02d20012000340348910b80214010030313210803601980c1d00d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 866806618 1250 866805368 866805371
    0x603020304110901060306061b2001021c0302090418051b04020c011802030c0315011a040e1305010c05070b040b04030903080c060f0c0c0d120e0f03070c0e010302090703 74
    0xe00b0300c00c12145020350b11400400c01c1001d9a150794020703000341010702860b00003d000d00345030000e4034503507a503240196403c03094500322120051000c600c50400707491424110b00415111080088030b1500f680e140250649025803a10360315800e002c01c4071044504810200107030804c281c00310340041444240d449164131040f81f082e5a10740480c019124000c8850740b15031a02c076242e00d004208922400300d1701e100300e00b0350b82c110740d24104242c1d070384881e1481c00e6030040b0400c3c0104501011450710207580024940c41d14181036036a80314103000700d801c440328070503a101040203008102086c80f071040d170103465050113414074046490b001740d4040000c6c001054001002c021809060040d2080402540d0155829503121000b112498403000141e841c02c1049420300702151045820500b0b55a4807132501c0010071f68031a40305070807106d0816545820541941d1a0820040c03440107005129a01c1803440003540d80710a1450107042c00c07002913024251401040780140700503610683d980f40c0001d06440c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 866807868 1250 866806618 866806621
    0x10b030d110c1f0e060f040f1a03010510030b0f0d1407210f080c0a03091505031306020d140a060602101109060c03161406060415050d0f050d02010209090a021306030203 74
    0x1715950388216031200c0e0007200040b4000941d510000300d01d206036480203d00310003000e0221604041c6000a0040c00c1d0b00104501500c0d51240c86a0b02000d01c18000070007580e071464022000c40c1c0740500403c0c0640712200c00c10813444440200304010340081c18002206078810111042e41e03011695100c00c028104e01c4850003080511000c84103444909910300180d4640542924002e8910809449040510481c080349081a035000348250703841101d00341036180e0364684503592500298041d00c12211250f41e1512034019861094841030f129034588940040c546007420406032501c1400210040c006003000300e01d01441104e03409444038000700b902d071030780ca41500b10010b43c02d6004619032969022180740c03109003480780403442c40a8460100b170690701075031079100901003580e0080c4c600c980044030f04803042060342810040102c1c854082c1821200040e4203a46190600c0715000b1402d00507900400d042100e864040700c01600a0107c617000c40c0303049881c039107103080c5e4541d5108803010701d82d0100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 866809118 1250 866807868 866807897
    0x30209070c020d0813061803020102070e06040f0906021b0703020d0b090f060a0603060501090b0d08090604180c0f02510a11131403010b030d110c1f 65
    0x4900c03030300f00c0d5214443d55241c002104032400315903460700c903000024410385e030b8140080c0e00550350403050701c0d0180d01404074907091003070400b850900605500e402c03594420550400150030310600c0c50051090704090380d80d8516442d141820700d0398001c107030741c00d8220301c0c0708000582d290b88600301c410364088850005596507181c40390030084007a004203880e0059804200c00410070364406000c0d240b040504005903600c83d0100400c070781e4100070964102c06000400b0020600741d0002d840041e00040226251944800c10047c000030600b44401c1c580c3c1d00c40742400300701038006088a0300c1903041d2005042d80b07200c0200e0a02e0401c403001d03102c4051f280801412840c4609124a0003030300c0d020408145620600500c00446170004a580900391031901004030307000d00440003100c0d03402007941c0110341c40a0424201c55101c83e032585885505659903c41d011503031710300f80080305c9a00f020b0748403205041101100c2505106c04118200e100f6540b8078050390b0b603419001f01c000300310101c0703140034146401c415 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 866810368 1250 866809118 866809129
    0x1d0d0c1401060501080135070806011409041b05040606030209040c0212030708060a030b07020d02010e030f04030b061306031b050d0c09051e0c0903070518061c0605010902070b10030209070c02 84
    0x1a40d10050b00712000047c084842ca00003480030031181c03100300b00d88160b0703a1880d1707030087d0801400d0007607440341012010401080890702d83c00060a0348050700214075540314001800c4900781c0d07000c980032a40110b034001051134548104140011140090b24440c4011a08542c041c0b2008010a082c8003402c40840e01617120400002c010715444040c1c0395084c20b0880010f560380360303a40c0c0f42000542c01c01000c002100b00200594030480300401241d810581543d903945491f28004150303a41181003000b20707806915060185600560064100c040280b030700042041c501c0513070350040b0b4050070010543c40d00141030602c40504450741c5800004071500c0342c00070301c100a6806034410004080040601028940110081090f200100c080328207155480741804411080909800c05001c08040012240d080c0b03810800900d805894002d4044615503032014100c0307000780c21242c00203038041140b10411011458040c0c001001d801131040b4645554005594207200410000400454034a034074115205d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 866811618 1250 866810368 866810429
    0x11061803010609050f06010c150c0e040f06170313030605090a060e011b081006030506060c121903090b0c0f09130b01081303020706031d0d0c14010605010801 69
    0x103000740070b566514190303e8041d10341a25044010088000891465070241040003125540400601420320001c1d02c0d2800500b01c19840c04103104003030090f0221940d891242001e0040c1c5071800046403400c0086440808046084c1ca110301d03401045800c1c2003d409110035011294400c60100da59518441102c0c10154131450041520303041299045030000190000161104a45000b1b0000b0403160360403a6400e900f80d41c080f1024004000038803200d803180e0005948080c000d00f9091411070180d00313043c6030803840c404505800b800070074050403414104101c060781081600e0140581c407030755103810100b01030162034a9a9036a0000d0314141440e03120060b9045914018200c42113110102c1450b4060a0040c00b071600023182c0000003562007009810f00961260942d005000003070038200141e0090020108049070f6212206d58807034541d0707042085241c101025a9942e04101e03082c504162049400e0f4501280b036418043d0034082d60340c1c00a90741e4110360340b42001048841a404e40d00b480500b8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 866812868 1250 866811618 866811667
    0xa09060207020d0624032a03050d021501120206090f0a091d480405040302100b030106060f050702061201060801080d031a0f0102121c0e010204031106 66
    0xd43c0f01450144019a4003889160005c51080c0003801d80c42c0294840c0a0141d000c0140341003141020010610004407040d4000c05201c1d450304e1810392030351182864130340d03044074460050740142c41d020340101c030380c40c502801003070021003d00928070f10b6400606207008440030a0b0082c16450300c2406640d03205200c0030020540800100b00760071b9010a11451a48140041c1c0c80520511041c04184480c0d402120000c4050f2186080b80103403000400b154049040f14248600f8002c03040174003181c1d124410f16000b10706ca6002444400c40240118064921100002c0d100c0e900d03081003044803e130405900ca5481c3c026141c40755403005c00c2c0c8009040750017610340040000c5442c0c4000b01d5050340001c18103060314041c404403582c0008426040381070740c5000e0789030341000d1415a01583c0f24103004514081285050040c1e41c2125440c11407180960403021010003c11542149042032100f14070624a00d40442d00007589000d0464481d5029040c80c00652401000c00280d07880c0300d0404e5408c5040c41c00c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 866814118 1250 866812868 866812879
    0x90126090307030e190b0f0405040c090306050f0c030a1d030403060c0831050f0609010b01090501141206010c051027020a05010503090a06050c1207020607080a0906020702 75
    0x4115205958a07080301000f24045007442c08050300b00d00c0c02d0780c80d0f030040100a9903042c84003800c00c0000b800d06d810002a844110300c0501c8007080700ea03258021808912490b542d400001032550404800b40d60002e4030b0081c210003c5420b01c4003403010802125400041010b01203104400208408031705842035442e442580404038001c0108001600521703421030719582e030f481c1c20f03854805001041241c0031307031184003aa01400524074240b0502004c0300c4918025400d403245d9074200c1034080e00f88141190602241e07552549400e50560300b02200c000900302c2880c0803c07110b80140d174001c0076440f03010315410301c5540440000340c0b50fa01c40c240705401c4503070200540b210820020301c081d000d0f06000700088405038802c0e01b08070054141e810301150b0250018020100ba501d0440152943d81c0301410481c001e008102d90280400c80354001d041c0146400640c0503a1510380700c6030554400009410131046412002c00d100c2c6195011244d5030700302410302e40c002014840c03490541d00038032503404000c0d0040c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 866815368 1250 866814118 866814121
    0x3100f090905070506030c072405152704022407110f0409020105090409060230060102010204150e0102070f06050d0f02030105030a1b031406070207050a0605090126 72
    0x600c09900710001480c40345003102d122641352030421549000854451450006c00c1c0004000318a041291802020700800a120b201d0080b40056098501c110b4031074074811403880440c42d50341010450035085c1808003101c03541540700810000f11030b805c0904040c0c882c0905009000340d0704200459010180321410465544402c5031038242c01140d2a808614131030100c0d490782c8a00786c20540248007506034169901c0386010070400810004007950340083d140142d003071000303049010204444940609465000c54818010902c51905040d4004c000038116401840300700035101080c00705258803929810b0500c102095000100d190421a40c403213814070300741d000e0004045410800500010081e60000e229490049041030142d100a1007500c0c3c26a00404070700c0d01081c4c255940041b0751851600141815689480d4103100405490640074141c01c000c09106041340c0400800c1c000709825990050058501030019180d8001c0c1c0c04038a0601010080116042401e000d90040380440208000300a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 866816618 1250 866815368 866815379
    0x60b030d020a0c05010c0b0c03070e1315140d02010c03020a0b0f041101020d2307021513080601080c04050a0f06031514010f0902090109210b0106050a020a0803100f 72
    0x25140948415120718807003ea020030194420801a041c0c40d0300b03c2070a840c141c554522407030443e40001e00c2181003015031240d040b065a100c4882c91800c080b45403011a0416542421791000301d00c0754800800071041d24443c1c56036840300d007491a006a024244503002441a042c10782c14030809440042609503d20304004450000600d41800ac900501e22a52180b0b244801665240204060308011591448000801544420310036140d40d032885042c03401d280e0030381d01040090342c0c1000c4810b1058030224000d8883c070101e2810000a2104078018015035141c4141c2a8036040002c0300603000d6900c0b180011700565298105011900440c0010066031f540c0c1d0900300c035015143c50301c0001450904004a005090440d5281e050b205040100680d82c0d24160a43c4004d500101c00b01d0b0501c130002d080014118056192551400d001030300c1802c2800f100d10f4034150b4050305030447c0d01440020b0056101d4a907002602119950348410003d503242c0300d03442609090503180d40200138440494402256 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 866817868 1250 866816618 866816623
    0x2010c0f0b042607260403060e01050603160b0306090c2b2412050f03030a020a090b160f05010e071e0f030519031202030403050a0e03070f050d060b030d02 68
    0x444411008410482d001c04141d503c054410707260094480c0c0c420310709034220640000c042d4200400500320a41c03806640b40e6a400559030060488041c595441003008001e050030700c01c0800080d6805002c100e000c0c01c0203481c0c1040c0c0800740405008841c1c45001a00200d03181044400c940504c036001302e0b10411910b550b2260050720780031210818100151541d0240d00c580c1040622001c140c20806080d0521501965070384400b030050340c10780705100b0f6a1204000070300045024141c1c1c00005030380c81000d800301a04081d22580302c658180d208001e00901c0c1d1070b550754903203841030b8820340d20aa070408034109940981890030402c1040e001300c0700d0004a410b01c2181a01b1542040403002203616640c08503200c10a1052001030070641011541e4010300304901d0b091842c2d5407017030034010100030542c000f082c101d8108460440100d400002c0b111400e40d040810703901d000404500500c290ba0a0104c5a02005018400c6038003821070b0b90380f02c034104981c40e008503d180e20b000d0106d4030110307203403040290b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 866819118 1250 866817868 866817893
    0x18050105040c0611070504090602120f1b030c04140a050301060f050f090411010f0516030c020111010c090b0c0708010f1d0114040807031806052a0a02010c0f0b04 71
    0x110741d01c000b01c4001070043e010b980d100408000a40240810600e040140000b42400f92003c5801d40d9007041261203a13a58040c5486c096010300500a0306450050111400c200311880f010081309024010411004a00001c0360181e81681c0e48400c0790000d10004503040c1c07103568008036459400c02501040521441d25104100c83c0101c5880e80b821011106004041ca000d03203001c3c248503c20310041003d075020b2040045c00c81c0d11480c0c0b82c2d10700307024400d00303640c51415400120b00040a51f01b600341075603402000c601c00404264005c1001801000c4042c050041e2440b400000340d00100f00d482203001c0502a00e0014425203000348160800784400d00d00030b106044034101d4461100c20307140b0028105100341d07400c480203004481c10581310381c1c070343e500640c001ca401142003020005000b42540400e62040f0000c001c6612000e4a50241c0382c501c00070701c1c40304204043c00c0d4020508200000700001103001c0c0c465020b0901000d0480e490070118802607000d200945140c120100740000c0055444285 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 866820368 1250 866819118 866819123
    0x2f0306040f1a010315170a02010e041428020c0304030221032b02120405100b130c1b030f1d2d1003020d0b0105030115030507031805010504 61
    0x4208607414403207944100c1e00c6a401840a044034903105100c02d50082d8004400412440c503e0308900307680b08049040680d54003003c0001d82c11141d03c15045580081070101e100e00100c40511502c0600c045911200c40010400140321b60b40800144107e152242e000103440007801d0150760f600c90700d445460703590340a444124003d80d061f05004118141e8091000700100c00750005d5450403112911680c3e0810f4022503a120f400d260100c405c60012492000b09444a05410101401d103001d04116040000076540b03404041d0800644000d69610654000d52089484100007844014004111640c02c0074945190801c02c28441c44018180c0040d2801113644069540e44000c000045500c1d007c1c440802d0340d1604406000c4401d40700c4440882c0c00c400d8811080c03005034140d0103100c0000e0101b41440d41100100340d001503500300348103050180321112082802c216186516009417201181c0ea4020400e00701640c420205030942c0c030a8000c440c611414160244491450b810018000e183c2a01c08 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 866821618 1250 866820368 866820371
    0x405071b0f0b180304060309150c0c02010e030316080f0d0c020717010606120f090506130615050d0b0a090f210f140c07030f051c030902060d2f030604 66
    0x102060501c040f00c00c019040e002c043c50510303140210a60180c42042c2c0c2c2190075441c089216240c04282e0b01c02c80e5500c2d14039548001014030940000341c000640800b0850082d001003094408040b1400130203002e0f6503001c03400c207685500c2010191840d0184840c0003030123505004200e030480d50700084040a0341c1d02d40074500085902802941e00301c841e1480b450002c98815507210b020380000380d2008911300d80404010540d00419a5a40e00385403088580c1c00c2d04841c0702d600742d400d2001c40c3c03041c402048804003402c0d01203420800002c100012700700c0d000300780721610130006d0791004440d000804401c0d4004420300a4410174900640d204200141d14803001140c50751103900144155182c0d214440291a40903041d00e541002e182c042e4082d5542c1c1a50707109005c00080024035822403898000d00900c0503044140700c500d154002c6699180d1403c04250815401c040565a910100c4820b110043d100084810030405c1001c480c100303e0110b108030107259104074000c0c1506400861140904450 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 866822868 1250 866821618 866821621
    0x40c080f0303010e04080a023a020a05282907020d320d0e070f0f14210c0109080a17030c07080711030607080c0304020405071b0f0b 58
    0x80e06039039000902c1540852418030001c6000f08200e00014980d60400d84141d8035070740403070b418400351804500011410102c1300d000507180c02c025406210003a0040b440a00003814042c1c407110745e24160041c2402c0c4e20031021a002000200384079110194583c40424400301d400c0c1b08061007010840e000355030804140c402e0019800a10105402444807101e44400042d00c1000c050156240c001c0d043e00c030700c826500003074051580c10344406030640000f00c1101180300400044802d00781545e0383d200201140d20580140b00d02240654282e00b50781d00e410324411484d40c801c002034040d101040752490b28011915090f00300d0400403c503070100ba802030b294000c2195031a00815500da1129030041c02c5400705140c02104280b400c0000c581004001020f203080c5051b0303880f00491644050411100c622229400201ca0b003410b00801c0e501601a04002545280c10207101e0624480144024030860f078560001e2502400740c40402001c041c442426851500075180c001404800c0440a450300d211400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 866824118 1250 866822868 866822893
    0x8060103050a0e031e16150f020a0f12140f04050c01020607050a0509041d0313060207050109050d061409010207150213030308040521031f0308030705090109080303040c08 75
    0x40003034410403400290b02c1c200422051210092540d0401d121200c82002001b010054030440f416005000341c1049081440e407080542c1102c40450010802034014040c008000d0741119100d051f409803800c200740940110317200400100300383c1e525080300140e143d080c803144d40d40c008582c4d03200b0752050040324541d03011071006a9031075a0444101001440030081f01100c9881140900b6590801a1001c10f03400b94070300101c00659004410302c0010b0b4004110220f030002d8145200300104050f001030b089150900000a207411454002d860060103c01400c1c2d0400c1800c2c0c1c8119081441c40202c41d1642c10040101c40c042d620000095410151000306494484441d00c200c6075101d15070028408450300d10358081d60700501c001c1046e00c01303003d4403d070301442c03d51042518800f420a094015034070303d010750204040c0c221010b042c48181042d41428400100b0741300480b600640c043c24025100c0340c3c401c0040343e102d01c1c541c022001d1800040180010001100c94000c01e5039804005da4214180e0390 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 866825368 1250 866824118 866824121
    0x804031205190c121803020307030f15050606040e041b0303030614030102090a030b0c071b060f0c1a090a050a0614130519080c0d090503070801090308061309020a0608060103050a 78
    0xf20800b6100f001ca460f04031914500500300c4c842e01012a0751211301141e40c076000241020031942c001e0b541001c3e080f01c441d041200019a02c404000c030004200034a0801c034000c503405005501598660000031004101484941c0b4400400159085419240940c580c9030040c05404903200340b10b03215080360302032102460f0600030f40d1609140901808050b910f16181e001c01c2d00000380650034a00010441500410742d01c00301c020b08075681504d134101c1c0c1480e141c40102100d41c000010340400601c404d80c0000103680041c541618080005001d20755107c0004003420b10000880080c9640300380300c4408100802c0f038014400500940310001070581e210a2051031043e40034800603c0b0303030000840c00d420503070110440c5003c20300a06140d82000e0702e0b080254030703188800354540085010b1080400c00d03803034104420800b82103150024400d00c070035690047d0160780e014140b81e104091310303100303000e0b5068664000115203400a00b810344c1c0d55078071140500006030555030342c0c0c0001c2c01c00300058440700c6103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 866826618 1250 866825368 866825387
    0x1509041e0c1d060708130b04080601060503012d050307081006120507090f0605130228170402120604030906030e150c09010309150f051e0105010804080403120519 71
    0x10b0b03128a42c6400600303020802154000e035021a0395003014030142411082d5540c8200140181b4140642da8500b44201c0d90300e452030582c0b001e8200502080107115007140c1000e500d02c04030322004a00c01021002c28900e8038642c450b080550948548280020640d00008408000c1c100040007080741c151254051145d00300c2400001d0b00c42d41c00b0301d0003006128440c0d4803456881c0142c281c001110760300e407800582c210305004403010140fa00415810030309045007680081864580f510b4840741401d541e00604580400c61030715a1444030300c00050203541340c2c0032002d0112120702040d0340441c90300d480c010b44904014095440020f14052802c03410100000d244208012400d8225419540d404400c20480d0300001a040c10181c44a9540c80012a48001e8801100104601107002552441e0650449034001c2c2000b5010382d0309000c004010b100d0840f05410f55800b86400315185e41c42d41480d82c003030301c00c0c0d5000500181100d40f5940b0f4095021000c0d001c05024400c4c040041c404c2c03024100c07910f009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 866827868 1250 866826618 866826647
    0xc020c041b141b0a0f02030d030623010908030706090c0e0c0f0a03021e090312030c0a0806210115050405070206150102010f140717010605091509041e0c 67
    0x881880c2e410000751a0003074044241600c203101c40e007005100d40d040c2850740044007210b034061004134101c01c40c603040c4a200c0d10100b8078501040030901e04008684810302c1704602e50302c00901082c0207091640704d44c1c0c041e000b0305841c030200c0742c0e80d41540c500329005008814041d1030301c40b0101400f1a0300400d089040d40501c2440030700390708200011500742c070b842d030101d81a04285a030800200c0e8010505d903c610484400f40c609041d1500d18a80030b0508103184c542d81c95800368410800c018041c1414400c0d1007001c00d403450028001e50312640031910071190380e02401c0c0c164801e102021030810781504881c1c00c4245c845c5105001555440c24002038450640700d0401580205000800440d0401c210039560b503014800440d0300c55554124408507220702000456401114081000454000a1441c01b00103400142e485543c94094010b0250140c08078003445080c0a15500400c45a00011b64026080c0104100540100810103125640076843c5011580c0d0511001c10100350040310320450544 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 866829118 1250 866827868 866827877
    0x40b091207020f040e0f0a060e0d020715020309122a06070605041b060302030f01170303070e0d080d1e0606140319060803040801180309061d03010c020c041b 69
    0x4a280e0800501c8040f25907140e030095a10031016460107810071942140760074101c00f070700c42c61845050642c241c440103074012a2940c0314200301c3c141c1a900145440c1218420641c26030510031340c4100f20b04500c2100030305588903e2240700309a0042c40421300020118106090310355550300d040c0075080e480d220801c103960044041c480070011132010b41050750720510a2100b10307495031000d0804010075050f5048030340001e50210030409424500a9203502400c0100c001d030110101100d202c503500d110041029042121240500c1540e407144a02101e0702a44800803c0e00c030311200f0301d00380090a8004001030300c1c0c0150200110706a040d48142d0081d11400c1e95030b401070301c8012810020781e40c8003400ba50500c0741c40317041c2c0002d01e4442d4032480000c3d0612602942d5140d01e00704440382034982441c40d039041400c41000013400a86c1103445082114258242040c01003445000302d072640051110094165081c02c0c00002c1042c0e0115600c2110355040b0b07001c0200ca640e10180281e640182a0000d000c01c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 866830368 1250 866829118 866829127
    0x63a0614090a05040515090a0314032e0f0303120f0b031b010513030303090b090f0c090402010509040f05010512070b09090c0417030a26010306020d0906090b040b0912 73
    0x2400b19400c10760b07116001e0821240c0140e01e501c04074202200445045000c0d400c40d418078010940c0c0701c6814000040c00d440a54110306000600d1081e050071403100410010070325000040c200070880d00c0000420901c58165003ca90302c3c03c025025040840f2115109171070400d0b00c0085084501c600281c0f400d015000f0001c0745032090031502e8908500016038144101840420034001d200c0900b8809103210350380201e508541e515080890f5030018090510315002070002c800f00d000c000820303400340a02150380f603085031240e00040c2c0301413180d102559009410702c040d082405c0d00e0764002c0b5048520035201001d0b032007024582151112658040c9404000307080004560a1511117403854110300c034480c0c49480c0c19510303888650320f0101c100c111200381d0030201e02c00710842d030021700204040114500c20f41c2e54009081000c19540c105000007001182d02145407182c00d005544090103a69001204100600311801c00d92100300007107900700d81c070b0510303140080e0812402003101031810881c002042c0c00c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 866831618 1250 866830368 866830381
    0x1803030203090307020a031a180a20031b0a1403060604020a0306050904050d030c050a0e12010219090915081924020d0b04050702070302063a061409 65
    0x3940c406844480b03280b0090215102503070300d02003550020351080300d0362480030755071800d2441e4103c0c0c0100744000c0058040f00c5211424000720f82485210ba02035546813400c410348138071101d24203444034072582512500520342c51f40c8031001c2d1060b0514070121024151603035281da808403150030340d01d00f0076015003200011518900300394000c1d00c0542030606010130303510345510126142220440e8280c5650748001c80343d010241c4c141c4990380d20f05c2d042d450100e2500c854001c020300301481a4089038040c0840c498107010010080d07050703c00a0398804c05950000581c110020200b220070b014000800c4e2510030703000403107840b0032001011101d444000d0b001c003211495400c420252810000c1da000ca032a021459100710341071070303040714000c40001b0058445155000d40380469041030300d1240035925080500429640004280040300e904982150340c07000060500b4400032810a0028a07010071181c2c0c440310480d80c08551049524249405c221a41c0d40320002c00411502540d90b40e081518000410388 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 866832868 1250 866831618 866831621
    0x50c090d0311010f021c0f0203060a03152406110615010503090307120c2003060a020d0f05010303110d0201060605040302010e0d170903070f1409090a0b0106030915180303 75
    0x4007540c0000902e1003413148810b0b060760301c0581200c035001c8100126241c251510322500808551002c400c604501c4c1620104101c0091400080d014150865801e59481a507800c01d00c06806207100341d0207018000358072100421403030300078000400c66900c401c416100c0001401849240c0c5041c0549240030004010354240c2d001510360549800200451400300395200103c00c081ca8040c3c5d00c3d442140c415052210741400030a480c10024804448080c1245c0d900088864104843c80030041e924059086040b008001820031604854100030000041c1900311032941c003003243d280240c54400301c0f07402c0100d003207400c01d000303003000300c7c6092009102551084840071854100a01207040f5a50661291020305551a40d080c619400000c1c1440c60b50031b0a02c90f0000411250400c802d586042c01941031a1900c0c04090a00a480da900010441401040707186e00301500700d490100c1c0703540c4a07840100a007040c2c600c1660032000c080102c001e007000d1845034998550b003500502c0d200520329a000c80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 866834118 1250 866832868 866832887
    0x17030304020d14240901020903061b07061a1207080a080304020a080f0106140301140112051e010506032109012003130515040b0d230712050c090d03 65
    0x100c001c00d0300f08003030410f0801004082c800802840b41c4552020f101c1e40e000c2e07461a001402100580d006200c41d40c1a07480c00a00c2580240304050043c40507044605901001c4c091000302034115030414100799013400038420041035a440955043d4402d94940d1111a43c0351b1039481a4162039001e40b400c0d50124411034003540d0050b00c001d01254820380e40c2c4000518100a003070706001165035903001001406040e44614070000b42c281c000340810f406803d014400c8010520507000201070740c103014030400400f030145204d2519040034008600310000d0340300d40200812100540607106400c0e141c00280000c1e442450b92654810f4400d00c0c00d90305100444002c40300b4000415281109082c0020543c800c1c8050607400014981d00c100c4685413004024043e00068002130707254170100403e1081a40550880c3c110101c84d400c08a50703145d03c0260321044c010425164442041c5190a104195500503000d022100d01d29809000c2c54a03070180000352403160320f0020381c0c00000070301d584002074042d06601 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 866835368 1250 866834118 866834123
    0x1d0906090103081c020c010b0a091505040203041403030c0a090b0910050d270302010609050c03130f080418140114010f020a020303130305070906030519020d0215031017030304020d 79
    0x290051340301041142031360044540c026142c1d4403144d00007401e042c4040241700920440a062004100e441210b0f82991100c1c0038079030190341c0000000341402100c1c10b075074580240341c004403645c9240c14130000001d60414507000300000e100200000b50700030304c0c5064861941009080c1c420b804040c010541d0298040d00741c841e40d664071a2940001c0c0340c260700035140059541c40060150b018107103030003800c465280c2c00c2150068500703400e02c003071000620b080e2980400c5003001003851801600309922845a90103008010440000300401c103160380107041826031400110a1240343d403074104049070407009002d40300c1c100300080480501580b003105808200040d40c01600c079091207640202e030440d842071740403070684074242c0400c00401400300002c1d00144041c1da410402c0c20300310b5403499141d460000031380d007024402c0314400d070555541406162190b60300a10b0345899452418982c178040d01304580481d162103c240001805640030030b064501022800051403540c3d80329802c001d40b80c82498070a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 866836618 1250 866835368 866835397
    0x10f18180b100207080c060c0c0f060c16061b03230f122217031005030115030605100513051308030f3c0601120c1d090609010308 57
    0x20600c842e216410341d035103030394041e40c00780200a081201482ca02081055500d010f65020000d40140e4000811041c1ca240f200700e0b5441d002c3d1700440b00088590103805e40888181c000c1c00d242c1503940e55010348071421103010740c884009000b03000200c00040c00c090200500032a03100c15900d03412581c00400401c55610616449042003602c0b0404c204036017003541e0310041c0d130400307500380010308100055070007903c01510350451840f01e180c0c0c6c9858056428840c003e508640c0403011525000e05005600301601001c0c008001d002c8603040e482c0c10b405014417050720b000380350001044280108140420903a0300180081140c2004200c3e100002d200007004100d800709010003032000101514002c500403000004014030303d080101c0340c4003040140d966100c03c4c2c1a241c01030b00d040c8590b110300305845071004441d100709540d03410006840074090108001c6001e46841041c3d0641508103041104031550b403043e020724403030b40348144001002d06a4a060b40603001c00c0040001518400044c20103603510f500d0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 866837868 1250 866836618 866836631
    0x302031c061d0f010b1e07050102042c1b04060e040f050f0f06030c0904030302070606050a08030703080a0209061605120301090b090604050705190c020607060b010f1818 74
    0x520b10301442c10030311500060b2042c81400b902d40da07040c02d45070250070003103012480c101c02590501c1c5040c0d086000d590220301d0100d01003085c81400c0d03042d0b50082c540a510fa0054130780250003071170203501c0924035540d0740c8004c03004100c1074075005000ca880e460035220300b03901d0142001e4094442c001e90140a86d130080d01c0c0d2041e40c0001940d0f0148901070321180e08100304500303081414401000c07000304120f000707a010300d0042043e5a511060a43c0054142c1001039481c2d4040c00d040c400340856802c001e80011820000141c07e900c000700030202207000f990b61740080d8481601080580c450350100550160041c015421070070280c400c04075541b80306408445071061407403103010040c2c109a100651441e070f200036045050800680d0303154403513030840b004c008610780744501a01034060b0b8400ca041c030714401542c640c140c9004101d8888000d070010b08442c0c8070b000d2031074030602030b01898007a00e0010714007405840e0030b1800b80c2800411803008031b40614206040c5004c802c2003002c100d072200c81d030a80340c11 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 866839118 1250 866837868 866837879
    0x1140117070b1303020a060309030206010501080a0f292722050c0901060513230d11040b010207121b031401060303090b04261204120510090302031c06 66
    0x52074803840d00b070483e440e100d02d58010015070200369070000c02494203002081e00001e50104600c0e0650310242041240c9407614070003400100351840200d04443e180100004100028040c60b4101c4040d404554443c041ca140501c500c0030b600700d04100009811000041341a02e451081607400a070901c2107010b004480304a0342800030b0281016900d07900458441c5c00c1c1030901c0b059240c05451181426487c014201000c0d800a0044c0d00c00c204031400c001451008900201c001d0200c0206d000340481c00f105e0b0142407610307517481019011f81c81a450b00c0c1f560f10a03540003107405001c80721003501a506d414640d4a0780c142c0303a00d07140d01445071210119001320004625203044401c04200d070000145035810b519010b89a0074842d044000030040c00e200801c4610a420244000b0080e1a00e1200c501c40740c1c2c5103403501d0844400310010040700049400700b40c1c482041c0d121240240100304980002040458200840f642c0000190041e0000c0004003020251f51034036034803101c941c100000e5501d6541 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 866840368 1250 866839118 866839139
    0xe03030f060622180b211204090209040605010825020a120201020310050418030e0613030b04030215070f0c050705031006080c06040e0103020d06020405150415020114011707 76
    0x8003c0e20951034580c0341c24030030680c10109000e00603500710001c118800020700003940e4820f10034824000e640d80d00c4a22101d1840030301a182030102d00308485500c91741c8603201c000c080e400c80c0007072078001d0b443c05000207102d47c85102d00c81c1c000c0601c54802c00300850101118664003140d0403642c800c2d8030032000d6140000f00c101d1135070010989103034001a20390030481e204070841c05e0345510691199007041e01030200c1d62882c0c000c420f082689424144101c1392840e01103003443c01150361441d86446d10b00c07400001d00880c41c4940303225a00c681e082c2c031400301c00101e0513602060f058130500001482c4c0c00305031402500845140d00c205020300f049a001039600c0c00001d10f024291104150020b84030071042105c0e6604010041d400001100e41d40c2c242400c0c00c44101c4a0541480081e211300004070251b0103008090b41210003500c1d000c2c1c9406014840414480c0032548035114425400e40c01c0381314410b00074818032840d091581041106903da0b40303002c0e004c4010700016000744106028250b800650201030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 866841618 1250 866840368 866840407
    0xf0c050c06180306160f030926120c1e09060c100213061b0318120c030309121101030c02010b04090c050a08060c0d2c0703060501090e03030f0606 64
    0xc41c4104040884003d16080c5100a0681c030070340f845100d542c01103503402ca511010900f8840c030b80068031031824242003a41e9040c1503811001108294010102d424550004003002016010600010b0703c3d6002d2440d51444ac0308401c2c0c1d04100c001701c40808481494001b400c0c0000f005000b2410052000d051030f092030380741060850010f60005406400d1130314111920001c0031076061003214401031980d017804082d48108004c00b041044468600c007a0f12080500c0040d00180001450305082c80c680180c00c50200d020681c041444038200154030004104d41001d0141e003d003101a07040021001540540325544821056540750304400501d40c580f4442c031510306018229508035270340b034002400b10100c2160440040358010744204100948070034100e80c00000644800120640540c44a0300c1c00884070f050740102c040e1418500030750750b41c0010804242d81c040c0c2010481d699030798042c00c00703c40c4e0110940006c0d8005100245ca001c0b0710108241d40030b44040d154034070f00340c8034020b4401083d00c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 866842868 1250 866841618 866841637
    0x90f08120402040b040e0309100318050303070e040506180601030b1914011106010e1e01090f051006020d0e040f09030c05060a3303051c110604030f0c050c06 69
    0x3403180401c0150f2034030340221a541003040d5000c2240d0002855007540341d200d80c480c0e450094801d4038440d4109882a0b01100503e1000c520300701000c0070030b1800d192243d20540304034001070614040014103140c00c2c8102c5000b4103004040a0707102c01c0e165481c54500100504180c10b00daa203a4552207070b5200d507103000e800001c0e13071140e049526051001b80084900c00000d014108030700742d06a074403041800600141910540c40c1c04440c960f0781c0510b1030000009110118620010700000003070030f449280c0180149022846080c41503980d503000c0e10503503881b0b6204000069111100d00440580200c140b02541c002c0a000030410541101840040d035100c450201c0010b01e583e0044402d000043c07000b81e410180c060804c0c0000d400059151540c2c04011000b070687d140c1d41c005001d04205030f07080400c015940700781900c808200c214180800305100550741c8010881040c92008604000b0900d24030856164542d808840780c1c484041350b08000546040b02c40d031049252030200c581d6440042e00d21040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 866844118 1250 866842868 866842897
    0x90414070e070e040f020a0804021309080a08010314121b030d06060f08070801120201080603030d0608061e040b0a0e0a0503070503090427032f030406170106080703090f08 75
    0x3d241d07418441110145480b170700d4000e1040c0f0281460b15849020240c005804440d0303500d11411803124000103103014030000b084a42e00042d1091444d0b0003000850490740110f1400c1000009100003540301c50918546124100b01004a4090703407401c0d1828031011200d8004480c281802e1444403011100f20343c0018001c16000b00348403e48652145500e03038024a145081d18540d45042e5214240c2c241c1518020b05108200c07000907110748040094030944100c0b48010710000f655804516140c1d201030f20112299864407000b6880c6014140609000d168072140080d003a80e45c00303042c03000511541040c1e010a000b000c082d000443d0040000d81410340c05440590341e0f885201d0200310868503c00c6050800f81c06030031002480311405294030f02d1050b018104020110144211101101c4404002c0109091000c6d01d0f0040708000001820544010b80c4072542c03005c415107040502c0d20801d100d50700c001a004c40000f80402c1c841e4114005491141480c8492081d240c0d035500d03d10741140485441c400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 866845368 1250 866844118 866844137
    0x80a080c0d020a0312020d14040b0f0a0c05030402151608090a14030c010f030b03010e010603060f05010f030f0825030f03020412030305090307081c05010e06090414070e07 75
    0x30280110110541680028042c0c5011654041c01406044892a8a590f4041144080c0c17074140d411844000d030a240c8400302070b2a0a10344044140400e075203140641d0022400114a483e4034403031200c6000e5070703484060842d608c82e802c0024030f01007182003911003541403143c40b6442c1d80721401800d00340d20a5141c60b482ea040c2109002d61402c880e8402d1a407400351028503085524041412442c210082c40c0880c5031140c5c40700240d01400c204141e49070550b180003020900004103500013415644110028460b500c000c1030807009540082c000e6544a1034905001c10014600b031207500030f4980b155003d9030501c0c02c0320800c00f04002c142034042d101c580c1c6a1b507840c01007540c02640240003202604045080c1410601415503400f0442d1004090558880200300000420815600d00b644d101c80b61740c0c0c0c0c4020f07154440e6003050300619969003080c01c0c2800412040c10301081c162141c403010703100e1920f9580d140c8139468960348a8491207618003a102021078010300400d40103119440da5110180700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 866846618 1250 866845368 866845387
    0x2073521040915150302090f130906051503070b0a1b0c030b06090903090f180108150a0c140d0905150601020f030309060117161410020309010e060a0306080a08 70
    0xd4441108000244483e0808140b100e52000710114a1028052400680f01d007001c0c801b180c49030224210823035000000a000c0713204190a900140b2086120b000c084c805a240d01c0f8000500200f90101d003541074000310b03011b0100015a0307010302071003d402d1802c8c00d66031a441c4406401c1100e100402d0310445000311050060204603101c6940003c2c040e10141e1052078028921500c900586000a1247c3c00030034640c00e041e602e80d5000038a550f031824001e20309594824000c1d942c3c018100c0702c2580d94611800194110100e407207a00c07414645611840040041105c440089600a200341d4204513070f28000100030840030400e2820703949a02c40605410304118001901c0c0544c3e200701850103920400c10041740c0c0b074001c2500c0c1e044540f02c110b1500c0c401e90011803a8104a61080c240d418405103010000307146502801e83c075941c10007540d061500c250320b00b00c00c03070b100d1041c030395541d000c9940c4111581540c100b46000340345003001e6240000d80700da203030030a01d0b04000b9840015a503480c000b01c1e01005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 866847868 1250 866846618 866846621
    0x204050f1f0e03031201170f1603030c02010c05060f1f03021c080c0d0e010f0905090712110d1e05070f21110a020735210409 55
    0x110342404964840c03200000c0711100e80040180361a010400005640038001e5860800c25180c084d2000000244036684604944444e0644845102003a04c2400c029203007800c00440c2d640a0b1750b200030790250b0481e04503241070b83d100358403c2003281042856541c0c5400300d9414042103008401032103592a560405100d110b00d52050300807095204e106600003000140d803414401081060800c0080080000170700342f54016000d200d151028600540c5040320603503501c100e002c20704900980700c0d19800e00c00c0c030310b044405d11228001c05800c0102840410080ca00401011011a1000902141c440c40c040c4440340a50061501030092035243c0c0c032802601444015003000e8014080e101708124600440014201008445014184411410268200c141c003c908032160010000b0512056005200d681000e03408420304900501520501243c8000c030912042c1e08014100f13548800030b0f21250f9504150030442c0030b411034070701c180c004507142c600013810451290100c41280d0364840d803400d0003c80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 866849118 1250 866847868 866847889
    0x3050a082d0708060103060b1602040f0513050f06040b0106030905010e010c0c0b0606071703070309020312071211030405060d060306050a02070b0f041a28060f0605040305030a0503040305130306020405 88
    0x34107060402109108020380705003651081c9c1c45805445000c07042600200f00140340c2c81c1d542050842c10181001459200f040942902c00d205004440005143c800150740341c09055400425a83c0440010446c081c4240c0044024074012000001da4a8512308101d0846000e079540d07101250300d199070700080c409a00c03145d640c458000e032003072860005207540e07111f641c0d81c4041c1c0ca0400c0d004007001181c0000c0c407a510205000d03030b01404550300d8908003140010542c02220381110081d0700031800708140c5103e1020040c40034030500065080030b00344001c0100680054000c089010b6513210000f0109020303018850181d4880d03003005a03114103070b04244000900c010140d40038031403144207020004a0380a07450700392641c0100362550640722030340d52039040310803a0021400340020f41d08101c0724400c10743c400822100f20800a04d02c055548805488a00803031002030104c0e0014024241d40602410045902500c80e1800304d14000d140f9000d803451b405190800d0360a9a40810140100c2c01c0040e20310 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 866850368 1250 866849118 866849131
    0x80d140603190c0b0f130f0317070c0315020f19140f0715180b0f070201060503030906030a061809060b040b130b0f030a11150703050a082d0708 63
    0x1e002d0030302a0344078289010071070300c01c81d0402e00c4000b0b0a001d0380800d120548039200e011100704540c05070b4030102520100d01500082e100591001c02c44a8489a503608071000b99034401403008096140d604c1c0c2000d51140f80d40850306940e020004072000010450090801d95140020001c4401c04c0182c01000e02c0154035003011301442c1000000701504401d030981c0e4049e43c4c055401240707512014100400b5000c00301d0101ca01020841c9003104025491064511943c0d400d4004c0640c0d58070104102e090344c40501c03419070141c004011503680c50130309800079039010a8188001c201c0d0366550451313060101c0c3d065145244541e460345410200b02480c001d90060507002c940c1440824805000140c0d0341412070a02070104d50b89142e05001c0f03845070321094040c01c03001410340307100c2034250034004240c65404010501c0b8490341a40c80104038060025030783e102d5010750b9142e0804c1e0300e41a0070b40c3c41070f0000e0800760454499080300e400b40000d0048169406001c00030003812400d007200c3c040c00505016000c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 866851618 1250 866850368 866850403
    0x703080115030920011403040305072a030b04020d0b010608010801060618170c0415030c0905011203050c1203010308221a09011209050c0a14010903060504080d140603 73
    0x13060101d5800e81303081c031084c3c003410300c41e0302d4400058452410010f00c0e08035254020080000745500400038059450107000c00e41c2c10030344000544450000e1615120200306a01c0c00d0920214102e209000d9100e48064414010740c0d080d9140c001040d0005da120700d0000d55298018055402d081c01107074020100c90622a45800c08100c0c1600030100b9405518006452000446d921a004224050301100040c00400072022030102151552665010079180d864403c0350024050685114540c121030320780201b90700a00050383c08031010f6000300c0107105988a1078000812104980c80114000c600c1450065a5401007014025140146000c028080010b0402c2000710804400c0c2005103121281100c176950700d07007080140d540620500345c404c81c0915164a100400074002040f48201c81d00b1510404c00075a00d00e103000c80c0781c0c420358906001a07611001000022001e03000345402510554850b806d00081e039401c9001c60b9103000e203040c4888070210901c80b41e0704083c0000c0707a5400281c0c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 866852868 1250 866851618 866851631
    0xd08190908190222050a060b040305061b070506090c0f0d021005031807080709050609150409062a030b100c11010327060f02030421050f070308011503 66
    0x46060b02c802a000c07116541c201c0d00b5010b0070855580d100e4411141c001c2c140c6415440840c51403042c01440100c030404062442c102001c203e000d20802558202c91b440001450141d407130580a843e81c80e200c65030041400b506000c08000100c0070b1003500d118245560040980c44498010482d40030340c1a90800d0081100d2400100962104560280550300d030b402d00741e5403900d070800301c8503240310b004524442034040e0900200c2e00000101c3ca0100301e0b2140f060600240d1140010041c03444419290700140d20324012403920365003004c1d00150280c5014034000035a0f03803d20402c92041c00d020507285010040100311129155030903106414600506954501d41040f5100c0302800520491601420182000d04c0d08071540e0310035000701d00c9000340708002c0d640d00030707030301100030700c004001c20044800e02d045c059119100003040c820f0364403558003c915030458500c24420b2080900c0030000c10b41c100401040008070303101d200e6009051047c030a0741d0300c02d4550f250a140c154902020300150040506004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 866854118 1250 866852868 866852879
    0x5010f060f0f020c040c02100617030d110904090809030f07050f190f1205210a05090a1a0c190c03030f09030611180d0b010909060b0d081909 62
    0x50880300a1552030406440c031002c03140c000d07403401d00d0804506a00508140c40c51548683c00325003021103404945043c0880f5880e004d00000f0040041074040180e8018809500704140d1600a40011104949507501c0e2206010120341500e42100e429600801c0002d981d40003401c00300101e02444803220050300b416414407000603101080f4120b407038410a1444c0e5040c1c1c1d05c04110460000429402004492580e0f80f0f400491450240c9001039a0b5030180c110000210940b0110446c3d0855029040d1742c94681c0f03000c416a05600844c54090b040002c084010406515010889030715a401030241e9494a021100046ca003981c1c1d00180441800000d40400c002049544100152a8035050051034403150752012641003070340350700c0071b815982450f2065528910640c028040142101c20354150f40c091002030040c00c22a501c0d0007411034103100010090312002e980a540d5030340c860301003c00d120000c00c00090750134500e4a829100e1400c001801101d01c2446c0032185694240c2d400c1a142031440e14 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 866855368 1250 866854118 866854127
    0x705030303190b060307030b180903030f091c030b0a0b13300f0204060509040b180c06040e1e13080717070b1518220206070b04020405010f06 62
    0x103000d204018202c0c040a400c0d0a04035001900c250740c0180c101512441c0c510030050103011044c41d07150180b12440b10310ba505040710030100d4800d0a48000440ca0343c1c03580c0c1d00e1612107140003400c0e030660b0b00543c6080846000001600d6851068076030740401c0c1c00d20ba1400704460f4100c160300040042108210240c2d030110070f6000344003100c15951502074003c000c0c0080c00d070340304600b8011030701e4102c9400c8504200140754454031030f900d0090310700f006400c0d140c03000d200c5904400c0c0e07405040034840c1e40020340c4207070801c840311101460850a49024000302008208103800681048102c0000e236410483c481c591555000c044001d0100c0c00d24050506a01301d048011090b5000382000000090240c140102e4920400b0340b9006d6495096030f130751003828104c5500c5419a02d1848800c008444000c0d14600205410300c02c1d00f01c03140d4074410b5200d86101f0900078144151442c11212000506c0700545c2d00c80000d00541800307001044445d18180c810001203c005810118400608010511178554030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 866856618 1250 866855368 866855371
    0x2040f1806090302010216152702100e0a0e040b060130061a09030f160e09070e01030302060f060d030f050306010e060301090b1905031c0314010b1b0705030303 70
    0x1011000400480c03c0c01d080380680300d06a0000940e0007010030040410400f600c00983c0400c0c5a40e041203070489000702048602100350b010743c0d04110303182180b00503240010320410318070540e08010154140e5403010640484180d0b1103641140300303900420043c400d001d42d80a50002c424a0264110403005c50355219000704e100314900700d03000c000e441041c014580d90003c4054a13540c074842c1d5058562800d8525a0341c49003914a0003400b03945221019400300058078200d000c43d021051104e030b402c02c009104601c0c0c000380710b03088a204850000400002c0024203c1c041c1d40030354050a103078948010485000e100180c03e4038040c034980c0b04400c0c0400d40c0946540c000342d60600e0643e940392100c20040365110300c4030143e254440c400100026480801354400e43c0100410b445540c1e000390011200f4685140a206660b05034001c3d50300b242401e00e070070080a8007040c0e1420005003902210100302d0300c00400360049144120300048420802003402e5132035140d11008002001d03102d0501000c03c1c2c49000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 866857868 1250 866856618 866856623
    0x18041a030708060601080112170d020c010e070f0b0a0e120c120a050601210606060201051b030114091308030406090c05031b060309011806060509010e0106020703110f031902040f18 79
    0x2450020f081041560500f000100c0c02c08034001d500d4900d410010402948428010b3306158a09901c540b446200071814000300c0c0d04510780c10a13000d1400e08040007680c0322416190800203001030440041da00e2100d2800840400d900802e071518241041c80100300c251180d0412a0303000c0c105a00c006a0000381a134192044110840303c281203600c01d2017401c1c1008500100301d182080300100310b060f41540064481d4510030000399103100c000449081c0f52200b801082c8400c013501852502c0c50605801140d0015076108602d01e00980310b854501c0c26410541702269070b90b49410000080c04607050790a40501411009410303000310701c06603200044d60b0b220100303000740004000220904400c1d88000301d00303824030080303d07a1b1101e54507101d40185468050390380f0503042c0c1d83c0046404943c4106590503215141c005190190031500d410007104a100c1219906c00b54500b1010b100391018092200f140e146d4642400c03684410f40f04210559a80c1c821610409140c181c0100c00000c40c04c0310f4608954 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 866859118 1250 866857868 866857889
    0x903030a0f0905060a0507080105010f0c0b0603151e01050603090309040b062a0d021c0804020409120c060b010e1008100f06080421050a030218041a0307080606010801 73
    0x3584401d0440600300d41c80000c1c001e07010700d40c100641d541068004038459070481d81e807664940c0c0c031100103540d1900004006030002d5030f000c6210002803445072200d60000c10003000c541c594108410700e15a0040c00300c1700c40c003601e404c03a502c1c03062038401402e1103805040304840301c03415881c1c05980640d490143e030480c40e11031a2122030804070340e180d110131694904107000310000c000c0d041c2c000c8071401d40c3c0320040c0c04440e4403888520900d200d00c0419904a0030402401240c9290b10440017104e00703c001802c1603a00507520b003200360001da8545603910700048542c40d80841c8845605092003100c4038404490305009001b028100c1c140d40c1d06581d0700902c1c11f5030416a1031902e82200304403d80c00380b5000720861428014001c110141c009885502c201c0c8903080e00c0d00c904081000d0402c072901488140004180107000031442076000750003a00842c1c0064689509100c08000000e0649880e1040b0780b10040c0049003900a030305003444000301415550005081c1400d100340000d086c60748c14070610750160b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 866860368 1250 866859118 866859131
    0xe06030a0612080c0c030105060906220e03070209010518070f020c0618010201152105150103050a0b0108010606050405101206090c1101021207050a05041a04090614210c06070b060a08060903030a 85
    0x10444103160303030601070cc062041050b0400b0f200225502d50014109a100d411300c40000601440d0a041c00507550301c900ca24118242c50f880c0080c5c5884400381c00340c9066018108451400d500c03400080c04141c40350b2205802d0419614001900319480d00c1c0f514008100504030612080c01e12070890300011a120581804e5450a820f0150401214000c1d0f520702e1848080004181f0000040c100f040d81d0144031031094a0341c0c0d404486003215424820710000c00c509000800142c0350248004d02091440d0800c003600c850103400036400c50b01c00750011007507260f50326040344510358000007003031115000c171000314908012038a9000b064500248100100000005c0000d034043c03081d41aa002449180c0100b0500441c0141915060700070b4020a05c0f02440c042c000240c54194000da81c015200180401c078624500200801c002116900b040f03130b4510442115010340e44500c0001c02c11180141c071900c013542400f9040142c0003003160301c841b003154807560502588500100850750828a4940c7c00a0003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 866861618 1250 866860368 866860399
    0x3340e0103021b0c01030605030313051e0d030201050a05060d1518080a05090306071b140f0f0a1709010f0c02030a060203070c210e06030a0612080c0c030105060906 72
    0x82d01c0b0f024000520000c04207001d0540450003c1d4659126030240c8080c0b0240391a10107040e034074024403140c1d25666820850800881c200760454926400340703ca00c0117030030042440420300541e030026003140182e5541c0d007000350600103403003034641003c0c085424841c010300795121040311801c0902a071310000d682d001c1203900300c200c0c2c0c0d40ba2180c2c950b00900068880d2103400d8040c00355000800e580b4040d014020010b14520f2103000c01c1d013000798900241912001142d100e95240b001c61030221b051910a00000340c0103904200441c484901c102401006000880e1804201d00300e400039520f03030f00900a0021044681c0c021507035400c80001407401c50078807141070002038942400b00c08090070780b80c400402d1044869010403146517a9000701541140c061100e03104100c0080860405e00009681030030031010741c5032230001550800310100e07010500d15100ca003c1082c0181410f4112409000010510502201440303602035002d82240204514542075021500c0e401c0000d01d0740e40f0410103c00350600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 866862868 1250 866861618 866861621
    0x901021e010905191203060f090e0c12010608070801020a08130503070b1311030a2001051e0403020111031201060c08120a0e0c032410080a030503340e0103 68
    0x80803a0004204c2d0f001c0c10b502e19012040d00c80c82e0b0010b40d0b142c0076081090f81541d0003800390340212050700c0303852640546400001801800303510075000840c01914217407503a9a80744030004d20961803410000a0782c2e4505440c684c908040c56000d0803041e401405028030a6400c1000e0030713803080d020000d04085103c0c62500d2070a520540c40c0050062070180103020007610a06051440c00d80308020004000394984101507458011890041103c1420164604001103043c21120f01040605125042000d03d00300c2040c030700150120f00381e141c0d80c041410019981d000201d40d1200182c240a5032500d044641106000d000500940c030a200c001c5c1c1e0854100142c2504490b0b1400c004840060700d0f040c05030401000c0d210312202c1403402c0c442e0380840d45440c9808111001c10f140e6000c2c202c13a481101d01d9404481c0d0328000d000003000307500d0081c0051011814000c040400d07100341e43d0f803075891510300b0540b90040805040004035260f002d00525840c0c0c80d441e40d9421001c000d042440c55054007000480 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 866864118 1250 866862868 866862881
    0x130615290a0e1309060b1c0b0106051b0109060b0415121212020a2708071e0312020d0314040b061905040204230306270a080714010c050901021e01 64
    0x2201c3c03440c01200c041801101d611000e041c10003255515140c00031160f404203001c03003501014002030032000040045da40140003c14150140c10311203c11401020440e600b156114035003030302c00303a84074040207040c1d2900d0b2049409002242c51510102814000d04c3c1308101c074513200082542240740a00004140214110000f1804190703043d541e40200f810b0040080354800e14004c04007645004075644603031003095000655035400e004001d02032402201380602c104034a0107100b013444d08900840442d600ca5903c6200c03030344a400810425a40c4500101101e24070526289040040700501c030001d501b0405d44d54102808031400c043c1c2218081034105401c03001c0d4000e513030084c80003e00140c02298002880d150b009000c0604050b50b44082c189034841c0301c100c0d8043e1040d100c400c40c11100310b41229106485046210031260034000c569181811684400320585400c0448104540c0060f070902401e80c520407985001402d081988001075074480e4505c52000c0400030802090005040951106 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 866865368 1250 866864118 866864149
    0xf0402040b041a030607080106120203041104020a05130e1303031d070f0e0903181012020423040c14250f1203050405030909130615290a0e 61
    0x401404206446081e08842440f030315900a004080000c1c40080c091148541201d88603200c00955103000f181600c025031005004544000046000c51800d846d0703440904031078902900c403590351302400079a07800305001542c044102069807000f08840c440f2001103210b00b81794103080c08100c023001c000718680803c0c009140c81400344a0741c0f500040920500041c40f040700c100702c126038165261610b07116124820b203c05820340c003500903917034600350500700e00d0403c0b080c0d03892030142d0b000c5410b5454601603900c0340e440718000851081600c003001c6407500340c1c00801041142d04000804c41640c02500300c3c018030106442c0c0c40004a0700d017510000c1c080780d84200303101d018000782d000c115a21f0000032881d0114015200840000303400a5558028883d0034005c64001c0011030800b2069801c01901107401000110103069145240c0c002494034011803038054004442001c1d810708240500441f04842e03040b2540d1805601607185086458104589803901d0300d18140c0c03000320030940490340c0c1c02c0d6000c400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 866866618 1250 866865368 866865371
    0xf1014010e060a1112041d0103050606090714120412050a0f031808030c220b04120c0503010f060501021b06030f040c080303090304050102240a0b0a05180a050a020c03030f0402040b04 80
    0x1e50034131241032001b00151001054424419009039551000080382400000e0840e880880416031a02e042010a079005266113048410856510781498850b00840d0342035655142110074041004041d4451150700c110a24100e404d04007881c03070081c0110b1810801e14181503803040340612030605c06041005985c0c002100613624103080300e6400259004012a518000c080002c8190020900c0d81c2c0700201ca45101c8450b08103418044c1c20300c00035031400e008660700c414403800010584c600f80900f4180001996000800500e010000781c2000188142c01480924041031101c0603134400341502d810041d0f070255498550340701d00d444039403040d45804c050341c42d20011041080001d0000000c000342c542c2a07094801401c100107000001c1100c0c0140e1180000c3d00744005001e2203043e40c4081404400280202846643c51011803ca8015080c00030102e0290404118500c8603501545401c2000414210315280c601d005441e202e010103041005013440010202d429507560750807491490000910 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 866867868 1250 866866618 866866633
    0x4030203090d1e0b060f030c0d0803061f210b010c06020705030c06040b011a0f03131106030907170606010504030f030207030b0f041e020f040c170f1014010e060a11 72
    0x8001001000440300035100c1d07202012000c0047c01c021a01800c20b541c0a071201c0d0001c00c859803000b100c1d80008200c150090380c800d86607400030018601d9545200782544641d0800d541034220648130701500014400410308040200340e490743e0202200c1c80f142c0e0811b82c01603e4503030600d000303810b40c499411524950300c1058140b0040c040800c1426040700c3c0340410103081502066101c2d00a40658020082007443c280001280340c0c00231071a40319100c1c030a02c010110000400000780b4540c1080e00c1d21407180d4800e000c1070100e191403040a542c8080100e000740102c1c82c100000130198403d50100814001003003401e0f608160007001100c021f1342e030001c0314504c2460702d1803410104000454059031141c0712072828041c003d50500035000085d402500040c80104047c1c01c0c03102410300c1c5a403900030454510036040d21890006015401a19007805000e481c2c2845002d14545804642114296411407038149540c1d0f031b0401640c0100403010349942d500c03440094410f65100948142c11101400781c1203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 866869118 1250 866867868 866867873
    0x30c07060e010207060e090105041d060114030c0111100c120507030209090708040213230a020301060206223009030506010f12020402032503060e0c0304030203090d1e 73
    0x10180441d0304020780c2250000369a0b0300040f00c4401d5640e8a95411503034000c01880141056081500781880c140d50107404148402c04070782c45d1503801d82c800046804442c00540759407401340b003035429056092801e0342101401c3c15030745495040c00c00c03502280959402c0c4986c0000e00a12404440249030030741081146000c1e540a4082d43c400030324280309040001c0010303c00350080e40140d00840d0003800282c113a2030b1040ca06802007822a071824003c0500c100d08000311b2203148180c2d4032450001d1380158413540340a6029141c894041d0400440c26004070540c56400a5140040361458202c8050b06119080042c410040f80500014200c41f08614001c000c50302e8100403204c080764420b2044510b83d0380d85401c8100003042074051221041c030895640300140c0303007a40256400040c0e004218003644004c44d40a00c08410b40c2000002203230b20b41a00f000280f01400000c1c1c1d0002508521900d0b510340799400030b40740e01c80c40001c148140d81440e0942c0034425107006a448141d40d41d042c00c10601000e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 866870368 1250 866869118 866869127
    0xa030c0609032102030d1d16050405010e07020604110a051807120e07030f020a05060c21070c090e07080f100b240708070b01091a19120302030c0706 65
    0x2d0000b640d40c0c4062803180807400071240e090400850b15940a9400c1c161005180405401c401d205003941010b900303030282400009014490082c56404d803448203c0d45400244400d071201680400e0250b10381404219540340c02180c41c0703038016070258030881600e1a0000103071110505801503070f0414808621a601070102e00c00043c02000f030350703c401002003060a11401aa549018642001e0b00121001c10000e541d9080d500c0444d0300c000c20b0345603006e0300c480c0454040d030801494404c80358032012051a04062a203500202000001030591504600d9290724000318050704c12200c8090f80c88404035070825080c490400a80042401e0b64034854844c1d44080e03603601c0c0c5c02c4999001d2854088052420300d07110400038a1000c410480b8080070420800a44a076001044240c41e000420410600003425656000f4080c0000400004d507200402100000c0b051080c40c1136406138000c540c40020721060101c1007000c4a00c00d80704141310b84164034080307066001d000c2da151142c1c03040340c0011607610b070007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 866871618 1250 866870368 866870387
    0x2040f1104033c03021b0604170c040c02070f0602030702180a0e1005010f0509090d0e1315030b0601182603040806012405040509061507050d030e0106031a060a030c06 73
    0x25406c584d00008950354003442c0281840b48960700084c03c001c20042d2084d10800104880c0c0702c44180c959451a04000c50103480408181c4030068001201c00d00000040030355034000f5200074030041d82404101d40c081482d0070039030b203031005822143c04005402110703250040c400e20581c4800f40d401d204d404038030307a030040e190a005201e2064488180032905041ca1100f00f485443c00d5401000c1c1c1c1031840000341c420000b0b6410454111015900045045040d07024041138a015042c101e07072300628500f080702c5074140140c40a41046141d0503800c2a41882124003000e031341c2d2007202100e0305101101b03c120041e410703d40546a5010100f40000c61090108203141202e01441c04030080090419041050400248000c0c0111b00103220a00c250704200b03080950240001d00007800e29140a8051703600d070f8100500803203059000d85100e0800640c14003035088007540e2038009110040c115503510341d100c41d0a01680523504105400125950385800355400115004070b032014400b5126000185007160 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 866872868 1250 866871618 866871623
    0xc09040603120e0f120a0b04021906080109050c03190c0203220807050303160f05070e090102030702010608240a0f020406091406120403050a090305160302040f1104033c 74
    0x100421820a01c0c00e068440c008100d60800c050046e01c02980d803070551184000c0d0059030045c0744e800280c0c0300049100d44ca400549880e07215200158500202c0ca825901c00a11010903118203105000c0141030540c035980402409010209414100c0b04c0b04034918029140009202044120011003408090081000b6254008143c503500c0da1643e040c0742c1d591040c0036402482c2c1100e8840000030034100c110400c4040c1c4500f003550304d001d544400302d0700604015685050940d5000082c00369998092051000400860010b0301c1c500700e69200400c0c0348559041c00c000c2c10b149190005d8001c01c0c0030350281401404002046450b01e840310740c018a145a14010300301610b01e11149241c5600e4400292115030892584200c0283d4969400b15066008610804144600c864012000034400d105010000d00004801c2c2c0d0414a980100400d5989801c400350b101490300c8900b00b001d10b000000c44083d0ba4002c0089104402d00b0001d040c40b18000300080e43e215004038440c0d200e07052100d4140c249035030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 866874118 1250 866872868 866872879
    0xd110a17220b31031b080724020a030506010f0806060f0a0e0d0f0c090b030a030e06070c0305011b141905040f060c140d080a0b0d1b0314070e0c09040603120e 69
    0x2c5c4814010380308005203002c0c1545030705024050000d010440111005a00701c0003000d4003e18102081c8241d0304a0510030010a440d07130304204542d41c1c0405110300c034000ca454000003d0038400080b9005c0c0c4181d41c00044803110005a07a41c020303000c0d001d0071042c260094610444056941013080400c94900b608070b07002ca001e20000500340c4090b01600030b009100502800c2c40340c20f19038041c0c4000071100c21282e00030b00103100c0b1030045044110b102000314005d800200da80b02940b1402c6201b8205030114400348130811100002c0c1c5003210050b1540b040c2240d48001d41540701140580e518001c580c404160360000e4507001c0364155106540e00c1c1002d2255065008264410150390385030b4a81c900d042001030320328000108810f80e07a801406041c2000362400d0f80b41d61140d1210140000100c4102140e012288030410812603041002080900c881c03010f0000103090248a00c440000640f0706a148180410070050940d144d80c021001154082c0060710141c0305100054030343c415451443d0f1165 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 866875368 1250 866874118 866874137
    0x406050f0f131b1208030406151a031e090703060e010c0503060f0d020619020706140304020f04180f02030d090f030b0603101a100f12020d110a17220b3103 68
    0x4060300b500d0071043d10348ad00380f05c900c07074540b080032403640f600014054003246d561996002d20f00810706100c1400703810090060504141582060020b0f183c0c000d0070781406a1400d6840f5075280e91040640c0c2c2c11400846041c505c2d81e4881c800a042185000030107580305400142044007814490311941c81c0c44c40580980340709659440c001e0f03645009040d54044606010400280145008885440da89100901c0060b10003044140c01c85012031404044035400b0500c80c0f0441035103070030004401c07003510340c0c644a545181800c44903107a0308501e120040100c40068003040d0302c2d607014031040d03a1051480c078082000400c5160492820f221510ba09400f9030300071a418102103121710b8030440f440b00c1036100c80007100c0c1f8040100000350302c51403900c2581543c03214104841540c0c0030003022031844030759426030040078400103002240d030054419100c003080c01084074086e03040041c004a41c81d030002001580c2d40c0c1c6002010180000c00b04051601c3d00e04828000c41c140b10b05480d00300d400e4080c0c1c2d1080b452 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 866876618 1250 866875368 866875391
    0x12132f03070e0106030c0908100c120608070303080403271d0c0f07030c061a01090e090d0807030b03010e0609071e0b0c150406050f0f131b1208030406 66
    0x407000340b4015a5008080c05005100040c0241c01030740491601e86040410240c0e41c40c08181043e40e20040070005a440d0aa51198294041c0e6424444c0c903408800300002d80c941901d041d654920f0340f00080911580c0300c002410300d0700889400e0507a40b00d0045080ca900048141500c4800f080c0c020746010044101c1d40c0c402140350415014400c44000b24068036100c5d200e886158560042d031422410030031140501d03000500030707025110b03440e00c40c5400110f000111b00000b42c018426a0040b8420030440c00c2000351040c0001084c00a15045d82441c603180e40b02c204c01100a4003c0010042d0190b0074840144012500014043d01c60541d1078240c684e101e4464406141111400d51030742000c8010442c14058884002c000f8100d00f14488112a04000c8031000078000708000c680550302ca9a4480400178801c1ca008055a880701564540300324a00d0001c00c0301d0000d02881802404000c000d40da9480300415011010002e4800c20300c2c0c1418803801c51500c4003040d40119000c90301e945c144192482c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 866877868 1250 866876618 866876623
    0x90907030c020d0e0a0906080f0f031c0209040209060c0601050f010c0c17011409030703031109060714030c0f010213050d03020619062103020d09050612132f03 70
    0x81c00302490303001d40410258203004075004035002e1446980511018400a042d0149124040050002c08081d00301b24034040859820680c00c03184090325a0010020010030003103070825010340c0145c15000503110b040035404500240110300040c1e41109002407810010f50740040c0c864101d5078221541209440142c00442c3d16025649004001c60340040051000c5610741c4100f2418546a800000e00c1a004c5502e10300300340000d40ea000301e6078000140140c00e155040c01040c0c1c0100c03000c5a0607290014640115007240314912010b44400000742007620201c10602c101ca1061845004845c01d001040284034000d6000d0301c8000d98030842100d001034a030030011046505990035401404560751002050481350701020340010480b0350b620001f041d0358102e10320880705191001000c1c5800e100c41d1601038905149104418180241484108010350f182c5089030000c02011010362210340342d0802401500c1408000201070a41c600083d000d19201079040301009004019040c5409101205258 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 866879118 1250 866877868 866877881
    0x30a0b0a05130e0f01021207020c010302070308060907021c021b10170c1e0301090c0314060616170310060c03050a0c1a040818090c070f03020709020f09090703 70
    0x182c000c4504000b1981c00e003802d5000000003030314074003a02c0c04c00690340040d60899009602146540f0314810900000c0b40d41001020380c064000c0c2011031500714a80c4010348003100003028903210710026800105074074401d20203540c000c05125403449043d0b55004010751200c0c008104011903d0040852405525102c071441c03445076425100c0c1a00c05a046501a84001006081c0d5591031000c0084134101c2210240e106451030300781101075200c2d410001040159500d080590f410982040c42050031000c01854403504920101d603010703503820201405004007c9006006020001c00c1007020300c0030300c2441d004500c101c004d00c4076010300a88a400a4410714811000a00041c4050120a2130b5a004031101c2a0080c0141860f42c01081c0f0358410040c00b2030700711000c0300c2c818070104100404000090004062600c200c44010452400320440c078044d020301c107405018230400740701c42d00c18903001307200b02c034041d1a00c00d105555074840041c1c046203541c04442018040c1d0002c01c009a000f501c03d21409 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 866880368 1250 866879118 866879129
    0x10807080c031f0b06070b13030e0103051b03130b01090903030b121b0a12060f05070e130f0b0904030c1707030e0d0c0510020f071413020d0f02040308030a0b0a 70
    0x11900070043c810740b401460082d141d1030308220100000d00100e000324489900c41e205240d01d1131400040d030710300201445074080700b41e03061600305410b004602d04180305a003205601700b200251643d9698504c82c2c200d07042d014018290f000d904002084040d040d0308804000c5000340c40900441d08070f14180401c844801d20009000d400c01140d0f00c024004a0501480111004001002842d00c6030f004101c0744000b07000071182c10341d0f1841862600800c0e80501940081c0c41e00745444408007200105040c2e00d6001e44840b4910f40d200310380c0d012262a6840959150307406880c08035545400c0c0340240c100d100c800000e449001d072070840c10700a8014a0220740c2e1465040e91044c5c461194070040c420301c0c510b048000c03610800080320118203610b805900454511340341e8010800310403542c003e80d00741101c5405c503982c4071603a00300211a9440388100e5000000c42130100682d0346511520344002409106540007050303000050000501601002441c09400308460070030000f2006000c00400f207202d40b00d034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 866881618 1250 866880368 866880403
    0x302030d080108071a0915030a05090106051008041a0103080c1203011202190801051311060f032d04210c02030c1e0418140307051c020a0506010807080c03 68
    0x18441d007500f00f810744170100040c8903404d0404c9200c070b000814503189569803180d042c0d80801044400b9000b400347c19002003641000b04a0b580c188404203200a455100401c24031400001040806c13802c1c81d500401003910044080c1c031940c40c0c0c645601240e0000d1984401440707803400042d0440510002c9038120340714000707448552040c55091050410148005c1c50b07032a41103032000a1403920a0045034458460400784c400c503d050791420301d052080006209021701018400b0031404c0c403050702200d40002c1c0308030407800500c800400d074000003100b0f0070320301400601800600c42040131400c40c03801030800d08001c0c22005803440500702c9000d01c0d00f00000e5456070250340b41c08041c0c148602d46202c9a020584001c0b03000d0304840c0448c0503104102e410000d0100044003c0c401d22404044c403813511480c15024501e01030558030750700e41c0c603e0440c1d00824003483c8c100c0d281001d60700030090091b5090307004e41a01d02541c1e580800c103440760b409120304072045c000c04026480d14030740403401200440780b0480 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 866882868 1250 866881618 866881633
    0x212010e0f150f010302130b09010201150506070b04020d0c03030314070206090c09070e031e011407230702130f050c04030201090b0a050f0c0a03020d0c08070b0703020d060f0302030d080108 83
    0xc000c0f454202603540d42c1072550800048007170001680044014024241d90156100384404c002400c640c100c0318403142d003a0840009002d0741d034400c400c4614068200056040d103440b01c1c00090030340c02c5013880062044071205800820160107030014110701110140c50800d90fa919541070f0785500048601c0c1d00c45401c0403003941600d213444460316402108900d0310091001035040800c0ca40110141c1c801c0720b00c0c11251a0901489090181074200d00140d0f018520900b401c02c00680f2800440302e003181025020a05800c0302113444054400c10b6400400800e0401174462600c0010300208400e000ca49042500282c4e0440c6901c0c201c0d801c480d03040e51051a61841e240a880c429040390b81c1120801008103c80e0f0400669140a0701ca80800f2a002c1d00158400b440c0107858100e400803008180301c485001c05000c10040400d4504950704004c0b150403650315410124000c2c4181d40103604154584000481e908460502020a4034400d40c101c3e003000300c07051400e40304c7c05d90921924150340d00c40203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 866884118 1250 866882868 866882911
    0xe061914011404050a0e010305010c05120103030c0201020327040f0b0f0f03010e070609170106120b070c080327030c0a17130605190f0909021803010212010e0f 70
    0x40e0340070554074002c5141c10719440d2400501c803518941e01203000c03408403200501c01e005003880b0340c02290090382460351070100700910450041e001413101605214000d0321010540e40280101c8001454a5480008a21261084021001c920343c1114080d61800c03840e61482d648500c0380701710b00c20006003075000c41148081001100c1842c2c00c50304c1c0c1c141d501d07407021b50481182000400f000c0c1c03029444040b01c060a142c0a43c0740c2088030303a8a014140e040110400250f641911182070039500710003460b006a560303200035141c0001369072000340b814200208001014900d070b02800ca40188511083c18911101400c1d90b5490107004510034207900000840d0380041c03c001001201d18103100c1c503680c00c10701c0c06202e8080c00c1c4882d0344281c01149000400c407402d400c0c0e0580302c40c0c07424018144951004420b90005160303007654014260301550010340c40c41c501603038840030118420300a009540d911b400795008900c400c03080c42200c226000750808140b40590803107406100e032145500d00e021000e00c60 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 866885368 1250 866884118 866884127
    0x20901090e01060e25030c0e0108040618030e010906030b06160f05101d03280c060906090618050303070503131b080c0d1a0714040e06191401 62
    0x7080c210700c0d0b60740c02c1d00042192404d00e5052059000c4000f03442ca0050410144603a130001c2200c8004262400450b00340554024500545018081c41d21018541c0c2d036141030401003c7c90759000c440d2181862030301080540c4000c0c6d41000c440c0c2a6280420113585030710580590740c054450315800304041c0720000390103900d05807820145000741019541100c1079100c07a41010707071441d002099144c84984410f10403071044145000b07040d01d00000c620b84030300c85115500c40340642004000c2038401503400403040b441481203010241d08048200107686080ca484070081071180c00803920305082c880070086040c11004002106034016020710302d10b54800f082298107500003400b0036015080b0600751408107030083c004600c0170481c1c40c0100c141c5428240303194038000c3c032035075a00d03c43c03240386043e48002410300100e04494240d00e684401240c030307400404e071440d20540f80c08000303603500810001560754289040d02d000707034025a07c105403c3c00140084004080601410311512a808207030001d55204 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 866886618 1250 866885368 866885381
    0x8011d010c11030f071e03080604111911120a03020c0c0603060a14030a200103050a0e10150510020d0e03030f0306010503040606030204060602010606031505030c102a051902090109 79
    0x68000792006d407a038034101c4600001d4400056000965190807c001c1d070526200d01100202445180c0307007000d03500a11640494440c1000c4010041074030300859a82c0c0f001c1288180210306d031802d803030b190525180000d009401022200101303104080c051740c007504180c41100e003d500040c20307485d0040d0410240d84101d02802601c990180704940b555808107480c04010140300814498107105140d4a01c0010b007a0384024102e40e4440d0f00d40042021000800a0a040303015520440400c0c00111b4550a050a54207a4051601302ca03c0d4031003552991340c0803031030740303610800740e240d000040440c241416900c0c01508410004090b040010038101e40c01070011f0b642c00b80c0700320f50105101e9200c0d80840d09880c0d165000c000581e450355030901c03006030140946164641d0441c030f5083c0562400000030b0b91520000c1109000b2554111546140b03445600400807101c401e02c0504564181003801c00070342c400300381d425074050280d51000b01c074080b0401803022505400410f050541c0c1d090004d0140108003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 866887868 1250 866886618 866886623
    0x120911010c11041a0907020c010509130906050a05070f020c10110c030109080a170f13021225060201231008100c1403040c0608040c08011d010c11030f07 67
    0xc4100c2ca120766981c6002d4154100c1010348180001050101441000680a00400c09541141c8402c2d540341c1da01006039404404200d940c6100005c1c45802c0c04010030045030043c0c03149041904005080b4035503004640a00b107190340b030029501440c5012a26002c40517a851342c0200d8003142c040005104600030801d40a181c0c05070b981402840c80081d0864028072021244030340d01040800601c0e8012148080d82944140d00e06400d00e807034103009000d03210003480c48840c03038500c0d1541015519a503c3c1608c40c00405400c64040d00740c3c0d000a03400c50001c02e50003100340b11043c00c0c003042052040c00b80c100d45414003110611f1861a1080030745075480e00601020091a40210015074a1005c01011410360000c40000400c44400c41005014501450722500b200c0010400e00c800561100503620031103200e46007504003911340d0702c0c048007440c0300303a84a003c19600b49601c1d10f0007041512205030105d1018002045041d41d0f0708825a03200103000003040e242d0b00244040007045000c940202006032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 866889118 1250 866887868 866887883
    0x308180a0b0319060e0a05010806070903051f0b1309120c020609040b0f032509150e0a110d0b0108061c0f06021902071706010b0a03020d09080c030a120911010c 70
    0x244c440d950302c5c450580031a4842c00b400e0f1220010030146a081c0305603900500c40b4a040001107041d500c07401d0f56898540c1c055000600e0444000c1071042e2700d41d0204a40700001030224000510301c106c0d4101030310b0b20210640d111000c1165034a410740c041d8030070121096001d031449007081441001c1000500e032000c28075400c05a00418456541d900340915008024107640180003400c12040c0200c078030b01285c04c882405880c3ca6816030400f403c0d034441c82c08907203044480d00180d984031102c06014206107043c4038500e03100400c100344d20000680081c0d03102c45003a61101201d90b5a0300811116020b030044941801320a45018804a042c3c802001c4d021401158003614021909146071251120300d81080c00582114006101003600d0f04034110181130700708001d1501c0d5041c81078041843c81911500014568005152404e05a07160440420301e038108490355102c40050504a449620482c2490001925070540d51041000f030310503450102d400c42403401111070302034015604040075801c140c5824 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 866890368 1250 866889118 866889131
    0x709031101020c040f270c0e150418201e03031303030306081009030806040b190305031b070e0406020702030a061b030c0f0e01180306060308180a0b0319 67
    0x161618000c0300c80c1c0301d00117840003800e413400b02d040e48078403043c4079003a1585680070303c00e1001040004d0407080549080c0c2c02011145e807034681c04081100300e0342d0b03106a042400d001c03010707091140141e01807103094000c84500007d035592404001c084001151082d5000924180c490740c200940d0002100000001d41180d151000c00300c064440644036502c1100002e4990034180001c240038807a8095a0360f50500c10301ca210303000e0380d0183c400c41c40142460701440d80d03050740240564406040e10010a4983d52500c840c40d10390525585036804410480c2420010000241d01104002074050403580700780741500343c0303803980e0f900c5002950000000b44c0c0e1510492610102054061007420344000c480c012480669045841c0642510703a0802d00c5414050720b2008001c00315040317034188079034400905c0c2c00c83c8032690200c1c40b2040d60300c0c15000030740701c589403070408800c03c8100e4001305044241001c40a076445101403c002c9100e055000d1081c40800900c0421503e40e10324002c0700f600c503a40c00002c500c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 866891618 1250 866890368 866890393
    0xf02040906080f19030206041101090b0d0f06080a050a06110c030a020f0c060a0f0e220e07050910030b0a021204051501090605010522050a1509050306070903110102 72
    0x16207266070030440c0c2c40d411214030758950f050300300300340d4050340c0720440b44401c0c080280e20042c1d21034400500c0503011311842070994440760b208000b103038050001160b890b5100d03021502244000c003085069407440510b004001710310b0b12800103020280075809001003103040c107907a07180341c007030716025204660541051029400d2004280b000e04443d468a0f401061a04202c18059141a41c510640f0b4021007080107100070711781c0c1c84580310642081500b0a0940c030541c0030003084800101051b414060029174985c42d200854907000404407072580021948025160300820442a1041d01e14007041c2d40140c204000283c03000800c5e40e48440007103001401e1201207411119043d008590441e01c50700014012a103080b40c2e9550240501380b0360710200011420400041c100344628441d010703800038581c05100908040e41c0072035010f00405030030404803d40d200d10440b900c40841800382c2c0130440900010030b4034180020410703c00e0b03240790342d0007030540c3c07454407141d000d803400c600201d045000f420500c805 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 866892868 1250 866891618 866891621
    0x3180303040515370207090612060b130204121b060e011b0206031021020a05041d070605030106120b01051b01091a1803031b031f0f03060e16090f020409 67
    0x1180d500c0c0f13101041c00181060000c2c20544903030443c100f0b0600d000020700c1241e4540c026801007030b0381f200e40000d883d208180002c003030140d1203c201808a000080c08180c80300c0502442111a226950540100d01800300360300c1d4502d640d024240000701c1a6200d00140c0d80708601d042d0b0a124040700e12601d0f1682130300450000d610031103003c031010124a4040151800c0001010a1801071000640c8280c40c0c640c0041d00c0001e1034442c0605c11134032030f2000701d1522041251610b03881040c1e8126601c056580c0d102400705e410910034100451070a03d1180d1026090b0b0182240488059540c3c80c0b9092080c2c00d0b80381d601e401098820050340d40c9820210000340304140b4000000380c00c5d41c41c5042031415008030f0401d4003022820710465002403081c4803165801802c1c0041b40490303080c00c1516550b402000d694203210074202c8480c030061400b00007442901080c01d46c0142c9003d240207108002d51501101e59480f0b2218580d40d01080040041156070440d81c0004000c4414034005460255109000760 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 866894118 1250 866892868 866892937
    0x102120307200604030801050f0409170a0314011d0601020307050a032d020610080a150e0a05030d0203090105013003120c020c0a08010612060504030504030b040503180303040515 78
    0x31701280819005000703500d800107003039544082c01c650600a041c2250703039450a001c0403014410004001140d4801180e01a4001b0501e44020301208042076946646000b041900c1e1003071081c114100d800810385651011085440c00c43c3c0001c02012138861698003242ea403101415102000402c0740c0c0d003165025404030304410f4565442c1d0040c0a241050480004507a040e03600c04000c1740c4c00107500000140c4407060119840c07203e0100050050303140c010039410040c07000c40003070403408006070a007010f18444e4040c5000d040240000c1105030b894080944040030b0200c5001001e00b1807540b40302058040c0400080f400c2d20070324005205034555103121007601c1101c4032000158000b00c2c5200d2540c102500c09500511a010082c481c880c60145000884107118401800c0c07291a03000040c24140280119001554418040051480c182c20040e45035046544240402d00c48004030000c5458004146e5007a60310051000c00946000e102956003a40010400c0e03040004c03034100421204000380404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 866895368 1250 866894118 866894123
    0x31707151b09080c0105070c051f0e0603060d020d1406090d271502010633080903090d020409050d0207180618020703020c0a03080a020c0102120307200604 68
    0x1c244008019100c9110118020071502007080307446041054400002e21054086001c0c00d01c1e03a602c041c241880151204030303030131541c1c00c04400303211044803195404480941506a070748426034050144100411440150f540c0c40d0700200c80503c43c0003514000030030707500b594070441e44055030440c044070392401c00c0c0d012075961600760010151015050b1b04400d803140d0f401d416001c60455503020b05071060381c40f040c40c003588910000350307111a00c40b98002d6210760090701103a090400003426010f11004c2900540c00d59031880f00300e540c0d00c2e0325618000d04950b401407140001540c10581040248289100c07040c0060381d0051b121441d040100301c003442501c041c60102d9000e000c004d800e0408600742000c10f1000c00182c240342c03002c10001a4460071509491941400d40903039213107030500b802c03854a020f94a150360701281d00c0700008104072000e0000c1800400c150256149409110010780e00c0d0807103002c000e10325000410004000d20301c10b0003402e141c420026048841e0000c3e19840381d18110084404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 866896618 1250 866895368 866895371
    0x101109120607030c2f030f0f03100605090a031104020f0c030307170c30090106090c170112060905030a020c04050c0702010512060a05042a0c05030403170715 69
    0x500007a240d1500a04411032124206002084400820104002d4a24000e0352255000c220b003626000f5041c000c46488447d4158010707110040c150046043d0b41c0180c1c1c03c0100707070303801240000f8628007501c180c907075180c0020010441c440c9951500011502410360503a803203942040031202448140c000391000003c02e1000310340742e2034401d00c00f41032240c500b1983c004050210080051070a00e8600f10394407411803110038114050b02c8951500326100100404040c019041c04000f00031505501c0a01140c4c55070509014251125000f81c0346860035074981c0c20b0561003e40144415200007010001d160300c185000152100c0303e8603885c0c2107400c102240c40c0141c1010120b41c0c400d18040c02225007004c04441a03070300d0000e0319030010748144141c0c0710007440c0c664070000049055640140780c200030a03000e0428000d22440420b50b5440540086030540d030442d0656000781103511030b00140c90159405002940351030b0130342c5c44a000b00c4d64007042e078080400003040598001034101c81032480044c0f49000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 866897868 1250 866896618 866896621
    0x50f01020a0e0414191104030209010612050c0306010e270f0f010501212a020f06010f0f1206020f070b041a070f0e0f100906201011091206 61
    0x1048150b501020783c071011390458000388004001440500700442071040c2c0c00207440c0304c501034200c059004592029512280c10320000840076001000d141d403104501808011555444403c503119000035140140002c100c0c038040b10759403c01c80e40d4428110318115030803031022000074140306403c40c101d52900080b070b080401e0042684c07402203000d0241c031090820b00c1351218424203914900044100d4840c00d03d8843c22031099641e8074090401004180702210503070001d92810280d9030ba91502030194180c841c45000182a01d90b444d01c031019104c076070b00316103806071900c029075880162032617060355041d5081000e0486040d44400a01c04544242d04041580c501801d0140c10104120b0600e40d000407158200264254400d139500c010520508121248052000c081040c581411f0100d0344c101a0304151100c0d01c68003e0803250460300d82e503984402c03e07102c4018102c006e07540c50041d4503550b40a06040c0940c05c56581040300300b40c001040303490801e480c240016691455510800c00580c00000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 866899118 1250 866897868 866897897
    0xd09050d2003090913020d0b070f180e01050607140607020c011202030f0c1b011e0b0d03120b1201021c150b0d0905150703050106121116050f01020a 65
    0xd090400c00c00d2001d024508240d080c40214008510080040c800369149508440840da104039030800301315005124442140340145002e01001c400d041400041201d0240c00281c00c0f64450700981901c40712481c8540607407910041c0316894002c204c0840301e1a025003486515103004019480c4101140c1c1d00800160f416107001414940561000b180c0c2c860042003041080c0320008403aa4000744001c035016510100181039822665a109640600d0750038080c1000d0010310225800c0b0040c031070800704000c1038804004101010300811002008100d10300148420f12805074003000203681c02500103540016001d490301c1c00c9170f0219509800f034110444000d80010224483c0c00d0a404000c610740460500303080e148070307060180404440c10f10f0784500c0d0a400300042808407503803c00e1210749600341800d04003406400b81c44240201d00004404c40c0b071140c86002c5034010030301110400d0030811724041242820340740c202e0200e00c0c1541e06100f141b500041c1c1d1789003440204003190b40e079a50468110680c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 866900368 1250 866899118 866899157
    0xb270f06031f090c03050a0503190516141018150603020d030c05011407020f0606031603111c0f050606091005100216140f06120f10030602070803180d0906050d09050d 73
    0x2ba442504100007444800c16042010381c51a58460308181401e594140e03000d000d6151044000b4004000c0f41802e0b40740c1240540180e0a0014500c104c00e01c031525030020495600700d0380c2502c4042d40c8140c0010700d91002c41c3c001c20008140c14050303000481c0b045c1d074103400e002e04c450058030200016403081680ca20003940500c103007a0031050031406000d4100c480080541c10100d54040a440d0007640c0030790b140107540d10b2129114485006030140440c1c9018182031401403050752050742c00303008440020b03c192401e40f84062190f124038800f40681c1c0e044c40c1c24815010042d00841095101c0c02180003c001c0e0011030b040000c06981119041d204d4a007014080084d034125480707801110288042000442100c804e1540001c2070703a6804100ea41d00981007031888050342c80607008510000307a02c018060076170003c5200f07010100d80d50031102401e407041c680c1c07180704000300c0c4009141c1c50410301610740300748000e21752004600c0010039920320540b240c5040680301c04042c8040b0702d4851803145d41140b003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 866901618 1250 866900368 866900407
    0x3030f0307081305070b25060e0d260901090b0f070f05030402130b03120a05070c05011b201c020a05030f07090b270f06031f090c03050a0503 62
    0x103036070b855224003c640c1e803d40d45250030f00030003041040109454400120010f0300812100d03030700064207641c60983c1400ea008000c02d50725140c103030060301c060741c88042c020681d24610040c02186014000002e0025107083c80018050380304079522000e410001c207140503001030148500c810390101e039081c00c110107006941404c201805000d0140200b001607601e0286198004850100100e8100446000a400e00d503985901883c102c2c00840e521202e943c1c400301404100d0311608151000d6903e58005449100203d024100c2c030741101080b400001d0b030102c2d0080700a502050480c1c1a4012400000e00002e10131102d692406410b0000b150561421452040c005d00701680544048d1002007640d41d2244144e008044d1000e0710f901c1a01000c1c2c940c81e940301c00c5144054a0a00156541081c4240c041401c0e942a1040b03240f401c0454401d26000c1050442c2424564416440301105c0c0003103006049400c00940c2c0580c1320b05000004030303005000304000240f20303401455880c241c0c503041000c550325 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 866902868 1250 866901618 866901631
    0x150f12011e0c11120c07030c06050a0801050d050a060b0a0906030506100501050a080a1a1e01031a062704060b0a030f05040f0f0507081f0b0409080301030b1503030f030708 75
    0x240680215520070f010403056960495488002d41e1070200c100554a400b0035640b0081c41251b5101000a00c0f80e4441c0c09011404d07a25a25a16566620000c0048440901501a0054108203529000550183c0c0051202d038800f80c00c1c0b18050b0f9071040c0c00f90071503a09030304c240c0b0b05070007030002c001c0c40140c4e1403001e0f40609000d00300142001d0350000c0041030801e00606d54480c2d90764598410480d01e40508041241c040010a442002001180e0b204090740c8103219050109082c4000a070114001020300c009182e00074114030301303200500c3c22548a002d010503a03000320004070340502d459a10740b0b010340f40c0980300404140380d030707400c85100080440c1d602c0c90480e81d40314a80003e200000b000781d01040d081c2a00a07000c200e0302001d40c20500d090103e00da025481502c1a01105064482c1035000541d920408103810000240390304280f1060324034602005118242c200010310020b04007108150308074619001d00180001c03a000801d185a001e0001c4803074540d00403040111495010008940c02030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 866904118 1250 866902868 866902877
    0x301090803130f0609080a171b161401090203060a050903181305040b07140c0c0103150e010b13050d0f17070c0e011a03150f12011e0c 59
    0x52403500c9040a60002070150040680c9210440d01404404000d00c10300513001002001076502c0d5140c148255031000c404607010813469902c0544000240404038824490340400c200f150b0a1050f411000754443c03896051125040c0d020315010543c0b4403002c4c405c0800c01c1000103a5800140105460480e0051242d0301c03071402c00080010303140c004030a0f5540c140c2e0300c1590540610041001508a83d201000c0a2603e480e060420050022203c0400e0107100c8686a80c00c2000c410f001c888800c0c40381141c44142c560180c100c080c4203520a52083c9a61604115442c000549820131440305803401c1c2e2100c090340f1408903001070305011001030540101002c49449102e4650350303941c01c2ca803200c41140a010101c00d40c0390500c40c080c048088451ba01d5002c90903504080e01d91110502c0c0043c28041c07030482070f81c142c00c504031007a2010103c2e401031182032802c03a02d011040c4208a91070943c0100b407504807001a2482e0980202401400382200c0800c160001c0300642510b0710b01100c1d02da400c0e000801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 866905368 1250 866904118 866904131
    0x905060403120c020d021c120c081608070503130e06040209130b15040303020106090506100804112e0e04181b0b0f07030f020a0c090203071e0207060801050301 70
    0x380b5a002c1000007044a41080d440341585800000c105904009002c1e41141543c41e50904900d85000c5030021288036030811200448854403c68915028240041c24200c1c100007100c0c0981840480d0260320340320307865240c40c0042304e0391403c0c00c542000648840240c80310405021500719850031540c4800d0644045060403107420004880400740c41d81c01003101d545201c80d12894a03071040101548020318500c0d42e0700c555900d0004e00a19036072054417101850240031481c1c514161100b1044d9107003554540456448940f40c0c2240500346c00701c20303903014550984554081c140c44440140321303419480d072a40e804c00c0c0c1c3c0101926031800f0403901c0744200c0c40c1a0780b1040c0e03500c02440c080489500b03e44525059058810304480e0300000340c00c4045801000300d408403000718283c000740b5505100e541c403050b0195240100340e035150002c05000f0040c0108400903c5002c400d0303406140d01c413485151900d1000703c0d4502003c01021008a08001600300c68018420707250000440da00400b010340081206 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 866906474 1106 866905368 866905373
    0xb07091a120c03160f1728050702120f0d14100902030408162f1002031c33050a09050402030c040f1d01020a0905060403 53
    0x74201500003810350351100040d60f0061002803249940b01a00c660306803110380005c1c07550b404000d900c44203080c2100b4105400c2c1d01070112044c4044e000510b0b0301008a44003150529126075a007440d00744000703985e00082942d20030944ac0c59103911108600c41c48640b41c4a4148080c19490500d81e5458519910711302103801200f607440c520401075500c0300c0183c280c0c0800c840242403160b090005070300c0d210b042581c44011342d1144031600441c66a0100d00c0001c031040446800000300d03090107900950420320040400c0303514500086041c0440742400b003001500b00c03704565010784520b80454280500711443c82d500360986200103903007903032030180a032421086c0708051040742d69200020b000c5100c1d114150145401a01030276405803d0340c2440060001140c0200c0307007540d1107500d00030540b20f0642910300215014009079035280031107801003418801d500050b1281508000c200300 = true := by decide +kernel

theorem cover : BRFrame.Cov 866726618 866906474 := by
  have h0 := BRFrame.cov_init 866726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 866726618 ≤ n) (h2 : n < 866906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
