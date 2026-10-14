-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0956
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:29:17.588639+00:00
-- url     : https://prove2.me/submissions/0da6589f-f042-4c53-95d0-a41c576d5bf5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 171762589 ≤ n < 171942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 171763839 1250 171762589 171762601
    0x150309062306130207080d0905060a060e0703090c0f08031e0307120903020a0b07021c020c030a030e1f110c060a170406140109090309090203010803090907050f070b 72
    0x8018024541a0111000e5800715a0444072009000c000e0003a44180346411143d244658070b60704035442243c005a81c1540d40700ca40a580b0050094400d04039400c1c4070b2240082c556000b076101c0c201c10f69014203d08030154403044400c40240030f1b46070b4290340c1c05202c032000084e03034840080080000c0c0b0601d4042c5480b95401d160403001207140c04103100102c1400c104001045601003040000740c24008400110314000f428101c0c038008214000800466140b420300030f07800d4000034410141d4018400d2810b9001301004120f8a88005420440d05580700c8105800000d010f070f0304400035003201034602c2c0510301d198043e0b03031980d0038442c000c200880e102d010364902d103074020311490341500f030252825071034005800c2c00200bc548240d601040d10201c041c020401708056504428000f071100018a5410b5071158810701c01403503007440c1280818554500001c0c011a00c1c007c0d24120750404003d103051110080921080c0c00000f06800100030080108100440b4080040c0a02d5802801b584400f4030b020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 171765089 1250 171763839 171763841
    0x6032003090c04240e0c0d02070b011e0f050d030212040e01050307060e0d030509030a0501090b090f07150f02100c030209090603060415021815070605060d051002031015030906 77
    0xb00b0109489806020110381321600003120302c4210b03180101110800d0f03890301c421007260300502840d0b00707110b03000003924024000d80c3c004080c1601c0c00c43e1048101004c80c00c03500c0d074501c07a05229110400003d21800c103c0741c074124403c6814540240144c0e244500345100c4041c403070384950407070350b80c00310800c006211074141001000c01401050824a0031000d035140045c1a07288000c00080420800103080b5245403001e21040740d981da0b0250080c0111801454040300e81802103a840300544164070920445400001b401d10840e03441c40851503841c3c0500100320342040c01c1642c10401c0d4440c802e82c0c0d14940340944100c9512240580d030050f11034509408000d0101006800c45203c0e500400900022502c49000000c1d6107030050b500580d81c92020740c10b1320b0035400d403900040d40040880da0003040c54001c80d00424501b0310544003003003266208003c00c0045164180084c00691000c205168841da0650046070484108403c205003182c1e94202110b0207400301c05030400007030315100346070104026 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 171766339 1250 171765089 171765101
    0x219080715080a0f06031202060f060411091306080a0803010e010e010825050415030501050a0c0804030e0109031e0b090303060d0602091507080a022506032003090c04 73
    0x1003248070840010440300000d06266020b81410000780e80e95440b201c0da114141d000d240195800707102c4010003a03040d03a0194a805084a5540b05030082c48002440e616140c422907039615000703040a41054400028080405240c1d40c44070007403540c824010805403000c200841c2c2103803040303104603030320340c100007418120230810381c0100202d62040c3d00510540308085034a02407900100007414504c200940c071690701d42403950040b60024a42003642281400100c80c110039680110001e01090319a0b519020440d049203520000203a02c24011400080c800c08403100c0110341490402045510fa03217035402000c10b60820240140310341b500c20410003650a43c03980e80860441c000c1e5007145096004140c100302c4000780100111750004407000181d88980904105c805150701d007a896200a01e0818415840700c446440944a442d041d4007541d60605456103030702158040300030203a441c001d4150302030301524002000ca01105040c010b0009400d80c003a6202c3d5000c0c43c000d00c294102c00e400d110455013 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 171767589 1250 171766339 171766349
    0x506131514041505010507020a0905010b0a030e070f18020415080412030603050303010b0c030c030a0c0c09020307090515070203010e160b09030703081b0a030c060b01080f0610050702190807 83
    0xc100303042c41c03101d83c00c58140ca5007200c00c2824825500c1c0040d10024200d00e0580e00301148040c030b450000f1a44540c1540035101c0748241c2c0d10700f004000d1500d625180c0e1102e0500c01d031701c1e0700c1e41c4004052000c20340c103a1010b0058000417602508064444000e5000b10b02c0c400410703400100c0c00000c01050100c14040d02da100725440c101042407a0440d00c8042d141d1105001c0e41e810500001580c1d41d10010420499030040304400541c5d46030200008000e00368603582409544881888001096001c06031007100d008034074039203500c50940d1920041c409030840d250803005d2600414400790b00583c9084c0030360b80e02500401c0c094607020744403030000c04401055801195050a06005801d0603840010391002a01d8000062540b129100d0325000440050200718410754081c0c0b2081d40f04054000c032803510454030566051121039400401151082c0d002c55150011b52203040100c0d17040d007044118a0300d50340f0a0300c1c1c00e0b0f2030100710350003081c2e8021001c541d41c41c2101e070082d41000068000c0c0a4440582 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 171768839 1250 171767589 171767591
    0xa05040e060c0f090d1109220204110403050105150301050108010606050d0b0a0b0d0c171932011805190c0912030503180706020d03050613151404 64
    0x4100c1514803a51080020b041601078000080c0c000143d0008006030380145400900350310380b0184501d0020380403008040381c40c0c000e98100021640c0440f290398840039000404140100708c0c500ba4007040043d00e40021041c4d03601c0d01c1044044041380c428064680708842d00100d62102e002ca901c1414216101640102241d0345006000d12540b54480c04440400e1110700001c40c25900b16000100c4403ca183d002030504800010b14050700020b079000041c1d0007869468611103500e403280401005002120000c482e059040007000d00c0c088140e01c070315088601500c1101c0c0040982518112660710210a0010900c500c2d004002642e1007100034000228620f00a1004c0d05004404210380308152220103e415200c4419031801fa20894100c801011101200c0c0c0c0700485608021302143c1c020784040d4114211b110302e84c2800c4c540000d15404440f440d038010408440c064008800408025003015442641c08030314164116050096801c203000b14052032058501e0100404d4100c4401000d850260f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 171770089 1250 171768839 171768851
    0xc09050118050915040513060b091006030c030b0a06020f06060a12080705100212070806030d09170a060c050301150305011d060d021e010e0603040818010c060c020c0a0504 75
    0x401c00c01c0d4030741d074115001510414126103824184403014202ea18445400602d0300c0e0130405510310000d10065002e014807810020300403050288269854121080100c43c2e001071000c000d114480d5000007200c400340e00c0d00154885542d0700040d1686202d0780000c2c0182e000190350f4032942e109000140d00700e0811a103149a15103803083c0c00b10203d070b0483c0064240c450100315501444010300840c01c414241c3c1c1c0003113548501441104011040640e00c100c00611a040041e400f814001540484030303211f074651100c2c8524064191141e10151082c01c9124003c040000300000c14a002c0c510100030302ea2036141e1a50b050641c20025042081122410182440010880010301c0044009c0016408101c0706071503859a000c2000c0041c1d403c2c000390000d07500030954504a00c032820a040c40c007400da0f9103011030340210040040d540019540a45a014100b08040c440c89881509030342400c2c060400b442102c80c25203441e8216030301c0107442310140e00708818002003442c10b484400b02034042107a0802c80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 171771339 1250 171770089 171770117
    0x2160e0a0e0312010504020f0c0d03091202010b01020606040b0d14100b0312070b060d0b04051b030a0503040e040f0804090f060603060b07020d0305090a14030f010e0a30030c090501 79
    0x60f20303061190070b000359030000e41c5820703410402c81120602c012050444d074041000d203900400400d001d0000791030a0a08070384004a0b68410b000340d40a0302d8050b0700501080d180d10040100400c0310541c1241c6c08181180c2400004201800356811528080080d01414640000d1401076400c0038400d14442c2d0012849000c01c8a80d41080d152195000202010076a9400b1302260b1130090280340030348070010040400c03007080070005540812501070060301440c0309008040c5951505280f100074850340042c4000d200742010707a1109540705010b01903007030002019403a03860f07180d80b080d00001001c1d5161400e000b04028140110b138000c10f040d01d41082010314003e0807079282d0040ca54028881c0002c1010a424140706034151242c500000700401592540c414400603504510101d10307000780a40c0518004208041c03040304d419410030009420000495511040a108001c0c08080940c0818108450740c04804140e01040740c80740c1c4ac005003d0014003c050400b0049a00ca24100440d01601c510 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 171772589 1250 171771339 171771367
    0x6020a0209010e041b23150706050c04031407030506150607121806030f0b06090f10140a0806031603030207051509060c01050103020108131e020102160e0a0e03 70
    0x104607200c0103e0034015494510304045904241c40449604000f500340c0868017a1440d1102a04c1c02c0c401c40d0040b104d80b116005200c0c0c074080b40b00e01642e04c980140300d5040800e2458001d40da0003012240c0d100d15058403555164104100c03110100354652180805008000c0c08010b015046590f01c0c90032203d100094000550f68840e0342c40050818005601050500f4058080c03c800f0a54081c0051405070300c8010003802004852160907138107050a01000b06410010111500c0601c040c01d9482510100da050000900290f0701031000c12102201046004140001410141c00e013a62003104a003051010180b034510078046018005003200c10400002e6000600c0300203c81040c2c44482c6c0f98180c60001c15414050014610307001780c40000d021340130803070651185050f40d100340c1311145180c40f0419049408100701c80010400541030890480303502c4204501c03d0039910510440318031444107405450400400da1041550310b02038401d00960803414041c286c0313a00b42950046003041c20041c2184 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 171773839 1250 171772589 171772591
    0x1050306070219110d0f03081b040305151b03010b030403030b271f0b0d06061e0503040f0503072415050f01230c010b062b020d0c030b090106020a0209 66
    0x8040e0480e851300c078281da4807400401a020703500a0403000380a40b283c100036020381d07801c1300ea0b01404940c6655030940e0398852000d843c1600c1e08000180503224030611135022100000d0300c0c02c12401000720b8207601c1c8648146c000d50107490381100f641c1d140e0900e407601506076044960507510034080c01c03645000d0030070343d48603804e1480c4030008409119218a0040715080e1030006401a92043c50040032840203103150080070300c00a0110200540c50f540d0b0320448a5210004040e5020004501514155803103440a590042e02031062882041c650340d941c1031540d8808a02140c82c1d1500b02d003255204501101c092000c000d03511000c1c404040f684807010110110b5000b11813184500380254035071a403083d41c1980c00501c844000250005d4100d2003000903403c1a030100d0760075805c1c15803003056410920140d480341c07846030140503062043d080c1c3c80c2c0506d54140094058540c3d080c4690018030a040c0990402501d05480024442d601d06041c0015184140c05c1071003990300c81000b900050f15514841 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 171775089 1250 171773839 171773843
    0x180506030103020d02091005060a03150806040c090c020c040e01050a11250f08160b06010314010509091005070509180c03060111030405040903050327031605010906110301050306070219 81
    0x950450f6141680d00907d00f1580d00056001107002c80c6600701260540e12000580d001051780c2c0300350ba41e46520080c2d981c0303c2158000c2000391b1100d010031000f440c942000c24040c0083c015145d543c1052400701e011112804884429691542c0500c0a503140314412560640540700d00cad546010601c1803100707942e1500801100c0b81c3d0820480c000309026000044003441548040e11940c0c84c0c880514a0021040c01c0d54192101030200c40400c0c40356000b842015005c12881042d040c0582c0f0349410410120402031540c0403500499140700300c01c608030301c2983e1140c00361340c8845480c2c81c60b0405200c01d4804110754902040442010311210942901c25240d10074401d10b00300704408160350f0b015003980140d0f070005070400c1c1021510800c0580100245106803202540d051120314907900200000040c0b1001c0b031401e404c104401c904400e009207403804d201d8054400841c1416031565400700f180c00440b980340c40140080014003451500780000f6820401a100a1401013200f514041c01c4210316400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 171776339 1250 171775089 171775099
    0x2031602030a0204090f1703060f010c021c030f0f0212030a05040305041706061305040215030c0c031209070501050a020c010e180a0b0f19030f11030706180506030103020d02 76
    0x4400465904000100150f50302030424004424281b400584036210001c0803a9841440140c0f00e000380101002da030f1040d000140780c4c2031103205000c0196658040424266004501300c40c6c19042410b45120084605100346d8404007440c100c80e40081210121608800440d00807610780348070104414107a81d0820324610000801307498516080d946441594002d410b1805d48554851603c100410528421074041d1103a060310707610415440c00301c0d102110000e5104a0034145192200002e0001d50b60041c882507440c0d00d480d0545607032138915003001216241d1080700d20b082001c4240b00384a0312000742028200a810081844400794032a08000c40b094108006650395856550b0780c80c82c010309020394146c40c1c500301d04011402c00c01030a030301480d141c0100941541454036081c05080d101851010b00b16a001c00741c00d42d0748030000401148800c1d00c544100040241d03a59038280300903030060500e51038066071080c0365420903007040501e5200a1140e00144010800b50725042c1704d007640c50f0f50440e4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 171777589 1250 171776339 171776377
    0xc090a0b03060f03070b0301091109060a0f030f021b0f030406080a0f0618020304200102030a080a09050708030408060c0306090c0c010e0322050d12050d09020310090b06040902010203 80
    0x808030b079043c4240c46103d0b0b8903215404002420721003010055060364001d88050050003000c0b02c0ca9010ba2080140041e00b0030310410400007080d100f401500306030012860301041c4142600b4000c0f081e0b0300300d1502c2c4504d400340c04003003802e00e400030881142c100142d80c02031404c082c940080900000780042c415040181c81707600d130b404a200c03158002030152202081040d00844841400381c000d405c1240c0466061a81007400d0100c0d6120301d0101801d101c050340114905402c1c88012900e050024060310300311500e03180c056000074814400031000d00740c894002d60b122443c0c40c0c540c034a070201c09014138419410030000d110140e00ca641d12240c2c007001003e06599101e0840c40100d0040c9441e00c0d02600c0340c003010905040d44010b074000c50480b00850005448955140c00400c4a0000103490003010031101d060f1014005000d82e000d4020fa07036038004002068001500401d0800f4016404042c00c243d490000e103040080da8007034250490340c1903400300000106c90780040d50342d00c00c02081c528038800c041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 171778839 1250 171777589 171777601
    0xf09090c1e09010e0106030506030a11010f0c0f03020d0f03090f1101020f10050106030e010509100b03070b041e06230d0e07080a0b01050d03050d0b010c08120f0c090a0b03 75
    0x100024006481c0900b6000d40c1e50380d40d0f036110f012000213005500009041c540458514600010007144080c1c10414100c0640310140c01900c841511421120500c00d5941d00d41010031948030203030720603078001e401415061911003401450744804064110506180071616001b1590301303030140d200142d2142000f401a40f034000140d281142a003c01041c512407815060b070f50b41915040355040711050748052080d0328041c0700850907560100d0396200e140d071020b004c5201601041e00181748840000e02940c0321551038041d43c6080d80d219410441180903074007040d410104264a000008080c1c500d82a13001903507640b08507200000c01411100c01150201f108140c140160303208190158882c0100ca60142d0396001c3c03662141e06021040d40d803041c0c00ba00010302401c02000440c6010b500d955214a06130143c51000000c0c60310420f000d041001c50a1117400040c182001001d01c4042d1004810892418019800c00c4820051003503001e010107009004103030302d41c011f9080079906c001d03a0080d00c9035509 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 171780089 1250 171778839 171778879
    0x112060c0528020d03020f03060f0609150a121802010f0201150f0e0109110f0c0115090b0a090b0d0303180b10081002030c0f0d14090c0f09090c 63
    0x12016019000c0e00d1040342e0a500d9a81c4074400300e404158081d210481c2036000305404a01405040c0c40c1070000402c000f40061401441300b060248004200f00d00f8a5503400100303110004440f1601c40075400000d40300c00260300400c0300b036008042940c040c090045030761660182003071040030090601c90f030a80000c00c030398003e41003c2014210283c1d9150000ea44010203400d0482074880d03411801c03603c01c00030820b08224011240c91801d4002284e1504103082e61480b100ea012038002009075680710000e0b80d000c00c2d0301050300010b1003c8a4007054640801007006229800c541c44851a42c0c41c043c4040c0c074a0b00c5d00d01382c9180850300b50030f00045e5480300c041c3c41c1c03141c0e196420004005401c2107040140c0c20301c0003400c150540b000754003111180c289000030300702248410f590741c40cad00d480b050004e480345011740350003001c100700c0d807009c003086a0035029141000e2800650750b140440c2c01086600d10241440c0241e16400700040307515210600301044402c0e100c01200e00c04500964400a080d40c1524517 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 171781339 1250 171780089 171780097
    0x190501120e030d0b041d0c01111507030b01031a090c1605030a0c0b090610090f1d010e0d0c0c090513080307090302010801060509031002090a0504020f18090112060c05 73
    0x5141520703950b012640070080113040c0301c005588101c0c0b034074000f00d110046500d001c40710f03000c40500070003900c0110b600650f02c0e505802422501803003a0913142811020007138044c0d0080d000c07a14040f500c211355034000340550381d5140314100e001c0d45411024206c2c0d40c1d141c0589402c140340040155503400c00c602040c02403515828050042e00c0002801c800d8154840194bd60307050155140141070344500c00480e07200c40c4290344040c503410754484180005a01d44e4041c0f602e90001800010b080400d100390100e0060701c0068a0f002650b41e070b141031101506c00d1040c090305054a24001141c07601c0303030b500c020b94810f09000b080c80d0307030395100d0000f050046a00da801c8401c41d08101070382e403240752a6500425011a500080380083e00305400017408030f02440a4840c0c0000c0140a05031141000c00c0740c000940100310030070740c00248080c0002c1c13283c89070300c010030300140c840c0d20040e03a0b410010351006c80a5003940b00240034502403c01000103034100f510500809a0100b40490b00301d50a50089600e40a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 171782589 1250 171781339 171781361
    0x307090b0313060e0601030c05060307050702030f0c0108011406190201021e03150603010b31060201090b06060705070308030a021308010b04050c1303020405060303040902072019050112 81
    0x1000028001c84000b80322100040621440f801d00602039441d020a454403001e201c01410101d26a02c00c2c48071f440c1070380c003130360780080e03689004d44c20901150002032412103088061410345e002800060030550740100c140f409001d8510030000c00d00c44120101d01c1d41d00c070f48500c9882c810030054030205601d200b034044609040318042894840340b0706420340c200a0740b00f642d01110808030704e515011036040100c20f0700c0c104d8030b0001c040742c1403c416082c0343c2c1c550f8814031002502403018096100d4020a001c1c03e0001400040d80009100318041c500440f501d130380903119030311400f4240000800504006440804d0b03035482044e0540341d484000030300001e40100c3e079444446111400340806c07130150541c043e18a001c41145c05101584881c1000c00c428415030700c4248406a1910060003d400c040d000142c110303102808482c40e150380c404240040340c01a101c119144200c240801c91410354146250b003035904100c0e1850312107000b40340100d804109070f00c180b42c10b01800380000007440c20a07170f0000b0700c248 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 171783839 1250 171782589 171782609
    0x1012020c010e0d0f020106060f050d0e12070506010906030c060f0203121e15091b071209030c08030c030a080a0e070303020d0201231305030c0a0f0b2a030709 69
    0x450510900c80d10f40207900030250000b0718072105a607000303205010b048101c85103078031000100c81c3c003803104642540c001d41d481c58805445580241880344204101391407030480702801500c4070140c0ca000f03814168187d020381101d909055090011070040400b280403980e8500740f151640c0c049030400e90a500809171198a0101c02c00200405421001a91205d0801c0e02c56409403642e03502903030001e03001c031692007242c0240701200007504401603001e401310712120006c035aa081c4500c03651003286440750160b9410000d10f90220400400000c245000040c0031460042c6061541940e800742c0d4a0048000d8441003211038000314042c0c00c0d80740d202c1032005c41072409441c5165185d08000e07694088001030a0015868424071080c0b0326140c0b05400e001a5070a07d0000c1e80b9262810001c1e454607a450f8240c030710780020001801031081c2040170000c114410807801c070062070715040c10800060300500d47c100e02c24071182c03210141c0605040364850180000ba030991691200c4c58110342c1c004264100c41621 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 171785089 1250 171783839 171783851
    0x31209041d0105070801152c010c0501050103110306010b040e060405070306080d0f092c07021203040f030306060e18070e060706050901150e0712020d1109040b0108061012020c01 78
    0x2c1503100c005107040c7d48410b02c20156800014408842c2052008107010038208a0420031041001604090000d40c0051602ca001d81d07041c2c0d16401c2c2150404e0f170040320000c8142147c07074020b0a042c0881e03801880003010190405240200668048070b0050500b44180e43c0e90000509240c0294441c0c1d014002034400c942c0795480c80740c4098140d0300c00c1c00208000ca291110001a4080c0c041001c943c0100d00ca03c3c4c0042101080b01200d0170b80001415220943c081c0790040f450f42d0031001c0207980310304d00803148048000d415040203021500c081d0030000411044111003002e90700ca80305105074002e43c641c0021141d541d41e80c07080360900b01d01040caa40c0032200052101c103002c12504494021a4202c0003000710300307543c0c1d00c1d070701c204d860901c1500c01100030b2000080d19103004150340c21020304c074404c0141c60054402c0480c07080ba40c2c010351881012030302140c5500c450506224400f4030b40405c3c00e128001d42030a00000300c9401c541072001040198030f0301600b81d003503440c3c0c042d01c0d20090024000d2001e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 171786339 1250 171785089 171785101
    0x11404030c05030409020f0304030306090c0c3f03110307082202060a050405091f18060801060905070e19140d1406010e07020303010e010902031e04030518031209041d0105 75
    0x8c0d4002c1d60181c0c00a810f0140104203003a4601c142e45082d41c140d00c420143c50700c0c07a5100200300d425059804c0c030100d0030790306c0c50715450840d0244a413040304050795404d0070840c12201030115007038050b2000403071500f801004191900141c4040e042031288541520303981c40071041341050681248000c1d0864400320b556031020760440003030801e40b80102d0783e0414076135030f500449030500d0749447d844550103e400c104015030f174100100414481703285440852010b0701c43d4000760955126a0000008c1f80d84c070002c205903c1d40c8500d510080711001c03135108084940e003114904000d0468020b0100c0d165180d0b4060340f040d55281d052031000303507200c09024810b203400d94059440d16003d1043c0318200c2d02c00310020b95500d1000c811641a03da100b03883d018941d08240d480320094200401002d04400460180c10382d000110901c00c0c481c178070a90300d20350707250b0198100c0c04e030040d00039000a00070b90000302060824051a41a10703c516829180000c11b05a0030741042d030f820048003442c06840d46480c0074858 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 171787589 1250 171786339 171786367
    0xe01030f02090414090f010b100309050f0f100b0301050402010906050a0306050a080708060c03040803040f0f05030c070906060203090d02040b060f16230a1214040f031202011404030c0503040902 85
    0xc8580c0002c02500e101b90060060700c2d00f078450001c206a4006100c1d00309020f85400b9512208000b401007048130000c3c041c1025491070b0030034640c000c0300664494000d000e60743d900381c000c4c1d888641c0150300a018604080c0d002a0180d500f9020340810f22401165404000344280e101400410000f08440801584c6603030098541c1660300820200d401030f41e000840e4110b400f17080320b0080d40d101015600c3d42d0b0b0b840c0c40c1c1001c80b14543e1001c4503141200303280540403460800290458040c0440a04034903403074020003d04640d42da41c070071780070f5401c02d007d80201c2d0798a0b410340340d03580c0d501568040b50301c01c8100e001032501c1c4180340542e0403041020030303510608402168080c12452045041c1c800300c000b1014031038800c055030800305000e40c0c00000c0202c006402c40c84c4e80d90003c0058104221138501c110880e80858101c1e40151641c00f003140020000d00010748040f1260005500080008291403085103107002c4d40240081d082c08160149601045001c00456004003811138085403102480c03031380c0107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 171788839 1250 171787589 171787591
    0x3030509190605040e0a0f020a1806020d0c081e040f140603060904030c24150e040c051e04061d06030c06190c0605040302030c0d05030105010e01030f02090414 70
    0x54000e00a400070016260041e2085400740c4005855450801c1d142c01400021804028039080c04181c9518045031201c1c95800640580c1c0055122a9400207102001100d40e0403213034490411540400d0000400c0c80d04680342022003500b1140c01603607101414514040e9002104c85008080000507001810080a0341440c040d203803150314603031000380145c00b0048a03000070f40715a80d01040800101d800a8000d02c3e0416000b1700c02e24102104081c0e108045070008820282503001d03940300e0525402022080780d83d28040c007014045141181805d45a240310200c6500501d03001300322018003d40031101c680b5954103003040080c8103005540c1c45110001e211181e01ca031b03e058440d01c24012409519011642600701000034224504150700210700c2047e190025114005001d04212000301090701c600a00b842070f0f000e60001e44c0e41d1a150b42c0b210346800d07824440182080820310060100d682d1024242c0c940000c00d11700803170907100c1000340310700a21440d4072845c0d1103468101001501c100342d036019 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 171790089 1250 171788839 171788857
    0xc06030a09120f020304050d03020114010906150c11010f0917070e070c050a08030a020d0203010b041e030c0e060a170a060b180a020304050c0d060905060610020303180115030305 78
    0x401c0d491001100f07503020491a0b400c4000f42c0c1042c042403005092a28001e07100d14080e20002c04c030400c4800710742c003410380e084c1c100f82c00c07035502c0d20030a201928100050144407c1c2c94034048030600d40700d8a6000c011080048114100080414251181d906c42e490240203805950303034407400d421076401c81541d20042e40c480c0c42c4580c06207a0004084a020ba6401c0c45001d801c48050b0160154954441042d139200414403401c1603424071907031225a445101940c041d14403410b040e0354032814803400121480101c100071000d044410b8050000070503d00c1c4041c00c869261041c1041a100c020010310b440d00305800811007030b4501c29458511940004040b603240f80038000401c208620030080c024106000907005580701e62440100d000c0151650095074400d02030b4081d00d1039030403000b00183c0403c413009015245207071141044028004180081500407004444812654038411400b0f5202e0000900340c1840c01d4040040c0d04601a00303401011450303001c101105000c0c0c1d12840c0242c41e58210342c1e05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 171791339 1250 171790089 171790103
    0x20109050f090a0c03061a070506010e06130207020301142401050a020d1d06190306050a050d03030c0c051204080f010605030304030213060306020301060509030c0907200c06030a09 79
    0x25140c10404041c1ca024000540003034615510351882e14060403402e00c0740c4040664402c0f00040403580400084c1c1d15080c003101c1243e0700d03619814401d10f820300c180c000403140c01040080c0001030383c0b80303015458012000640580c554a403400005e00510405030721000038550f8104102e440800318181e1840c40701d00c100c4050407610300301c1c011102401020044000360303000e40d480700c1c51203020b80b442045850f50140c4480c5580c070094041583c0760000c91003040700b108107011080c81c0b60340500130080a84810340340700c800c80f071408000a2155210400c040c050580d07079031005000741d20840401c045c1640040031240004030100c0307655000c1c2d02512030614140100000c010405034180104012030744000c0c015800d05003140c08015002c100e08480c1402c00703599081c00000142c032400514001c02d0a40c581580301c08544060508000c00904290300c40c0308480100b000c10b0360800c5c0c0100040c490212448101450a91505e29001d404500b25601140110400518a0040c2c00080d500c034400c400d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 171792589 1250 171791339 171791357
    0xa0f05102a0c020901060e0a0b0f0a020d030c0801030602030612120301140306060901061404090c021f090f080f07050102030c0903070f080303040f06060b0d090201091e0e04081b0105040201 83
    0x1c421290a02d00030b4000394010b0f0300f41d00402c84248280c940500320100108424100f990b40e0a2105c0311f0752010124480da00710109000c07407195014030031010f6251440c05d0034040564400d200820711001400010035503940030010607002c1e144d499040c18604440011105a0860345d103c0b86d07070325082441103070f6503008070101c1a011800c0c04240d85006d440d018113400410b03428441c06031440015181103200b803540074400040ca4001502030f0080c07604854020b065410302d150000c1d2000300d0030301400305415080140c0807001810b550b514000d0719400c00c0c0c0e03c43c0c80c1ca11307042c80981140b0503000c019050703600100901c1841d04a1b0780051400d0038044003110307501c80e83c0b6080390016401c14800c565094009000280103d00300c120400c00f164481e5200181842e200c207000031107a08480c900d208820f59035a0148110350b0008d040c200542a80502515101102501203140d2100c5018595540b004000450200480301d416110b0101807200400e25030030b40d4480e0503000700b07012503040c1d0003d881c1c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 171793839 1250 171792589 171792671
    0x30703021501090b153601120c020606040c020c030d2006010501090b07020112050403050306040c05033c0c0d0b0406260a120c060b04020406020a0f0510 67
    0x48500d695010000c0c080b16034480b981705450350070703800c289070228880d80c03d9034a903110812407006018214545600c1002c3d0f03078903034600042c0012949032002014034503003c05900981e800044040d400802142c000c01c0042415004a0401925a003a10f41520941a40541264000c11009910440d01d403800c00d2500000800c55a03416081c81458007180c0301e2034045c40780d041000010700c2c5041c018103203005014903001c4904d0444008840c15000118007005201070751038940115070040400380381990440c28404048028064188261004103155440820000c0761480d4254010180c28000041c54500780641700b6060b40724031403000d0410302e402ca150446107485e00c0740e002540c0c0c1000b6013241c4404140c1d41c01e0304980c4091011a00d9100d283c114500162414031722481c6135240d9500c0c03942405030740c0f80100030f072400040910b2155006000611400b0340c0000c2441140d0340001518000401038208603003001c1d03902e90904161414030744040304200501001418a820003c035105000b1024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 171795089 1250 171793839 171793841
    0xc0b1806071106070804030c090605030f011b120e1506010908070b030a020304080c0a0501020901030e01090506060607150f091505040f060506010e0d0c03030224041b050303070302150109 82
    0x4060010845041c03540244081c0c14540084d04015220f24501403402d5200e031106881c3c01c14507400f80144540301c81092105060a00424114a550384001c0c0f02105081580d10200c00b00405003004104c07001e806d2000442d90741d00a803400c0f68001e0180d4040c6541c4c0c0c29098031000e41146c4040c0411038089000903118000a0884121040141c202c9e055440703101c00c0340c029510160003070350018001e000c1440c00c8103041c440300c0c0d61148100001a0b440c80280009820b80d4800b600c5851664508030b0340f0000f29401045640e07020303408581841d03440c00285001c16003442e00301c07040000146440400012454107500c0308500302c0c0100000d808813030b070381e01d9a44141c07002107400602c8505c80b13810380d04c005903a580205030410300504180c0360340d0300040041814007401c54020380d62140c0c659020402c0c16010f01403850007030395a0320040c1c1c113040c40c010380c00000b00c0043c10041c41c02070148641840008460406405880002e0903030b40c2c1c468040c10000c0d510380404100103502c01c040800043c0300241 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 171796339 1250 171795089 171795097
    0x327010801060804030813030e0315040303050c0c060a0e032104020a090c05181203071a0901060302150304020f0d080c070b0a0210020706021b0d030f18020d050a0c0b1806 75
    0x200d5510181c0c51f95540818408401000b1021803d1040980141095690030f2005411548400da80300740c0926103420001d00b520409083c00503160801c120030041c40401281541d40319412400202c0e0004821081501d58400c0c1e0101c001c2d502490302d14051b01212440031140101e000304d0702d184109444111150407107109042000100f04100401c3c0402c0c0c030076502d0586a404000c0507640481c40014003241558400b0b0760442d001c0002d13864100040c005460050b800100140003008110300b1079021a150344000c01c03d0454142001c000242103503100c2004407028000982801c00801d0b0f5440c0100315a04501c00300c4059001d000b102081d00401c19041d900e440009034002e19050300c18407600e80095007e101c080d185c440d000c201d4500071003188040803000700400310040030740392403a0500070308403401d4400020f1308070700f4107040703044030007000300c10510b86d40d0103d40340031f1000440d2824614010420900812889210200007619401d550103030064902100d480b104030175080b0304102d9a441 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 171797589 1250 171796339 171796343
    0xa050a02040f05131103270d050406050f0403020307180c1707051e07030c020102120711090604020c0f06100e250c170a2d110327010801060804 63
    0x5030b004402c224910340b8070900c0c8116503034000c2c002021040030182d040558812203d400100c0e603440c203050010031058030280148a90400540744048031110003c001e841140308460400502203091101061210102d900641d030050450310740c41e5903100508a403031606510030a41d50b14090440090a00455450300051842401c160107a40d45d50020f1781e01c1e8200c90030f0880d164942c1407130504081110002421424000d031500340d0b000045200082c60465600c8050980c514240311560020700039000707500d130300300b0111000c0d140750b0740c0d500c0818024050325441c00c40c0341c401c0c40100000c00801050a50162000c114143d205c0e51300c0380400c040d000015681c4980a52a503042c64109072010382d48c2c0c8011124610341203001c04001e40340d210001605c0840f540801d800010040c17440364200092880c4d4114200313a0a43d031080e2b40125860040c104810141031200301c07100e0240c04a030510480c2e0709207a08604040003e00804261403100290000c00307804a015100081001c5000e0303149144229 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 171798839 1250 171797589 171797609
    0x15030b0405010b0c0d0f020109050105010e040b160203252f04020c03030a02130305070807080705010e01050d090321050103020f0603101406070206040b1206010906091e08060f0a050a0204 82
    0x2017101c40c001c07a141141540341030b0441d5603410300c030303000a40280641d90003007100d200090a0f9040074140255401009094039281ea8401e0810007459900131040c1c4690540d80058a90781d840841070405e407040c5904001003080070076480345142d103a001c081c8041d554081c0f0400c514000250340501c0124440c0c2c030701c03150081d402407002940c00281c98000b41f1290f0b040403010312500b50780b0360707500c4d10f000c001c0d03000844117800965092182c01400c0010f40010070003481c082d00c441411100191440c45041900340c0d0b21341d210310164051500414001d4505400c418401c8611420203072481d0050100b03000491145000d61341c40d0136a41b074410162405140c88000d00c000041ca030a1162046505107194140c103d802840b140e00583c1d188000b074002030801c3c0c8201341d955580010034603c5400002d0503103041c006020310a016895101041e102039035000c0e46c01c55011000300ca4203800260040e0b200b202d032445014104441055800d02c2140a08203412080c840f0b0303254802d01c401030380035074080e0352240 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 171800089 1250 171798839 171798853
    0x20c030120070c12121211030408070c08061303030f06050a0b070507050402070c0e07093c09020a0206100506090603071101050702210c0705040203040c15030b0405010b0c 75
    0x600514801000b240b0320031151400e5080e030b40c2d0304040141848010a442024035174100c0c02c0c1c03041d00041d54111781003200c1781c00c00842d0502d00003048180809800584810000f0442ca820000d04003180d0019084072801c8071060300d0030080313803154500105003c0b40080c0c20503100f4444824140101010390b00c0081450491038184004282240c101c3e95094078a48503040340019075803541d03c02490114010003c2d01c880b503082100c4031413a8080545030300208546418104103921201d030742644a0b04c10f55440d40c0380c10030700400510350070481010340d01c44d0802104c40000e0b4003440ea8020070f000720540e000d40b0800c1d600c24032048030414003481076075008041002002c0403890036500a41d40100713542031250b0a602c5899100f42122801c464150159205100c110210a04480502000e130350358250309180900b01c1035801e4990010381b0070640501d40103c0030804000344125840c018007559549a155507110000040141c80c010424030301440c501000400c11240a00c101c40641a088004001e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 171801339 1250 171800089 171800141
    0xe030d060f08030a18030b250509150a09180f050105100909020d020f030f0103020406080a0807060911031b0108061c0b1f030606080105061008070806010c21020c0301 73
    0x110b41c002c1000c500d1412071001c004400600d00c0f81f05a402800000d28400942055240103039030071807151055024050140305a041941e504180311800d0158580e02d0b540b5952221025100d0460980284c010901544100140c81c9904d0b0f01c0300140040c0c50307031f051007da6604c0040c07243c5142d07038140400010700e00203000d00040205400800380320340446401458000310060404242e0020b0f521403901480031401002036241902681d00600038000240080a42c10380d40c4110300d1090f271400426480d10381400301c0502500d8807011001220107025030350048a02d02095400903075030802203000c16007000c00b00340305081404642c0d1405640c0e005040d40759605403140c400d0714200030310140341d88400c41c00d000c100e484000341520007544620750100e503c42c01c08640900b07617080104441d001d448441060608103600c0348540360003411500f00180f503030304c030b4100495104c0a40c000160410000c03207100d8060720303181b0b258550480102da003601c0c60008858101070a980b0390800b8504d41344d070000380d8081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 171802589 1250 171801339 171801347
    0x206010b030c041212030606141803070504112502091f030606090c0e06030c09010c030e09040f1209080c21010603060b150406080703020901020a02040e030d060f08030a 74
    0x1402c1407060b0300e0141015640c0e458201182c5200f0012100800395542000300642c050040c035020741204e00b041880d400344d51645820a004221000006405c00548030103039850a200f001d0160102a2045c414070250141c0e0350b03120351200030046048080582c000c00c00c406d05104204810398010204407107a150070342c4030b0380306c10340842a0000c1e81d140c851002000031510701c07860004048500001ca00e030401020081c00c0700486054460158400700200b000c3d11540390b0468030002400d003007031501380d2201d040846100c0003042c00ea580042229040c00207100e10442c0c115012841a00502c800940442080740c0a02242c0b240201942c00011700c01031358902030030f03284101301800600c800340c00e001103a074500703480c0c05510a8604550f105c0090842c0e00f000540300d100d03003118000a6107050b00c0c0240080510303174003c08510400d03034007055047c0305a2013400000101c5030000e0043c0820b5054521140c1c580e0b00009410407034504d44080041e010101c1141c14003140c034224080c50034401b8400040d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 171803839 1250 171802589 171802591
    0xa0e040b0408180a030308011e0506040905130c030b01090507030207051b1c080315010c080904020d0b0d05070e0901090308010512070308041710050402033a030504061b0206010b03 79
    0x442e01c0d01c8510031803e054442580100040d4000e60790b81c0c42c035500d0441c00f1148601d05d0300100319aa800d4103414012500c9070400c4070102c03010742c800022039a542c01c0d914400d80c03041c19001005181c02c0c1d40000144441000e245060301c268030390030030040d200c2d100c0c150200d10533400c000b441030700102061541c0380d554024403900100003410300d50844440c0036a000071801030000c1100c0504011092001394150301c0c0908110000070b00b848a1030040b152a01c010b180112100a8440d03a00081c440701291700d550000105007001a00702d21050071280340150716000240a4056220225800550101c505000b0841e440da01a190b0341c09030b90a140178005550400e01d8103101c1442541000800200b07600010402031080c0000038441481000201e401d100132120700710301e503e003080d085c0005a40c0c0810750031519483c00314030305400902c0314801103030710078940c1104186000c20761a0868540e01900f010b845244900301c2000100d410158403880258088234240c0180e10100043c403c0452030b90041d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 171805089 1250 171803839 171803857
    0x309090b01200f0f060a1121061c03110105060109050f040b060c1e060105191401021c09060305090115060807050415200c1315050d080301050a0e040b0408 68
    0x254210426510150303150001150308101e056000c0c008000d01b0401074420020441c04220040c1d14084821040f5003407041e00e5a6045107415001000c00c41f1a81d030001d60104a021032821000c00a203103007400743c0000ca81c0111000c0c503509150000c2d1007584250195002e0b944024607212070b00a008040c4001420103501007600000204184c411400081290541e4404001607006403c16509905428010181d014a01a802181c0380e0030200d01c0003d102015100410f041c000802a180b00403442c00f81080c8140d190701c400d54080380d18065021000d4070583d940c1d51420300054070340e401b04a00700e0701c9107002d11503000d1242e00c0038402503110302a01074100c015454403c0c10503480b40c0851400c043c0c2050380c0800f00b14000c1c05440084003128400d00b403000ca48000e00480e00c00c1c000070400c240136019420300403a6944c1140708150942403200e0000d01000307445002074010915024034603034402e009041c03141058101c006000f007600781050f40701e00e0307000c075059111341c803a580c403c20107030044240 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 171806339 1250 171805089 171805093
    0x20d02040515071a04020904030c0201050d050c0a1407050c0d14010203070804020f09040317330f0306070905010507080f0313060501050d02150d1e0204030309090b0120 74
    0x78259075600d800400e402c545010a90350342a162030030309046812141100b0114841034104400b50351250f2026900540600f0301050b180f11610040b541840b84124a4011074584420301c407030305404802520150302c0c82d03114020014032102d0001da450051000040c2a03038092451040c440c140624000a10351140e500d910441c3d054100d0582640c0044030010002080c64040005502d40415042c12000381038a807048581800c0d20004e02c00f85008015503c0d9440b84030104130000f2408230039240f8080e924142c0d40024150403105002d08403201c00c000d200c0d81035440814060714000c1403160081000752626101c1c289850010748854100010541e4074160601c90160846d10520045228101c1d085100c001c0c1e1125250a070101c58041e00094041d8104174401ca00584401c0c8444a000b00002c20850b103400f903034007d460281a00c550441d00302d400d050742a60071040b540e0003800980780309848555105480348184405c4401c80c6611500054101021034103616684a042c007000841e441 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 171807589 1250 171806339 171806347
    0x3080d021308070306020702040b1f0305180712051203070f080402061b0102090a08060705070201081003050f0d0305240d02040b06130509060d0506340c0b13020310020d02 75
    0x2d82241000ea4544c41a00e699400041e4001146080d10842030a010200c1d01e48120a0002c40324004081e2003c4003a0185941c0318040385189d455102003d10003119030f4221040d86441c0c030011111100348080c00c60f414407400342004c010b1180303982500c0c800d0341190b44440341c8071a02c40c001c070303100d040240050742c108400300411344881041208115501c2075040000d40c0d1100c140c818003480404550008615402020900c24000c3d400303001c4078149a02442c10047c5074407030620b542240d05595100802d0741c030401030f0348010139401181d100d600140da5281004142c0d20045145454502c2089118444074070714600601d030701c0e08d540d81500003400680002803c1c0301c0800440d601e0f601598840301c110032580300030003840c07070104030a55002e1002c3d5401c41c1401060b40c0c90070390f50003020340864105500d125425108040180720b10440301c8001c41c081000c0152a48003030840d06160701d040d06d072101d1200000fa400c5c6c41e01d03c003220042c0c0e4050018489581850041c90007504038000d00e48a06400304 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 171808839 1250 171807589 171807599
    0xa08040311060c04170a080d2d050708090c10261008011503050601030b180109030e0111010b0a03120905060309010c0206091603060209060d02070b010602060108030403080d0213 78
    0x1403003840c29084250341d131414010171038801100d0582e6500d8560005001000190f440c9040e1103104007010804602449281010000700003407030750021034002c1201155085034542d410043c0034154680300c1d10083d4403000400c980390b03895082100d421486070100b210600d4442e111004045c252240048410001b4031141c4d03123030020a075440e0014407481182400b21000a02c40d441007001414649169a40fa5a98140d00d40070140f2018041e004e483c0001401d00c00781500c2d0004540c0800000c103c0391026160151041c05103001c41d50014400048c50038a240051241d01d41d8104000d024011492030346d91140c074804190407131841004211080015141c036a013003d94001c1d600e40f000030615066584000385060310007040016150700c5121001d03c0160a0b000c00001c1e65005600582e690300c50102161442c801c0450b0885901c0c400a0804c040c0142100401d040c0c0302a9820388030a80d07038072280503075640218040608004d400300680344c203008650b4024105503100e03403000d0450a07030300c2e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 171810089 1250 171808839 171808843
    0x708031b0c01091401140115021203040b0a0b060405132403151a010815030c18040c0b0c100207060b0d080d06061e0503090109020405091b0d080a08040311 68
    0x20224203007a40c0d180c03000c803410032001410329980136103960020402c006520407089526a010721032900913203040703070780e000105200f03010785082842c10701d00c05a901e080c28680700c42c80100468480744c481c0e1504203059140e01d001401c840c111480102140c10294801604d4402401a003d041710402c0d46050040094510343d80c285000f540112081075510f4001e8401c8410350342005110342050b040101d0703100c0b1aa8110070395030780202d00e07940c0c2e54011501000120b4a007890f8800141d503c0707803511268004001404030744522031446103019120b903d503203d100d03051a00445140201c25004064403959508041c1d001c0c010542c0107884c0410f1004160011400c5004285d0341511803c07000140c03007010180c40d005210040400d880d201e0507844110441e0a402418a03580004010000004c1460040b09400041c80c040c0c0050080281c0e0809003d40c0b559444140c1c41d5010101c1400b6400003a468000b0110381030541008140c1d2410400813070445640300000d004405010703031001b0400e0075580c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 171811339 1250 171810089 171810097
    0xa031515050903011b0912290601020d0905100e060d0c0e09090d200f011104060908030f03011221020105040204051503070e0a06030816260708031b 65
    0x4a4480c40c2d5a444403030705240c2903a001081c0c0c3c0d200c070304010804500c803560200070441184e01d000308000101802e450028448030440000c80310b10180400f40345100808040c20500460003602154003c0e2890b0740141c80d8001e0030700c1110340c8441c0d80110001c20a0090700e07607080910004002e03178134100a1218100448801a40f41400a046070710490103e0230b0041540d600703c0b102d85c1c01400985000719000740401c401b03411403003c80680c070116620b40761040080202c5408004024000705200e0665004150403510030440096000000000c01c0c0c100441100c1146450400703142c6140e080c0701c845452840340300b00c2158451544000c00790b00d005080b60100e00d0103003d80c000b14680c00c15004020076900050f0803040c0e50b1410600129840c0d03400900360301120300c164840004ca603180800400201a140c0c00542038440002d12402605003107150891014031950149240c9200c2000d8850356400a44245054000c204405d8020814403405190b101e20795a2020784e4003000e40d4800c41403500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 171812589 1250 171811339 171811379
    0xc0405030a0804060305090303010e0406110d090f0b010f0f15020f150109060b03160e01030b030d021e0a020a090f1d0c010201051605160c170f0601050607080a0315 72
    0x42c042001d000603581405807507000a80d4800450440d410621081c03e0b20201510080c89540c1ea007405a03002c008030000d0780c3c20044801030405c609145030501b10608820154101c030110050030012441e1450b9924645c10344074001e01c0b0b00ea120342000c1c05403160306102d10144041d8491514140002882005407403003540480741407031155490300c0007600070340d801500118580c481c14401c10040e080c4bc0070071707110041058580a01c5600c2031a005a0060041c03100294250040701f20a140540e000100012503005517074041ba0100c0090001949562010791300a5100108030010005581e16411040c20703403c1d40d0800040e04440120210640801c2a2460015130000c1080d02440d40e028482c2a620400301e48221483c401c001130b0007085449007030f03144c40110074001d00340c0c8180328204540c2c1c8050108000c0e0301503488200034105079103122000755a0301c1ca2150303000100300d50400c04143ca000c151302040607820003820301001d46c00707050540030140110741c0003140000c0d05401600e40c009528 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 171813839 1250 171812589 171812603
    0x30102221701020403020d06021c0c02010e0f060601020303190b03010c090e06090114060729010503120f040e090a05010c18142b0501090318050405070909050c0405030a 74
    0x64a48420940001c0381e401e204a1907900c18001040076840e04094800b004d0f91043c401a030355042036220300c106240c2d100003242442c0c0351041281410b5015400720344011441402c41d40054000e40c07009075928022540c9074010f07007080c40800c884440c000301e00c900d84400e01a0214402038441c01003400c4817054140c040c000b40b03001c442048074101d880c11043e0001010344080300c0b15170401c0d01c0c40341001c039214a62402030000103a40c0050007500400000040a80ca1000b07a51041444002424007003e01809200380107040d03483d4605408030b405c6965407842d0008a509217031802600308030b00c80f00140401000e001e2401d201c000a8003c4c8101d101100594446000380301441c000c9458a4445d500300d01c0460688e4507100302c441c2c3c0c4040c1041109400d0050052001d4403100548002e290501d000804540c04e044500c001c040e0420003048440d03000000c000545560b40040009981c010745210011a00d81c0fa414070984206420807688521304060030740c505580d58011a2404030810030507905a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 171815089 1250 171813839 171813907
    0x2070e07090e0f07080106050c01020c0106030c1409010312030c0e10020610050307180c020c1c0201020606060f03040b0403090f060815030127110a090c182102030102 73
    0x40c10381d103441c083d040031612009000f54a00702d08044d0400c039041c01a0402d0000118200070205000d4044035851250700c0020701c0815605d10748500b402580c1c3c010b806e81d500b10300354600fa80b81803400055040b80d0b00441c0260307280100150a90044c4507668a020401044c0e0016100d283c1755000d1182054040b5402000c281c5080304c0c104d0444411508402d02c00e4000c0003040040307864604089101d200c0d0760074001000b05003100180e1070503242203101e83e00044010500c02c3c0d21042c84113041e60890003a0207442c403940c2c500041258510450580c900505420700205012a01d4444006c1c0e00a2090501c4084503840d042a2424107400d503020307400140440b42040040403142c3da4000c503165081d0000d200f5507461581003820000c495a001203200b41d200c240606003e40500600c0c2c00b03640141c501c05019440702e0303010001c0c09440030f014000c60348c0e541201d40680f441d840c1c600e0494101070740105c0703254000801109502203030b0704141c0e41907400b130040d02c40c85521800c0c40c1048618400e2001d01e1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 171816339 1250 171815089 171815099
    0x19050a0b1503091606023708040305010e060f0a0209010e06030a0b040b0904020108041e0c062f0c010c11180103020111011a0d02130618060905130803040302070e0709 73
    0x240013802d00b400030581e00c8071441002003940000d03d0410b4107164002607640074030240c502d42910b2042400c2c1d889030000f210045024008244001c0c01500c1c020002400b0f05408c910b0002c0d61402c00703451280381e41051000240b08103091394090f0400c0b060500d080e16201c410400001c11541040e035920348007a80d01c050041181c5014400c60307240940513104000300c2d1800e42c0019040381c0c00100081c0c900300000c0e00f0310145003080d0f11802e240c5540240414961902c86c00000d00014080e410b010080116454004850844016174841c0d1091400140300c2d81350700200446031800004000c0300e440c030445021340602e6640081c48020110780c112851003d602d140001415940100422400c503403502c80b509030818149906c0301d0340e5210035035400620700700078804526002520b90221409516050000c642d481c0c0540040f00445a240004e02400b0b07111500e0784c04603402502c1500c101507450389207200144000c40078542c081d000340143e075452035595210317846c07424007100c0f1580028850001409 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 171817589 1250 171816339 171816343
    0xf020c0409060b0f01110309091b03010303091406070c05040f0f090609032304050d030905030109060b0a0f06050d0b060c0604121403012105160902030603120319050a0b150309 77
    0x20b04c0c0c1100740f03070460300c44200503400354a0340702d1f49841e90f01403072480000924038540d200c181c0401c003030050000e070703646c0d0b80d24200201b40d036000b4020700c144a074401d80c070300c501464980142c650703554100e00c040c0403580c030f803008120080c11191005005140c9642903c86035145500c140b184d024020400484c1da0b8805150041c8501c0d19a181d116500300f0012031005595803820669065540554511618a81c0d5041c1500c2104d1b29501490385582071014400821007070350401820b1840a80d54511000d4454802c14495403c03070151400007139090091040e603a01d5070b0090b0951100c05041c0900c1e1a40c1c00d01d0450404104032425a0400d0b0090030103400d55500284460000c8001d81000d811941031441c480340849101140e66480440c080302401449014007a000b00c00350f404201020700d03039407140d101010390400c03aa902c0c402d0140d455945181c0c1c00150840c1d1007032886070114400b0603d6082500c1c001c010151280c84440d5840c42400b20035110f03002500380d02c4c0314009481e5101e1504a840714 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 171818839 1250 171817589 171817609
    0x6090e0606040204060c11030a0b04120806030606060708031008070b0a0801050603040804120204110301170f0604030f0c05031213060f060b030601120e01140f07030203090309010f020c0409060b 85
    0x503000b9031041100700070b25503102e005504511303445500c00400300c3d84880000c0c1f60034840b10380584003000050a00041150a0311100c41d50009900d80c05001c0e500d640c109038603072008035207943c0c2010080241d03800040b41c030b00c01140e2107210320002c0e40d0704689614100703140200c00d80040135210b40000340709400541011100380140360880b4200c1c0365107000da0710101c560182d840b440d140d0150203a509804c40d501e0f070700600001c400042c01c0e161a50b83d50007034100610000802002c0e1801041104000414041b544502c541c0e0507840b001041041281c080b42c41d11210481910140010f00a1000d0704040d4501c1501404005c0c68030b12000c800c6051003800c0b52604030a0208061a00004101d801c044500350380d40040b090820b6083d100756040705801070080480c1c2c2c21203651030b042c00c0c2c520344629410740070300409846241c003541f69110314040c0c1c1244001c1d100042c440d030089c00200f41a40c403504002d81140901e10540f00c640c040100400c0507209150000c50381035441e810031044c5800e0002c014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 171820089 1250 171818839 171818851
    0x17060f0a05090c151608090103060e040803060d0c091401180207030806061303080f03160908190807140a11030304060804151e0212010e010308030f090f0106090e06 72
    0x1040356080c5041020b90360816050f10078025510400f208072074901c1182924941c2c01ca10b529819030851502c1d20902c1ca500181c91180440e14003100458108a681c013503d200310351040300030345141c41e03200400404440340401150510454000461000e044d0f01409054003644a201042941080c401e43d5002c0c6110710340c183d480b0310600454001ca6481001950409002e0f1041d81d81c1d0750300149810743c05681074001804004002070b00c010a0046080114410500c0e84145c400141040d48100e030740560520480156034004044e0408081044151501c03041c894404146040762964030309510804021800c44070f41c122642440a00c02c141c0f14940b0440d10480207985002c3c144000a08078000280014001c180e1901e2002d41c0444154030010700c0c00030180601c0300c10030064102c0d101a40c80052260b803408608000012540300c56903015050b2544196000e0550395440c1c1a058840c800426068042c030a10300d6011280380c00384603003006001c4d510004100303119052084c510300754028203d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 171821339 1250 171820089 171820091
    0x50106080d02070812072102030d1109040c03050f0403120b0405090a0c050406180b04060306020301081605040902131a0a0807081c021e030f0406091806060f1817060f0a 74
    0x1000c0c0005850341c101e240111a401f00600413281030280c12451030080000c0b40c40c0c89450420300d4800c0c4255180941551642102c00f0f1010a40401e0101d0a944003502c54504144030f26010500007402001044140c3c1044480024a505100c00080c141c4106580004940d000601c0c110140001e40c403401c0080c1c0b03001d51301070016510f44000d01050845641ea080d11040d40ca01c40c0e40040e80e50740c2c000078011900880255200c0d42c4a9451a440d07401d120200c503002c600e60040019503092600510080079002070042e800e5501c041c1000c0d0240c0701000c004480301c003070321042400390360304c400780c0d50090803056006056441c00c0ca4a018502107172a0104503028100120401d88554005500b0403a0f8141c0ea03149008002061036040c17540c0038003100e030880c2903404107000c60451fa009120000300c1c0e580d042d03440b81280d101311121040315a40d0150400090010790f070714450718040c2845081d031800351400c0000e0241e440c1c1d09155003002c0590010110f0b0084018051505800000c40741c0245030404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 171822589 1250 171821339 171821347
    0x2040507030e0303071409030604060e0d0e030d030b01200105010503010c021504030f05271302031509190e010e07080715030c0e04020d0c080c090d02040207050106080d02070812 78
    0x14500760f40e07010040c0390204125100c40f0300941d9080380019150382c01c00150444069040c10b18205001c0c0c40d42624444045c4680c0b44c20780603d501c10b0003c8280f100703001d030240ca203030012541c00b10040e040400103507052000034139070b02500c451840740c01e2a42442220000516504180c209400d41c1c0040c050802154443d5848051980401c043c958101f0b5040c1490b411052138020305503010301400c294a4041e4607400e140c180800002c1c1200c0782c00040c1110711010204045001c00c0c105d0009890200760407158407401741c0e06040915006030022828044040042e1004200e00103503044001c0203112a511000014400041080344001070030400000d000d02500380b2142d07040609a00340b60404040d2241680440e0501805240c01100340c00340065640e040030702e69440c0500400c600f0100001c1c84080010140c10b035070300c02da54104100512104012565808020283d088100142c9095507a80400650a001009464580300b2540c002e0f046240c90544014103021607403400e8958240d00300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 171823839 1250 171822589 171822611
    0x9080105010b090618011701080c2103120411060d1d010204030206030a020d0b0406080c030d02070605091e0301181208010302010804030302071b0605041406131203050708070c030204050703 83
    0x102601e05c13614111081100e11700c81900101c61451222451310042c107504000490070800200b071115912800307a40b0048404280120340e142002c1c40c044621084d0420b001c0e82a1810040c4049900140601d00e5010018465000281d0700da0000031801c002c84d64405842d0550b030102621449190101402181482d2070341d00401c403a40700081c0580c001a50000d009000a08558030810070200042d00410101d82c46401096448400d14406032191044e002c90440280c0300040300f07010f0f24899500c06003810b143c0c00030b0088101c0000090030900f00e02d01c003c64001e071030900c90f008841003400d400d82e01014443c1002685821000081020004280014805030341c00450098000c4d5046c0f500680e10b25240c00c0c00203020700c44507410305600350003c00c00070302c269105001e841625846807a90301864025410046c403449410015a0b8079896080200001181c1d1104100510f010f428641d1414186594a5903561301440e400c40e001e040c3d2203400d20641c240703031060341c3c2c3c0807401c1e0404010f03140d401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 171825089 1250 171823839 171823849
    0x1020a02070b0f2a030d02040602013b0304030b13030f020a030503040206250b100909020a032607080a0809060420030a02122107170a05160309080105010b09 69
    0x44000c540e00b884218048465110041441c1a5110146019070b9200c42c03500707514001039070091240384010340c01c044412090400c1100810510100042c00c4165400c2078101d003140f00d033040040030f076140018440040420f94140f0b846202e9801c2d0045c4801102c039514000c4c1440001c1c206540441d0300244100d0006608501126000ba40407218240c451405403980d40f0014068407210201c1e1440e6079400b0204102c6110090149000c054464442511200d1034400c44002510183d17000340180c1d0108046803060001c114082d50846000d0186e042e0309501801d03503030080204891000c1d0000342003e10a81c89a0429000300604001c2c01090405803100301290311000c91004582d01100443c00032a5030402008840550180031640c4548004201303644948529021a86071007811140403501c800c40340480341805c0e400707407903291400048075600403a03030042030b294818098204440345011110b010032a400c00c1c82a07540b91020350030003000c5400d44806911007148100c0a0103010019075035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 171826339 1250 171825089 171825097
    0x90f07020609062a0702060c01090b0a0e120304020a050a06020c03061e16021f060905010812070305030604140f0a0c140901080a02160507090c05032401020c0306010801020a02070b0f 80
    0x13020002c400303001040540c0d01c0c10702c62104020340c08400040c0e003d08509064010072030460041d07075640802c0d690788403d03d042c0d48250801140703e0f0044d0160301000940000915001030016008420740d549500210b08403211075044000903911200d124122480c1c1005015030006030070207082480303014150b22036030400300034000200760094440028840c03403080110443c105c2042e0700000051001095000003040140038001102e0f08001c00480c0c0610009604000d072070071105d2b96450402a9101181c40d60000343c50658030940301d00c5040020800c4224107800380b00d03140304020603810641d403004211070b130049542080c0171404841d2100140441c0568503500c10a080003c0c0640d28810f0030320080c8a02c3c030301040c0d100c0c1e180c1c81780001c0c490300041281c2500d80c115010090b03800d00d080141c4282c0002c44503203a8249940303200034030361440180c08104c0d040303040c01260260030040c4002801c102d802d810214141c0c2d800304c1c2c82e80b0301660412101c002494541220ba00c1c1c00f055a10950305407007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 171827589 1250 171826339 171826381
    0x105160e0f040e0111040501030608030405090106110f0703080a02100506090c0f09040608010204081902061c14040510110405090703050601050f040801060303080f092a090f0702060906 81
    0x30720030002800760384503904512018154080200020440440c403441e580d041405524006490b04001060078403001040b101503400081001803160302e0400201d52003000503402c14080d009060781c80a100b00c0400240024620601c91661101c400c04402440d120f18019000f4019080c072080c05075070b0311200c007000d420014403070074155500c5107201c0e10041c034803c400f0240c1e00240340210020b40380e40194060001d8900e204191001c0385485681e480d99903283c0b20010754000d0302044440d0100304548101009141c07030710130105006c441901c3c9050280800c580541d81d03600605444c0e0340f010941d100340c20100c0444040326007481d080c00040780d00800000c10a00034183e941001c41c84581c00350069034100b10410340701542d200e0721814040c1c06080248800c40114001d40f002c602c03179101a2200c1c0d8883c0342170200030001c84501e81c0d406280c40b1028032403c44146c00c00640e40c40b542d242d03050030b540310300044000944942400e241c0203150440040c40d04505411280034404096800540000e12070707 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 171828839 1250 171827589 171827599
    0x6040b0d020d081b070f030b1b040b07020409020303130806160210020c0c0d0804090f091505061c0809120a121404091a03070501030b03030f030a02040305030a0804050105160e 77
    0x200f0300400a01364400c0c00f50a2400a104800000a41001c500816001d1300e00c59103c40e1480e440754040c60a0f0801c10114050b8040414802441070100701c00160001c240002c002140215103078001c64155842400068000c5104d400f041c0500d0b0010808103070001c0c0d18419000054204400007510b641c1803d0420b824142c00003404200c0713940400001c1a40e400042130262895918900030030b00e80d02a109105a00d170808200300051401803088201540d0080390904031500b8800703040000b82001807503158030070200f085840000204a42c01003000348207644d0166294002410041564680d82d2070b022664041920310001039483c1c4880308100745181040c525604511003400d070b40303001d2600300c41c80701403a00369034004004040e4646072a0382015010303100c0380c03178446d8011015500c404d864035406501c20800c000f58143c02c0380040d540440b9a040c0141070907203e56500e81150700c103641c00400100c16409200c04d0210a104041e00000350720b580b000c8171800c0d0200075218800c0070b40041e100b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 171830089 1250 171828839 171828847
    0x90d02060d05011d07080c04060f09091806061e0e07090305100609050906010503070b16150c260604050a0b040501030c14030304080309060a090b1206040b0d020d08 72
    0x64403480c0a8410810025805000c55a120340c0120360b08409440c682c10401c0715240401c9056004840c07241c015001041c02c1c034906400d101040da000c400108408081140605000400b00098411047c0301c16041400c081c41115074186101a2482c1d9040051a84030191900c3c1c0031550030700303e032002c0311943d1410300d02ea07598001c000d80307040c0d5003980041d000d80100050140e6188180d1b100c101903401c6010200000c3d254804003a80d00c2070240203030b5800d5844040140041c08038207028195144202041c844100c0d00c565402c1c0007c0000682440d2594640d14406540740e003010039080d20068030101c5000c3d58541c002120b034038aa014054501607aa030360003180b003004194120110b184030161090243d96501d1406004155003489004204140070200c2c2c1818500801260101c0d81c0c0e242c000d6082c0081c85040120550001c2c8440090001e4510f00040b405025800791814503288448640c1c24038058050205440c1d000405c18440c1490580c8080140d6500040d00015500041c1440e10303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 171831339 1250 171830089 171830093
    0x2205031e0607030e150109051006030203040f02010302031b130e0f070207060c0c21140a020102100b0612010801020d0b04020703021c05160c140102010501080619091509020414010b090d 81
    0x20031144080c903545c0308402c2e44c00880e031140d994020a0244960314104840995154400ca0803400143c40041504984404020141d03100b500699002528000c03a400107072000c0641038066400a880225002a94203080241050602d292a0301c070900d602c840c03000e86008070009454211030f010300070078072120010180620010914110141400b2550142e802c0c090b51202c0c3e1640226400445501101542c40d120390100032520364000c0e68103030010107001d1304e2410014040d2120700c04803a0010000d001c1195074840e5505524028100840010b9540071202c001506a400301c40f94140203900400c0b440c2c001950001e0044080307109071241498000d0500c000b00c8040c0710300100c20308502c018800c1c40c030520111140c20700c01c0341c0c0c8148803480c4041800c0010390a0303442c00d10603582030b6084840055a0306103289000320010892410002e1007810503501e4211075001d032024142c440e543c0b00900411801c043c400c050740500a40060034203503160080000091150440d401e01031000c074858201 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 171832589 1250 171831339 171831343
    0x41e020a080f2815050d0602120907050a14030c03032d0403080334020c0301050a05040b060d0510060609031a090318040605060c0a1704080307060b03032205031e0607030e 75
    0x182c0401841c036042600d06d410030b407006c0e412406125500c155030101084c001c22001905c0b8080301c5000d00302110321482e02c1d684040d41021352407031940600401d600740e000da9400f40000d18140a105034110224001045066005c0d190004443c00e152002c00051020038500c809691380a0480171001c00c91000c214680340c85031300c6c802e0178581c0460a40c4420480300d900070030608500740c41a8003c00c5903690345130032001070326000c0d9800340c0320000c0c3c400800c1660400d01c2c0c00310885401281204c3d042c10b0041038482c100e9405074000000500c3c0742106100300960a18010103010390003c01d0302c5c035030412600f11901c03446102134801070320300c80503d298410f480c1c80d040710005150041c005526884102c1d09540c42d42503c44c41282e54481d41008046944203034015a801c0e1010540158103100c0c0b61b03581c10000f0003081030403640c18441840144100c240c64080b91003141c03410b011100e54a807520741031500e03041000303906100d0800c140d01c0c2009034042c0020300c180c0c050f10500e00030440c024443d01c0c40d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 171833839 1250 171832589 171832631
    0xf041e03170a02011e0f0b060f0405280e0415050708070e0d06020c0706020d050708070b04020103020f03040303090615050d080918071110140402041e020a080f28 71
    0x10310b001178001c8010403104100e50203074002e911550000d20205241904001080c0300f0400d04580c810002e000c180700604224142c2c0c0248240080343c500b480c41c0440300c40c494111143e100200382e4401404210400280d480c00c5a90002c00100038403090400480180c81c4110041080d0100300c2c65000d034100994480c221a14104d420040031540c4040c40258140c803048030f8001d40c00584984400941040c0c460001c45503e80d80083c5540e06103a00d5940703400b10300001400590415809002c6060710f4070034440198001e620070b8500040d403886030320300b10080d554641e00d42220078030072410400060305c90b2580360401d1039025290035030781c945001c00110f02482130303001c20708814200000c02c0100c82c1c002c2e030518064070384082115000d0a888219106030341030241038400304a001804a0300504050f000410030b40408900304008807075040c281000c90b00511603600010f6509418040040d010b9418180c0103c03500d014041c40b4110003488500d8038a24484810b000c036a10b01400b551001c0d408429 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 171835089 1250 171833839 171833861
    0x20f13090605040209070e13050901020403080a1d06030606040e04140102030106080f0903071716052a0411030408030403050720010f030b09130501020f0f041e03170a0201 75
    0x200034040d081c1c20314000410302228102c0c007404e544004120010b00503140140000801041c4001d07400495031248064240a40f441070199001e00c800700001704103001400c41000b0507540d4544840c04007407a10b61841194100700c1c02207600b0002d126450710740a0854094410000000c4103d445e0b600e8008c0034032040e01948041d17035101000100700294030841d164050020a10180010b8039204500303501d03031003203030402041c0c83c08803081e0404400c0600094000840c1e40c01060a9a2030661509414180c042381e511501002d18107034443c01c01c4001c01103a050100640d4100020300171003040785110b110181001d00460320200000d0100741c0706200f2a45026444440f4560002c0503100084410f2050780ba10740c0417810b14884414018820300c651031240c1d0000f4480300030350f1601d401340513881100c00810f41d00355408101c95824401010010070141c420384a40326601c0c1d141122505c400610004906560f01d211001007002c0341000c03a11418281e141c210303050740c4000510069004160340e00758 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 171836339 1250 171835089 171835091
    0x10121a060d060f0602161a090a0e01091d0601050f060f070b0708091501060f0311130302010201110a0903020103020310050306090c0111010b0102070905040501020909040501090201031107030804020f13 88
    0x4100800344503a080101201c007143c0c00001d015031251004ea8507805014840300451800860070040541259070ba00e045c1802102420300e41007141c0049000340c010f54100b56404241e01004100c0010326100709140c071001c500c0c1c815404542c07410001d859080602c03506104107582c080036502550f46e4402c68410440545c06c041d0346046030f25103a107445500f11082c01c04601d00b40c002400482e030105100c10001490b18140050783c1c2450410384007a01000711100070540d0307500210084916060007400c40c28040c2c402031816615620009081d40c03009070b401140c0f00810700c8419403181c2c001c80d082e01500da09007805600c9588944980320032901c0c540c410740d8980b107440c042c888600300c04240c40480703a41c00c3c3d071580d44100207134007514281c03181070324014016070003824108208071940d8409500584180000b5140080c038070b0000c1d8082105903025a000e0755070310040c408560701132003280d4170441d02c401d115080c42481d440140000d940100040e0061704107144800c8075690304a101c0b15400b0038608 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 171837589 1250 171836339 171836347
    0xa0b030a0615170604021213110613030c0f080303150d02090705070c09060b090103050603010b032407030501050a15092106050c04050d0f030905030d031a10121a06 72
    0x1009019005441024440d8855940404e01c50305044c02101c1c804034203541c0000440d00c0340c940c040c12110116206490244000d18041c090b681c3e000010b00c1e429404040381080c0c1811400d03d0001e14903640d10000701500e07031640c00c0000410200540c5e070301512000444181e900400003250b034010703003102c00a5200084004000c036683c1c204001d03115150140c401e141110ba00c541140e000c035003080c040c25170218000d0000c4641d40d03200e50001a071058006d0000b040314149034020a28002d08200003c074a000659103081021010220165000c41c1c2803400344001d52505d03012a180c101640982004e00000c0c0c3c00442241d800b0b40c4c81e0b5002030580030102d04101c1e5840c059200c000441030000c603042410031022407600d48410003540c0507904010304110f103903541b95031051540c80e82d82508030180004801c0000c4c46540900c804d802c22505070b18003103031880018446400c2c030f20007940194815030b914600310a0b290751200f41d50180c2c080319100000d14141203501040c071041040806580044001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 171838839 1250 171837589 171837629
    0x90209180a17041404090201020c10030e07060c030f0c030905090a020717030907060302070b1f0b030f22050604020105250503090f0102030a0e0f041103070309020a140a0b030a06 78
    0x2d00a00444001540100361124090200000d484404002074016403010381c0d0901c461925011114038000d0900b000142480c040000f03604202c500d0b445800494030f40f00300c6da01415000005a061419945050790380303030109540c003800220040c040d8a0103201901c0003d040345006074120b40c141074121540300040c0303011040507441903004940052880c00340030000500c40b8040c1c000d64a007a640046212115070b10898140340b03503644520340b043c085036030080c001150701c9200001c60044a5020040902e4078052605c140880151b100c94002018804030800c0400e1740410455080350382407038456918400000c078550500348400e2011141d00e0040308002c10400000000c0010103019a8000c010700d03044401642c4034051b10340032201098500251240910380440400c1c0103410040002138a4190034545400c19001101c5110100b0f40d40e243c2c407000d610384043d0b454020002c0c80704a0b6260110300700400d101003141c2c0300302c0344c8045020001c0350340400a0781240000e488544126585031940c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 171840089 1250 171838839 171838883
    0x1d06030405010b01020c04090c2d0308090f100c030e0f1c1205030108070b07051203010b0d050105060f0d020d180308040b010906060f11160f0e0901090209180a 70
    0x1da07500501511840421b81d1080c20180244251190880c2e101d0410b2413401d8801d44c0c84070700319650400b0010400308a032454400094050020b14000e44103552503462040a01001301d44900e4103074801c80c90007101c55a0280e21040d01c0020a90600e803554407062200007149c4801d40407414a0f0b4490f4214212050180c260030801410a00500d10f400b06143d2052b82903565110a00802c0f040da0010705003440110301d61401070a03240c1c480e070110381c02100d4095000a05070801e8102c0d40d141c100c0040ca192000e0b4503070050601501d400c450303540c40c100040032a10310341e1145400c0442e440b0b8002c58601070401c03881c1d003c06445420100718680306502d52500400241d400c80c0d086400403650400855600014414201030320750a440361000b24403080001d440d48402d92207601014401c1c01d180c10000b40c03041070410024611801500d8900f81040399108000600400c0845507a1400a42001503039070102c0090300004442c29030340c24184284a071905009020700c3c09401240306548811415081d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 171841339 1250 171840089 171840101
    0x60305030d0c020c06120c0f040b0a0503040501140c1602040603170a09060e03060c0d0e0f0d14070804090c2003030f090f060a0f0b0d0f0c0e0112031d0603040501 71
    0x10ba9404d403902c01c80b650042107010f010300c62141141002c1c00c0c00240700c0054407401851101000c8801504107681d40d00d18590321307030100c4103d000141c030220074041017003c00d000e484101d0440b0b6034500440c1c41c3c4602d400000303014000d00c614008640c0880d035002d545440e40300001a44d0440d510214217034080900d00e0296106c401d00c800007880040c80010494410100e4596050008020b400c2940398807400010707035040301d02d61000d4107540e0205082248400c100b003c03c503100c2c80020300015003c080c0e0203041001c02c070b40350781c5121000f00002c50004032a0000c544c180d0f07030903020001d41e01f410503008494081d00035003031342601100f49008a07691800080610b1241c0384d000b4003104240da9041d4a08e8a40c20b0850144c1126449030380452001415034100002030100c0031400144c020300c4500040021101d0030f41690051050101501030244404040002c0c008540e00302c00c1c2d65150900440b01d80c41448001380400c420310751078400c1c01d1503039602c6100074403000b00a9138036800c090500d14020a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 171842589 1250 171841339 171841361
    0x903010f0614030706050d022104140709020c031905070b0a0501080c040b0d020111011104030b160306080a080309030d110309013209100501080607020606180a090303060305030d 78
    0x5440c2000b04018600042c9000940c1e805030b503130f40e0800b81c01c2c4105070041c0d009050b40407400a01c82c501d2101b41c0801d0840b99110314010040c848401800d110102e003884455080070a0f6580100030138034160310000b04036200c81c420044020f285207040081181d9a000d00403008218080d000f041c00085507080c0c2255058521500a444084504000b000100d130021511107801910125141c0c01542c0181e032220007003083c0d000041107080d20f01155005542c059081100d0500c1d0400601444482d01c44861641d40100c0c1400c1108508141e440c5545004000004056410020006490b807a013842604c00343c014440e024071100c19003040da03c0d8150001c44001c02690720b005808903103544612404804024480000c4154900b414402034140c80010481101303441041c51044240c001c1d4400d81b40205000405000741c0d0a140b43c0081c203018000e040c40344600703a04000351500c1d95003d00c0580d0030042c21100010b003a036041ca02035024028650015001c2d0102003a1280021129044000181 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 171843839 1250 171842589 171842609
    0x10803180303130311040b0a0801090b090a0c0506031506040b0903010e0703111e0904030f0801060e1509040f1b090e24060c01090f140a0312050c0903010f06 69
    0x6145482450741c2e902075400445821a502d01d02000494180034050142c07940c05840494200f00d980c010500902c020750007aa00d0340c1d9203212100a0040700605c0582100700000a402c01c085503440e010105400d6001d0f1501c52580040440c2c0041412052120b201c00003901194450782d0380e0400c02001d4001c0760500e4065400c0a001e03000f2850003082001c140d23071380b0210211800740c002d014441c1500c8800661601c076107403804030400d20741d110000d1358031403442a0f0301c0702c4103500442c2009002c0d0310103910602c10300034645442d011a56400b04420a81046080465112140700c40020040c01c0311000e011805860810448041c003200c40741a40d04513526151084031550300c00c0a40f48810007103445105000c0d8a0020200c408200c0c00c0320102d002008003003500300301e1117400e450f007111a81d40049034000c0d28200d000040116401e07201c42e044030340802a1803050b51f252000792610803a11307520001140e450002602d450840b1095401c2d0050140c0204029244e501b14203005003a1401503090790 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 171845089 1250 171843839 171843877
    0x61c030c030f031404110a05041503050111040324060e0f040506010506040b0d020304080f210a09031b0201020304081501090f020721051b030d0f02040807060e18010803 74
    0xb4500078003500e0403c6201c03406422441e900e50300d5100e0503005080426521503800d290000b00c90b0365502443c0004101030201600b010b2451a24608455000d400300b20040f0b03050000300b0101e01c940e0b0369000c1c903810141e203c000030038015902c50300520007034100140c081582c00900001d0300803104e80502c20380c4a1000c44032142d803107404100280c001d91103060303c01c203c10800704190f082e0320740246070410b02c03c030003480c100350f0400d032001c80d20b41100e4603440b0741c02c070710f0382140300781411100c061a0400418841080b80070000c1e103004004070000341c06402040b000b090007600310b9108004490082c0158401d072080e95a0b0103101c608001001c0c451200201e007030132800e0903081e4662084400403680403110500c2070500c01c206140b8800b2901819080c000140a1202e008070603070b070103840d9a10390301e02445c1d40e50081c0c1c03d039008607100c802d90700014510510040c0320b0700c9000100301d01541c5681c1402401e580d00c00340026403201501800740000b9170381c000000f0301400004041c00c6d040400b0301d0f6103441 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 171846339 1250 171845089 171845117
    0x3030e040c020f0c04021c060b12060f01050d05250504030506221713030f12030b030d030209040902030703030c05120f0a11010b09161403040503040608061c030c03 72
    0x150b440c1e08542c4103500e401100361144180b81c298010105180007911f0341c040b01590807600011107000341e0040e00d040d4800140c5c513562a40800c02e0550100301107a11b4002c01c041000020b10030b004241d00d0400032a80c0d840071580202c403a84941984003500e1040c01200001540010309981062008448030700c6040c0114070307201c04004400c1401c00707071100f0464040c056503c6e842a40b0001c0404140009020048441d4514110b050100514000d44180861003460b20f0305084001d0f890310000c04040c5090040b0b90140c0c2e020800c2c0c01001d20701e240244c0c640f0300500000c3c00400701c2d010001e500d481004400810190412090300300c050041d001c0e85e102000c1c00174003190600c01c104d980413541d00c0400200e4030841c001e40301d1021400c000000050b075404140085001c41c5000da980201070380021100c10585a840307a1008641413040303000d1411402d041e0380b01c556900841c0241c2d014003864100040960311403426903080c03950903643c907807074500d59820082c001d02103501080e00000e0b0a03804003c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 171847589 1250 171846339 171846343
    0x30d0203071109130c0b040608160f03050c040509130b0606250c08010218090916090506150a230304020d02010806011101020c0c180606121302060403030e040c02 71
    0x16000342c01c101001500b071581410425812001007000700541c0c0214103203c04500d00001020140420b41c030340781d03515403e000e000f0740b500000a1418144052103490841d14550001c4201043d0800d0300b004034090b110300b03c41101c2e50156030003440c0c00c40c01000401001d01320309683ea03243c0341d000304102c0744a5110380c000c0c4090340c03161106423403c1e07030310318031440d0b03180c104611081c8155401b803200d141c0311503240d0030380031300f0782c4c0c0190300d042d603031010300f0701100c20030700e4a2151603400c01103000060020445060702c0d900d044829102d43c0004955a00025950791a1640d0740402550031003052030b40c880320900e0141c91500107201e00d210703203c1c1c441040c80440d121801201c0c09950002c0c025205240c10b0340c011140004010300403810810803441d0251481c10900240010070508009043c40d030020b4401d0040f08050303d80000d5045500740140200f6031500b80807100c501c0301c0c01c0c01007003030759562407940319920f4501000250098400200082403503880000c1c4010f000c800c80e030030300030b240c00c41a040b6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 171848839 1250 171847589 171847597
    0xb0a0b040501090b03040309170d030c0e1e04091b1406180405040f05011802091003081b210418060302060405012d020d0906031103130809031209030d0203 68
    0x79001c0b0707007140014403111030941c020b9a0720510918100580c603132650240703221a4502e40c040000c50b131040440071400303501409820150b0486160032074951400d20300042e032a03050034a030190f0300d4820080190444e145d9030000010640c001e1781d10401c110740c041c0032003201ca07814800c40d410703100c00380228102d51030301170115020503081e41c4207020300342030003c00c0000504000d0012103580e021224882c002410078020700c5402200c0c20b050f082104203d00501020a00003068903d080203000014000a4054401e0b103000c1e0a00724104407000c0e0380301807140d291103019000d184108040e00901c10f522421703200140103488440030549540156840b0b84001d4400340d00009510207014001803019500c035111081c001c02045240c025014100d00c003503a50144031441d1140140c01c11404072044980002080c07004000e0b038581003004400180d00800280400f400107011a03000900c04400d104200c0c0036900704d8000213003520004902c1c00540116a400303001101d00078002d09c6c0f09548058000300a032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 171850089 1250 171848839 171848849
    0x60109110f030601031e050106020c030a05070311010507060608010522030212030a0b060c0606010305090d02120d020f03070f0e01020a08040509090a0f0302010e1c0e131e0b0a0b04 79
    0x181c1c00c00754020203000c40c1c0e8200610040c1050703614850b40c41c001440022402a540200c000010703654101f0380c0007400d00f040041181d010740c0c030a00500002880005840c800c82e50000c0009401411402c012181842216400f41c49942001c1001c10700710011b60140e40503010440380a5407841e00b0b06a18080f409a2042c0a000350300818081041c568903540110b902036200d0b00001020550400010820740118400074402ea1294003005203950b054420360307810803c140c009041d482c036000c41c000c0d40d4900007402c1ca1180480495003003040105501612030312807107806017503200c1c540b05000402a0b2840ca07403002c005820002c0c00d0203194000b2581c8860640c12040d0a442d082c1801d0501c0802c100c050804c490911a01400c4000316052070041d54803244030394004107e680941102a01d000c0804030804180d070804165007844030b402034030000d0159003d035046000d43c404498040e0043c05036917030030b522000d04100d10b500c0035503960f0300c8681040400c0361101c4034940c5640764184240034500403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 171851339 1250 171850089 171850121
    0x204051203030906330a05040c08060406050603040f14010b0a03050a0201080a1b0806031207051506100503040303091a010b0417120418020415050403140c0906040906090c08060108060109 82
    0x10140043d05005d082c0600400d010389000c3d40e80c0e5680002c6022607884141820001c1d0144040c80b01501d0035002c0c0da4000c10084605034110300702a2246520105a05c1008201d003040700364004a28000390405181c5180042c042ca0a10b03036642011503c0c1d24829004900054044001800405141c800d90300460908000c1030900f00111405030b418003405810940d142c03080c581d1420b0315070701d02c1c1c0003010450704c01d00c060701078200c82e10680c1e049010042c1c43c161040d42150348141c00700394000c060303d5000f40c061070003103400402c078100030000f0b140c908407150626000c880007182400094008008503030f00d080441d454080006140d03074641c098001034000d20f00e000c00c000c120400052400030440c1100c1c0800520342a6602c00e194004d009209081010803030226080044c0900c0600b5103807100d40c104058881c400806001464410005003038502c11580c845075201400443d601c240c042c41d501071100d036070f840d8944990943d42c01e0244914a9984243c074004070720b0f5485030080c21514484800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 171852589 1250 171851339 171851401
    0xf0b0a0c120903110f071e151d10050306150c330708040c1401020606060d0609090f0501050106110a03081e040f0201030f0212040f060204051203030906 67
    0x4141c402030403104038203a08100d012101410030702000c4c0119030040a42200818886140c080c68190b01c01c90008a52030b03010001908000310b0030302e0400346200540602d0405901405000c600c00305c9540e00100907040f491259614040700d401800540c000e0008070344010014600c00b420010074400c12030b110815400c00c845000303000e24102144c1011108040d8086075500d894185c260044008503a400009512402400107114105520070003600000c19007031540d81c03a00c00044d42e2600060400340c01008000b88c440b42c0e042c25030740900c0150000e0314042c8485652030034100e00100361100140d68a519013000040c1d914000c0c3c2c09a05050b003064090300840d40c02c5e0710f0039543d6010003860312420f07100240380000360701c9050398170602c00d51007290320801c0c003a084d000041c00c99000e070302c0c0000200c1c0304109c2c54128000581d0551fa2295000780407039083c051901e0000060302031540201d4000b44480d6200c5101c11011016500c078581402c00c07611203984805913590041d00c0c0101e0341c264400642 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 171853839 1250 171852589 171852617
    0x60d0f02090601050f180a092f090a120b1006090902090604030f0b07020f070b16081e0d0e0c060703110a0b09031c05010302150c070e040f0b0a0c 64
    0x1c0d00c03540c412014140642040400c2c04601595070140601500d105036994613820640740c602c001002520902d6000c00079040090140040d8611600c40d050f00898900824090017040c4006c03162421800b600403a80e543e034400d030425180d032640200f250300e0101e400004101d49120301412003112415a14032485600c0c01e48160000d43c0704104a87c0c104c181000080041500b0399580c2ca0118854071190109140c90791000b81401c5d082103021600f60020130040000203110400d8800c4003010a8480701c520a03140303825a818400d1201c02800d020034a44040b50400ca9800138042c0646003400901006008905103a101c0c035092031100c0e804401400141e000c40e1090322034454029410049030764050303068603180c160410446000c80036506c000703518981c01c1500c20b142c50780404000e03800c0c403035541550b00145c411304504081c40000480071490740011b080170801007009000004205100741442e08009072a07241115042e04c42070040340100302c001e100c0d440f8680780e2101d250384042141000e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 171855089 1250 171853839 171853849
    0x61504060c060608060f01061e082215020a0f0908030a0305130b0c090a05030f030d09051c0207030309060c020a05100c1e0209060307030f03080c0d0e0604020306060d0f02 75
    0x740000303560701c696544000c0307010402045a2401860301c0c0800c42180e6141102c01030518880130285904210603582e5241456009940141c010201202c1201401401c41002d00e020100807009405261404111b03460388807264020706000005540714080d600c81d03001300361480c040358070074882240d00400420354914442d500c143d07000818040081442801750b1036541c1c06040695585000c00350005446a85243c03040e05c440c010241540a40503003000c20210945038002d40075046800c0c0c0d218078a103410400c0a01c0391036a4854181038600b00c4d2101c024000350b6407601c4e40070403004104034003800f0402134010228030a9090b4000d014160b4281818107020042c40700c40c540300c00b8040b22086450000d10601d01803c10210a01c0c1307125040ca4450040043d54000500f04d680290400c0c4020f10104408020914000b50582450445912250000785561080007800c8042c5490400090418100407801c1c90040740220f00310743d0150bc84608200b44c201a540000b01800c502e000020014201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 171856339 1250 171855089 171855107
    0x18020306040e011a0a09060605030a0c1704030e090f060306060f01030e0a0b04050c04050708040b060a0f0b0304060c18120f06050c0a2d030e0a15021206150406 70
    0x400342000c10750301004403900b0700b52a2001000e0144c584410326802ca1801d2405401d0024401d5100c28022680340031005041440048c146c00300040d100c50f62081c041d8050580b00013910a0030f8022039070380c03800382802000e102c585407800303110700c2d0304c80003040b0616840f491480c0903010090203400035454480401400c0641c030100d09041c5600c6070781c03080c5150f6081c0079070240316005405000d0646410701d081d030309181c1ca00d1142480381c2c0c900000d01c20744943c0044c1c3c0581c4503074484120701c0b451b111000020350003d80d507480517103141441c041c00b082d40700611001d1400745128070418408406000c3d1f0a45a4040100001c8542054900c081001c080040d0f80e82c03944500549409158a4541d12290143c1e00c0c06c6500900e60400001d50600440c0d102c8442d600d440c0e544072140701501d40c0400f4800340701008404140c1056200c00305001d2440c1d0600c94600403e0340131180040c1301e82814001c102a400c1050305001d941401000a000d40c10007a140764580a840d0742d20034900342c142542a110340c04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 171857589 1250 171856339 171856351
    0x3011409060a21031106090a0215090301110a030b030a0b0a15090603050307050f0607080103020f011b0b06190b120c04030804140406090902030a06270b070810180203 73
    0x10b10721500042d500c0d8640b041109654454001c2452000141400b400e03407101c01c1c2a6100343d42c45041040034440002c50035040e403d604507000503100621601c0011280549139101d0713415441c0c20452541d80072100700030510912540c9042c01030003404020907440f80034400024150406c80d0300013540e0320810342c1c00210303401d240040c0030502986440c091170856001d90400c5035954000075150302441420018103040659030b000a001d06d14141400501c4954107210082c02072019100c0c20280c1c0c1e01801c4c01c1c090f00c00f05101c80c56030100c00b034280a418220259040ca0013010046440c2030100600052242500d1640580038079181c130504112900a07030042491086880611000c000100000d00400051882c1d14101c50f02415820401007182c0c0c040d408840e50794035000141c030050b100071079111031a9802c00d00000f081c0000b1380401030140a103055070400c0e09000001c100400c03880f04440350042a940c0d070380010726a1103295050345086a4041c500c4d010405a90110180c0705540083d50b001c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 171858839 1250 171857589 171857599
    0x180209061801080d081609060f030b0603100f08030c0a14010908030f0109320703110c1507020d021015030210120506061801050315090f15060301140906 67
    0x2103881e11124040751000e8003c800560031130542901d819600003503c03a08074002c901444540c01c54400d0151010000d849032034107100b08440c1084629010340d0010341c6d0800047c00c0c0990f60320b0240c10802c0010103600941d4803101c0520b80205038400000283c8055100b0340c0000e00b0b240d1090340700c040009007003400a400c5503403118042400911040c000c1c1d40204e242840c02030145d410100450107031201c46000c0c00e5a07502c034071607520b0b0060010080b032203901080308000d0001d44402001b10050052850101144100091001d6030b00c4d500040324188252800e00c3d0203410784408108980350881c507940803005070702c500120a0056001ea200000560304080c1208001c0c0e036aa01184e00000031140c00400705900c805203c800e043c00d03010301940070004031a010701d8a8500122484c42407608130005040080c01f2000420018140a40d000d01407401003c07005c06180c0072840f0425003034119540d28082c01188440b610508014058074183c0310850a10010a07061400f80a955500200055405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 171860089 1250 171858839 171858859
    0x30a03020c0307080a02030705070801050601140c010e07080c030c041107170903010504030503010501030e072d0305100b010207092007020d0c0e060f0108160809120a0503040b06030118020906 84
    0x41c415000500d143c605e40d402658803105541007a80c10a40c00e503100701c0540c0d052104010050780d2086c055540001c0c545182900c84000c030002c4c40c010107036030544150a101c1c0380e01c0480e61450008d80104540750440403a404100100240019501c1d0b9905814a09506010782030009641c4040a0289292089038034101907403440000d0960710300761015800300764008018071195a05000384c440c6101150b0082c0030092902c45180350074a50308a20380c407034503043c8209115640803001d4480085030032008590300001071203e640d00070228035101c503002d40b044400c00a0916581d00070120304c2c02501e0304800030301e10710190000e010f9101300812644803c03070807601000a5025510a00a00100417a405181c0307452014811011160040d050600074020700308811644034140c42c950760f0300e451404140a0b21603d001c1d86c40c1250001003040040e60100e2a80740040d403010155104501801d400002e68840b841414201c0d200c1248e2145140130100100d0054240030907042d4100c1006403000c421 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 171861339 1250 171860089 171860093
    0x171b0d02270403031a0102030903101d061f08071512090206030f0910090804090e031608090102070b0c061506041707090b010503060108070e040603120305071808030a03020c0307 78
    0x1851402c580c01c03408281d5030704950411002032001d00324024001c2c002180f4107144140000c0e656150038a4141c10140c4440882008540700799079040070340b00b200e0484019003450b403004140034030b10701d0400000d580040400101820f0014a04041b00c002040c8602069440041102c85490180d0b006100d5038960010380016110400210320890b01e01403025a10305000300c0c00c80c140a0a55900800e560420440d000401c403018100c030101c4540f030300000764100581c0401421802164a20f0071481d0164000c00c05000348075000f03009a20b4241e0039110b185071204041c0c4200d0141076909000c03a40410006040015140920b0f0031a010003012a41000d664501743c0d42560041d01c4c041403641c0140304c04120300922809504a480e4007420481d0840c80c01000080034100014001d50801c0446440b800d0283c46940c030100145803c1030303034021100400c00c3e01901030b0805680400004000d0030b0780650071000202083d054808107030181d468a820783d80114041c4d0049402038800d0b02042000c140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 171862589 1250 171861339 171861409
    0x9090c020c0d050c090a0b130e01090218040308010e010e070e0f04021308011a0d15020d09030305060f011805060703090803160c080102030907030308180601171b0d02 73
    0x81070b40c0b02c0e0000308448201582070000104011b49400d00103405d14411001907524043d9402828200b1000018440c522130ba207140500700044010750003c1033700e0f84a854050381d040800e44104d001740c03102c007203e1343d85010030b01c61a0001d00c24070180b0490340c00401e84580c0b0400085a003240000e1880340000c41401c0054101d07404060319040020503000304011995007030240c6103405800302a50302951114070041810440320a00c01407010311a00308100d51007010364190740c0015007a1004000c0c0801038035000d0300034141612042c1c480d03120418005515845044401030041c000c0340d030821060b180c0010701c0b1458000c21804c8051014100300890300040810182007030400d001103085811180e4200114280c51680140d00c1c244d0042081099036440002c5030402c4a503d803a090248d60f4889451041e0400e170042c4a080c0c902980300006411740300440d80010040f200e20644000c605000501c0c00d020f056240d8494100094510b203d0251501ca03144030304400c1d40300d0b5820030001c4c0c411001703a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 171863839 1250 171862589 171862609
    0x20c0609040b09190f020708041401120908040e0127050c04030f0818010c03020607200105040b0702010c02010605010e090403020f0601090203100605030105180622020702040c0f09090c020c 83
    0xb4440009040300c2074010000c41c00f92400c2ca00005c0b100b1450042e80f5201c031003c0c0d01c01c50007151800a0580900300103a40f08004030601c01d194042c040180341c1e900d26101c65654414480d1521280c404400410303079500c0124202407111401c00c14204010b0011590005004020310b000b4195070103000c0003000c9602e05c45402c00301803069403583e0b5501c0c1d000b0b640100700840382c0251410440990400740c0040e400060701c0d034100c4a203040580350481c1001686903509440d104488265082c90300b440304000b80e40920714094407442c2c00a00c4120440c4800f03ccc22120f00e07100762400102280000c490a00304400e440750024024419034656403e0b462140749855000e902080d00c843d40001003000c50100101c100010341881e1070024038652602c0000f6014902a03111b0544040c10030010410503a0b48030300e25040e0300f00d40801203801906201b103000080d040400164000e600b00760b03814880500c201201c4060f001e154940320900f43c28088a04024140d903204141903104099278070b401c43e958190740d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 171865089 1250 171863839 171863851
    0x12030e0d0c050f0c0102032203020409031e03050c040627080a03080106020d090e15040c090501090e06090c0307050706110306181b210106030204050312030601020c0609040b09 77
    0xe85800e0082c54070916020030001c1c3d42c2c2003034100c07282400f102e03a40801120040500f040d601c0c101d0404800130304519481540c0000c2d8003519010b0090101030304440030400b01800d4401c9040820304614095081e00d43c212000d00c401c01c4200720a010352806010454a40c0e040c140320401c1e140e02c00e0084000c3c81d13200c0d42144000e42d1044c12824109070303001c0409409000e10b4806004a5602c10001400079445d502400c5052900d03c400141d00910703010040098800c000c20a2141501060303000d003449002d4003031039002561280010a038180301c0d906990103080003500d4030034203075120702eaa1175541e0805044103040100800038000450454042d0107100a940c040c1a546ca0424604001c44102c0c0d03030b100f00c01040d03200b400f006010300004542c83c0030104c44185044d47c1389421013002040841c2e1140851321501800004030745140d00d60b014009a80341607048400120407982c0d00802c41c0800c564050059018001051241c1403403000740c0380c3c42802400101d241000c000000d0700016040300c427 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 171866339 1250 171865089 171865097
    0x1a070209100513021206040c170f0105040606020715030510090e010c032306010e03160b0d0b030303010b07061107020607030c02090a1404080c0316120806060a080412030e0d 76
    0x1c00e028070b14061407001030319406080c08501c3d020308003003000b04500c40241701c58411555071440010150240d59420504d8140c01c1142d020703481c04102c60b800014007802030f02d000b6480d124010801c5400013500d9804d84201482c00b4900b10003000c0308a0140000800c0d40184000303840300007031481564041c3c02424a074031000890313403001582c0000e080791199414100e9030b2640d23500840440b2408130782079800c40000e10341818094680c40201c0d28090783d1b203d2041519642e8030000500403181c20152003803603010002800090704100806550740001c0c0034256002001308180c1000a080f41c0c4030454550700c4070300350380c1070402c16000030301c1a40060ba41030300440c3c0401c3c003102c11880c000854650084454100f0080034104004e80880c0900c02480240aa40001594500341000b00140c44180c0c0890321000d549400902c4c101c0c1004820f01450710100d01c0c0003005c00c1c118507201c016680c40312000d6440322410b9840b900d804040a250034a01c5003450341d98124400884805d00003010715a5003921 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 171867589 1250 171866339 171866371
    0x190e01080c03040b07030b04021b0109050d0201090c1e03060507030b0909160902070615061e0e010e0402091f1808190209070201230a0b0a050a1a070209 67
    0x141900d94024600c1103142800c004000004c0c1020310103603001102460006690410000440c000307200780d01c0b61201503940d400f902d00440c1d405410252145100e5802d8426800c4443d6007a4241c0c5c1c9210401040c0c02c1003000c0600401980a262045441190120411031540d945412003104c8090f5171501c00070b51a0302c001c0310782c3d0400e1040c03a03810200c541b00801c0861038240c481e100d41e070b0b50760017130700030043c2c0015441e428003200d40c004401200711101401c0c0201d903689000b9040042c540e0052021106c2007212540103401440d298403080d206849540c3c0700c0340c100040100a620030306407681d200d00c10100060100c10031a2051180502580742c18121a107032400c8665921215405078074142d000208600f1002e2507100048180e550540c1e40320b0598403222800c1e4050800040c4150510054841a250500f58031060714061101240100100c2d0520420700030309089a000c1c107a08044408410008038488007001008000c0380b07980e86084c400158005030f0401001d48008030fa0280d080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 171868839 1250 171867589 171867617
    0x170114060d15151521020a0537080424020c01060603060801060506070f0206070507080105040b043008090c0306040602120f0415020f0408030a0207080106081207110619 74
    0x2020341d20950113905102c030460320146010049650520215420305030081510320005015100b641c0044900043c08044415020307103181d01182d03160100d03502c9200d4030315032598141c01010002e02454215100060502e058182c1020090701c501c64104002e608101841c0c6a25081c400d200140c04196008540e661800c500c507400d40341b85030412407103580208400c200103403031a50480000c2d641603440ca62a05404d043c5241031600b00e620642c00c550800e41000304000300ba03120310b44070f9440342c0124200c0051b40d0b0103940044410440920400c85242881c102c4940140b11150303110359080304403118407800501080c2090400e44088951a8020803810050611185090b502c020708011179800d501d01511520f4294040c2200300800315800100c0d40e1031103040b04111806003040c0030071203035075402d841402951544584500c07101c1d5480c0c62408940c4007400b01d0407030141100c02200030300303040e4191554141c62100e079610552180703007041031400b400003950380903e8450083d120b00030354020b20 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 171870089 1250 171868839 171868859
    0x30c15020c0f0606010f08061302070f0807031404060e1908070605030f091c0e04020d0204120204141302131d06090105090604030912050a02040510170114060d1515 72
    0x501001c5c1800940424031540940c099891680b01070111101c00400b410707040c80d60b0091042d07100c094040100e545e145d80912581000a040700d0f8425610805484600405902507024900480b40050800102c012680c82e000d949003903802c65800c105403804c2c0d581c1032454907154141e400000801c20200c1005490320380c24100c1580482140003600f89581850700c04151400c80c038081c0d00601c8a400c0c1020704a44036a819504c0f110800c0e0011581da9454460031a8031900c071400c1240f1460501010201c03081f15105000e00400d850704403144200d21582c200705050840d80700100d00310b90344040d98452083e544980800c504821000381205051207452035080d240c0003004050140d0000052200181e0300c590000e00701d411000d820030ba43c00e00782c42c0690800c03035214000b0b54041d0400f0188038054100407541821903092090122124078200c140d1400d84100303c01d003103000941900000c050382000e040e945a92031090b03010b134480024288920713044a15010510195418400d024400035a43c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 171871339 1250 171870089 171870091
    0x18060501030f20030711070b28050a031a090f09060106031803080915010f0f091a090c12070302040306050105061e0a020a05070e09070b0708030103030c15020c0f06 72
    0x4110300600c0060f0001d0030000884028600d40304001c100000050b128911074511400100354030002e46549031798441e040036407a04007941a03607550701c00340440050030050000c0c070300c0241c5c560f40314a4108454444294001c000903a29400d40d03401800c1c01140035519201c510307204404405504926051010f111407a044050300321030103242c9040041031a02141c1030b102e00015038507182200d00342d607410000b0340c20041d41707003008003092a006002007011880c40e44044185e0341500b1980c56400e80d140030040668001c0380d60701c41c1c0d003980c2080800443c03c12075200c40d4802540d960162600144450458518500320b90040000740d0104081c0100200750281600602088507000e0030b0107030401103050b50791201c500e4204189030008520a03598002d1180443c040d800000b62140320365a08566901c0312070442e282c058501071400b0119040c11840b0030b17210318035001000c050450303013996015140020040416503990300301202c1d40340c8030201c0340005c01500d03e500014122101070801c0302e41c50305030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 171872589 1250 171871339 171871361
    0x3030e0306040b0f04020604090e07080d020120070501110703030509010506040c17040314070305120604020703020d0c021318020102070b090d02041817040e0c07020901030206070c1806050103 84
    0xc00140b0012900b92001160040d4070b10030801465103851001446500c115409101e182e030402000b42c00e6840003140c4001103501e804280c4450b401011012402c944200140d500340c00b03206042e140307000c04448050045588220000121030302c1e40c90000f5059040000300301d0000780c42d0003c025040381b0a00a01c0e03009030084e6810722084188140180001d0703080a0000074241c411070000b000e1620441010b40f80c44880d0720710641d42c0c209410010115800602c0049650800b1000710302c0702e00b401d1080301c4405425070b02402c1039003111002114204240c01d001d81e405210700d00c005244440c50b2148001002e030601e00842c6043c154030019060008541c0156a0542d05105038902600d810310b80b8007810394111000034510b504513180f050035002030342018142002030920500910b116100510554960b4044000652741e100f5a400040c4100c5000a4000e14100c00420050030110082c0207024800c010b0820302d90b803140d00300540c40340041c6505541ea603d8420070001560548503048800d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 171873839 1250 171872589 171872593
    0x1d030703062c190f17040909021801060c0206031807060e01030b030a0b010b0a0507060207030c1b05060d0e031c0606030b010503010f031e06240504050f0f0601120905060103030e03 79
    0x18501c400940383e03441c0303504005402480c401e548441008001050071030707520418403006850326200d48034900200460302049008000c6d25811f00e000f01748454140e41240c030191303034203600c044550782807044a40010b0001d04803d0707084003107166504028840200030301032a642c0c0184611040c0001804c0d1050305a0450003a00030380c040d0400b0031070741401d03103054907105160b1642c0d0341c103614401c8680b880349039005008148042240c20415500c03000018009020380c10107541d4040004d0744a5400c05244a2103520103810040903405a2a03900b00c050540c22440969090080301d170898a00d0401050200086617520141803080e0307a0907115100072a07500b8a8030500b1581040354006c0003910a02024240700181d80800218401502da50807115030f00400520005481200d62140c03003499211100014400010200381410948180d510411a40b115007d454580c0038102d100c40030040d05a40c100814074024104030344181c06607125080c0b20310010301e101d600d1428000c000d01d84600c1054481c0e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 171875089 1250 171873839 171873853
    0x615071e150b011211040909060203011d130623041203110a0207030f0203120403080306010f0c050c091b070c0806090c0d0b0a09140102070219061d030703062c 70
    0x643d80c4800130007001c0c800f00100144200d11010041024000e59201504407424200c100040010716005941241c0044041200100c03402e82401c106082c101c4500d02d02444055142002c07c00c03a8100c0c0300e00b240801802e0041d410742034102d40c007003141100c0030b882214076041e00e034014a03450310801e00314401e540700a9040c00b04040c0001d44a00035440045c2200d0042c00c190403d40d0303410300c58002d4000211502d0341d07846559280c161555041100c0c400c0c0822142c0c22000d50742400303503010b4286c0340c0d40b1a018000205422080115542c1d0240c001e55266540031034070070f08421a00d0080100a004101c24030406d890000762520306a4000c00c0c850054201560806464aa00015a45850703110b10070b2011542c808400200904501030050207540d201d406001034010198001e0001d070340207842040e400c81d4240300c0540b460007175200340c034000b545150350300110320348000542c855400c000b0140c580080d5283c0b03414060f81c01250040c1c24030068501d403225145840507410400c980590090100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 171876339 1250 171875089 171875111
    0x24040b0f130e061c14031308060702031e0a020c060a1101060b0405010206040312110a12051302060409020d02070506070305010f0905011a03090c030601080c01030b060903060615071e15 81
    0x40701408030708000450a80e480310020008450004400d207840300041340e45074070020140308400d061508c500c4459000704c40200740c40317510110840da1001a12005846412031140a4031005d50011600c0421401141001001070b074600004010070059566100300900e0030345c100310b007121959445240031200412080089076000319589603c01e0f090300745404040d800ca51311314050000d11050f455503001c0056109402908400001d2410209200802290741e41c540004034001400102039071081c003d00c801c0104034815002812420300c05031008d17040c58100c1e5141868514203944050100c0c0d00d810051140780c216481d0780c4020301c01178200384180d500d0015441c1000114882c59503030740d000000082c455180030481e003210a40041e007210304c2980d680201949031040c44aa890001c0c0c01c21020141e58908441a6882c0741c600801800142d26080c08020450040303c0310280d442c04184000008144d8048071440a04103034890701381051110b2400702c00001c80c40c820190f0962500d0300d0420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 171877589 1250 171876339 171876349
    0xb0603090a110d080408060a27021201060504050405100c0206041109040201050c031b010b0111070e04061b2601080c280f03021801030224040b0f130e06 67
    0xc6000c0c0c01c03680c1100c4420000000c2480d805943c10b0142c46400001000221403400080d80c034400d001c110420000140840310020030251411403400d00100c5505e040d50241c6040d003008041d8040440002a066943d41e001c141035960882e42940c0540120516000d80740960041c04090310651020f02901d00e080d40e200540d0700b00c003014850007414018006401c5901580031111540d440b1022a0b072a0f2401000c0c100c040e4800000c481269400c0190b94204e40d4018225031304042c030b6036006861814204281d980c10200300400c25200c0da900d0b02011441c121000000d442d5000580d80d52044890b020040b07504024119240c203110000d020f0010000da00300410b00c0018503004541c2d1340c041d0048405418030144d0240300d480400c0c0c00c107190005410080e01501c6003100d1083c0d443d41040300910b0144010703070f5030921001e0b4120481d0021000c0b880440d10712407210010079059107040c2911006165510f4002d00c001041f0000005420100c01300d00f4140e810040a000d04c01c0c1006152450100e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 171878839 1250 171877589 171877603
    0xc01020a150b03100920060a0c14012304060b0a030c12110a06020109020310050405071205120d09061a0609010f0c21270b0a0e09190b060309 62
    0x1481c2941c4a400d040d0564040c809030000d941106018420080c9a0602d40c40040f880c032036441800074610300300f50143c20000c09481640310940c5500828a459448140f56070002e451040a0743d50307264681c0d5034800783e06406045c5600580241d900621700b505c0c12400700d0726455081c910801c0540c20800c00144003001040c10385a0b000e2100d18000d00c40d182414480503844501e5034071421100b000302d81d244d81540b007440070034002c80403200c0b10b4990502402c00c54070b099801030280d403c00d00080c4081c1c551050213403510341c841c0003202c01246800815040315000044417504072a00c0c0c10601d024031196014840c07000651404001c0301100e182c001420301d1044803001c0d4184961403070000000c5020707070014030000750401c03003031031140c1403929911050400c05581000400e040d40c1c008046203c200703032040e80d082001c45480110a0400c0c03e80704468001060740f404115074a00d00040ca5150321044038012203500b164240a4120002d030a402c0c0c81440c200a80505000d000b00000712800103480 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 171880089 1250 171878839 171878873
    0x3100303030b1801091a0904020f210d0518030c090a1d060a1b02070608040b04020a081b010324120c081f0612030509150d09060e0c01020a 61
    0x540858402c011800e0ba84803246005110384100000181002036a04800f020050591600039980d41107400c0082443c0d05440194001030a082c0311000b030f044c850103a8504118148041c2001c94001c13121501d02818003007030000191003c00d400c085280c42c00c100c19101c20040340540a0b001d8001e0205188c2c01c0003d082c0081281c50b522203d18140c480070104440b180400b064608518104200002070000313031079441400000703c0981c0e81c01d20310200e024800d403a02e5580f0406d403900da54854034407045000d40140c0e4001000d52000440010405c40b100c440ca0f0700c4508200c01900c20400903040b5001100e542603805100803219044036000d001c508169038441104148443c0281000174151985401000340e81c850b03d0031030f20700000840000d900f0744821080c04d0103010b172280c1c50403951004111004000c0742c81801007250740d00e02500070100c0c940740c8410b91410080000005020b80350070f604140c07405541d81001d405400c0d424495004200c0342800107000f94842595113211001c0c442400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 171881339 1250 171880089 171880091
    0x6070f0807080a0b060d021207090506160302010b06041509150215100905130b0604061a030601031b0c0512040501020618010b0301090c090c0e0906010c03112508030310030303 77
    0xf11540700c15030000c540040d0240019480f400c01c41d00840003584518400050504004c0015415602c540000c00503208044c0019050103c1a0561145051081000c030b0665484003c1c2640a8844501500042111048181e00e47c04840300140c21007096821100c5003102c0c0c89480c2004580003d08a40c8242c0b5042c0c00000e1683c940402041e1003185401210743c0780e0414040c0070007080d0114031540100d00492a81c04d0640303a100820040b51414803464800c113000301100424104150003940d4000410b040c00318485001c2ca151245c100104020b41002c0b40380c5518a405200c010460841c0d02200c4500ca03604c1c00c0c0c10040080c0d0b440400074040c9a00d40c5413203c0c80717450f080e400c1d0008010a0b0000c2c009000400c0745250841c04031085000d800062803415061009091203141070020665015000441c0ba031214001150300c40c440800642c2400030321064007040782010003c1c1100b4495511044c203001040d00c6140c00c8a00003940b01c404941d00c14030500c1885407082624200301da9150034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 171882589 1250 171881339 171881341
    0x40c2405040614160302060106110a020108010306020f19020303180105150d030c120c110409030c02060f1b010f0507080106090501050d061206060302030d02070311040e07080d090806070f080708 85
    0x2d02c429180b00d5480b40802e0340c2110440802090340010301f10303040c1d07086603c0304400280c002d9a0207a50741d20f40500032340000d500b03000406c0440d60035801450300b038000041482c80d200aa10013944004000341c80207005910010801446d0403659a0603102010424000d20403410100760609000040d00300d49403003101c0391030340c40f01013600800c401400d8991004134115820101c2c0c0c03010782005148981075400f400700d0741500d25035103041e200c1c0c101541e625454000089030b55809101c10b40d00700c1a00317541800d004002500802118421615000c4040c42c000304196190800a41c103441000d0000024051340f8001401001d0b00b001c041001d503a030038607000c0d0f100c800900b2103034060421584244c821580700c02000b41842902c0d005041075034001c2d82102c2600101d400220f0382c400e004d200140c004154a0300403445840e040e00980034040318a41140d030301d1a142d41c0c1460401074410604004078510402c20041500117000303643d40540181469100b014042d00003810703001004114100b0046804 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 171883839 1250 171882589 171882617
    0x506010b1216020f0a2904150b060f04091e050702061302061621230c210d061401080a02031e10060e0402090a061103040302040203040c24050406 64
    0x1281d031807a03001d8501124910490b0f401c02010024120800b41c0c0364907071b80f54a00c5260300c0c8021174140101c0d8002c05049404100380004402444400d03201c40c0e1001c0c00b048810265120400544040c0c203640c1c100050100503444030142800110200c064228200310400c40825004940f40da804003d02604110020706840003030311074491000c1c207403c6140031241c15414412010014900e44106d181241240d00910a066a0003140c1407500e0a1483e2400d03145044681458090290ba0000c801251f403080d080c03010b0050041c54240428500300000704100650b44001d00a4400400510420445100842000800400d0024200305840d6000404168182c4c0da02842401d1180c1c58503005c0f04509084a2003c1960828072982e0700180c2c40540d40400c503d8103100721555140c000b8002d04040745010f10070740d81d250504040721080c0c0024000040503031120300082d842503104402c0340c405d560078900004036485048000e441e03042c058600101d03841d03403c2801c0380d0070fa64003401c200e030480d1a62 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 171885089 1250 171883839 171883843
    0x6071202190c2003070611011b0806152106031009050c040c03050f040f170a030c140a09030209190218150a2f0a0507030506010b121602 60
    0x11900e001d1012034070541c0030102a4001d10507810035104400c96410210700b0000d400780c000325001c3c60343d4160804582000b0143c020700408030b10124041c000300320102038080d5211004a400190008200c016007044a245007010140280c1c81030080d0844c18418155889542e403d403105151141420750000305d11780b82e0781080b0103042d4041000d03051161396500d250041d01c49400309040e50190341040b5088002d24040e0050383d105006500700700382c0e56920b0703407149003141540000135a2204106580221821601402171010040d181c40124141c040344000800c00801034900d2810000103009038152541d12904410840e50125141c1007552124031000a020b2007451150020910015401003464412031a04641c00380844110b40550382414810750980300d01801710000031804116201c2c41c1c0e200b02a8541c90480b40e02d6a00302040303000e00001e2805c0c28a203c00d031a161b2000104004210080010a0241000c0c510143c24451585184010040003511014442d0800c4000e40a03891007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 171886339 1250 171885089 171885097
    0xe0306041e0f05060718090204080a060c03020903070b03061e130b1302070606030204050f01151b02100201020c06010f060c030e0d1e0303110f070318170f07080705010206071202 78
    0xf4103450450070f03c48006400307840b000e031424070640d00f06040020390010b24400e81e0200d8011134041d040128090756004000c001c03100750030081c0340d030900103051151003c01858000c0c0c42d01c044480d50301d00f004010440b4400100081c2d000b014030104002801c2e84071120040030002e620342012030b400c0700240000f4000ca81010b034014100f440401d0480c14009250011070840703000387c030308000e075072940845481e451109005510098400307440034141d282c0302c1c400d011040c02420641d4501c6a10301c0d40011501c1101d02040300040c1e4000c00d03030321f652010a02c07903030f0f004290300c0b101c1e59101031408001901211040d9005000e12108901009291300c030809031505803680401d241c034621400b014190168400700ca000c0e000245804c00515807044144110381e4201a001c4409040400a560403a011325003201c030b000b0124078a00d00007a071407002c00002c00b0301500010240c4154864402a6443e0060a5110101c2030b0302020b41001641d8020901a800c8480d519268000a80c80384403940a071103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 171887589 1250 171886339 171886343
    0x9030f1803080310090f020711090a060509010e060f040b0108160e0901120302070e04030e04050603010209030d0201020406020c03070f0303110307080406030c08070809060f07020a0b0a0902010e0306041e0f 90
    0x4000010408060010780030001500d0b142101002025a07181d206c904900400e400101a211821942c0d00c240c0342c0303920071690101c103802d008605541c23a0b00c08070300881000c2e170140300c910040d00b00b440802e24050142521001c2c0a840401c800d00c00034000800c603100c040c0c41200d8a174000707600c00305003d03ca4521031644480107020b964180d40c0d50880301031403001c0513100f030340180602080400c200030380c0810300d80a95016a981520050b0080802c00180700161845605650802007014561820711040810b003c0e603400058589e0b1811070003038200030480480e1446a0040075083c0102d20890b55034074141c030f425180000040035041c4025180d44140c071006004e40034049000950140d058001084451080d0f8801d140380d151044155601b020549400450742c00100014000041c8041c440b54083c0c800d01c1260b43c40c072465206c60344000010b80703040c15019100c21212042d56004450386814034810f800400c45171915841c2c0743c2018120301e001000100010400200703201580a032115203a03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 171888839 1250 171887589 171887603
    0xa08030a06030f0f03090b0a05030606090109150905090a0915090203070b040906090f0b0d020904080d020f1e0a050a0c020102101409010506040e0703020621181009030f1803 76
    0x2c041403c040b010404810401c400040000c0300208142c0c7c980800d9410f83c8034540c40380c5055445000802210390055601c0e141048444040041c50f801070041c0c05c0c00c0020540c840201c140e0400f1705100410364000c003210001402e0550120001d00c120401c0d1040c80c042e100c00088100c65480080d0508059602411944001082c0440c5c040c07950ba102c2c1040314180001080944004800c1c02d054071416002d41e5071000c0c482c148040941403004105a1041c4100b141c24a81100e01e440741e4100c2c1c02221110f51880d001203000e440511421304c07644021244044568144115204018940d10a0a081070b0803c0180c3c8040320842e402009140d030b10030310200d03085c4000c01c90601b0210803103408840001c02e075800c003030210300310341005d02c60300f240b9403107940250140e281123800340400c50740800c54445100d8003a2031b03c4060685c20710600c41c0285282420745000892070881c49181c10000e074403100c28907142c18540b01c00a1f8004203500400029810700200c100c50a0402800700c00c420b900141c500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 171890089 1250 171888839 171888863
    0x305060303090907120e0d050702010c03020c0a09020a0e04110418020408060a02271518030307050c1305150103050403050702030a032a080a200706030501050f09090a08030a0603 78
    0x10a800c03041015070103176525070821050100f0500e40390344103922170f580c1000c10801c00100c3c003d54461100c084034240280120b65860070000041240140d0560041403140c3c2e020403086100c0c4d5005a2035980c09004890611038024040c0d007240c060320a034031401c0c0c80c5145500741e80d00c09810755011f540041100d04151802031410303061030400380d40941c250500500c1d04031050510404100104490000c000d040740c0c41c44200590f8140659000040c95116902c00503141c0b485030f5010802490b0b414450405001d00060000510000c16045d4038041185400d02c410843c131180005240140680b09190124403901e036810140c038503109101c4003942500078034246c0001e050b084810480c181107004551019019a01c02c4500400140c0d0f0000300007041c10000c01a1040c403a000c0301079115000006041c000303541504075450301c10700394000d07004207840b10010000c601e4541407900c1c0039003054401040b1441d005204985800d488400108241804130100c0d03103203121644454040d5601440f00948 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 171891339 1250 171890089 171890101
    0x30e06092e1103010510021c03020307030605090414010c020703030f1805090f040b0a0e0c0f06280228200301090309030b071713030203120c0c0709021903050603030909 74
    0x1243d009005140c0204901441c5501442c4000b9003804105c00b580300260340e030324060380110007a40c0f010f04a42c04042d1140707000715042d81d81440142c0214801d070500d814050517007080c1425139a0300c013a0b84e01990400182000482d40003942000e400903245003540c15200b6030349042815401a4000580002041c410001c0446410350050b00440c002c020b25142c5558124156050b03a09854064951317401601d442c2e1214200025a1080104000c0002d407e0032004104034117100c540d1203c1d8403142c80b1b0391424014094041c80110185036200e5283c80861a038011601000d6802c0344004120156101035092040384420030548603480040c000c0c42844a5402e000b00180004e000607140070008401003024940512038002681d41c1c0c1c408905000d076110180002020803183c01501035000407c00e40f03000c109030f08031092140c13030091200d0752190b603568105403401c65a0340006174424410010b80800340e00c4040281c105503454a80400e403982c417000440d045000f0303080219008842c460502c41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 171892589 1250 171891339 171891371
    0x3021c061502060c030c160f061401151806050901020a1203090209060901030210050a0c020303161a0405120c01061a04051201050609010b0901031d0d030e06092e 71
    0x8071400305a0308640c1980c0760300710510641d00c015120070480070ba0402010085206038075031000440d00400104081031040d4841030141e07496440301d4405846c02000600c1021503c101031f1000359072901d09000b1808c65104503070003503403482c040c0c0b0042c4440402c8481c600d0788200141c4070410f030300c40441c10030012050405005001c503503804903c9006800002280780c2130a40402d1b040342d0300104004150502e0311011356003079011602120811007500200000340e00c00b0030051641ca00c02008100e5041801d0a00f10929020403020411940015007170202141340003c005803900803110b00e0741e40d52802150201c0c0103101550103c2e80c4e040c501d698204141c00603c0140048400c25940910716091850015007200e504440d00741c0d00c1801c1d14010702c404002e0002034407154106041c0010032641000e0700780c1078900c0c100440151940f1020b040c03400194180640c0d000f0310000002003802e800e081340c050b40c071201805040000350000720280a0002c440c4004d4000003501d140082100200d6440903030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 171893839 1250 171892589 171892619
    0x30d0305091f0606030e190f1e0b041101020a11010e0607020a090e0d18090b01050c0105101a070506010e04020612090c0301060b1204030e0307210218040506010603021c06 75
    0x40400c1c41c3c61a00b405008010a0001902e40f50324000b41d00f540042c0da520f00001045c81003543d80d409113181d52a09c0d002c48c000206985401031408400500d01071611440c2904100b07000d50440d0481201400040d251001c416001d40302420060611114503020038a503004501c07000c4d5100703001d510000394001c01a80300180d20300c480340035070300c02c2c41103490b0503100d800b005100c4201000b500d00082040791003547c080062200145001890400e00b840081d00751030043d6000c0c41c0d8003d12000030000300310182c2500c141c0c40205885207081007880d0316400c2d00e46505118442100255070006400c5690f18011118036807481d1041c00b00609045500740c1d61602c411151602a61a0107004114218074030300342c8160b0341e14101c09540b196200e640884101100c0320025806204280001c11684221452858040c07040903440344008443c1c010070691086400501103001e01480c107000201d100420800d05442441c1005652007400c40604041d05070301c5002210482d16006011645139031040c542 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 171895089 1250 171893839 171893849
    0x120306120a0f08030a0f1409070608090c010503150303041d06041b0e0409200a1203020d0c03170f1f0b0901140705030f040e0114030d0305091f06 64
    0x4010144442090907030346021040380980803000d051422030001c0e240388011641300f5208140440c050296240d000c0a0b40e1043e958003940a90400030024600720400000004105a140804440c100300350707000c0d15888085141c50402c14004001001c80c050014090131185003d811030703540e281d80c3c560361860f402c1040c949049010003c00807a4a07071a050188142d0b0b440c800c0b0f110300c0180c2c00560b003074410040c00c4180c0b681041e141c1407004007188480304418032040001515001081c411010403480920682000c450000807907041008a58002040c4030b804415003400f080920f402d04050b14124803013a440301070b0201003010005010303062101140200c52013100e4021400c401c440c0d101903d500d502600402d11000d1006800e25841800c480f5052990103003420325151480d1544e0341151700041000010301d900142c104000100c0c0c0f03008900400315002c04200d004401000241c03a0010351480000305612800072400d900010b010b4801400b51490024150078411076010000c0e082501c070b1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 171896339 1250 171895089 171895099
    0xf040c0905060d270b0f090a12030204290703051c050c12061008041205040801020d0b0109060f12020708120a0e19020303040306020f0f031e1506090d05010e120306 72
    0x32010f820180c0d40c620100c507a5000d01c0021086d641d200080d442c1d44002801800903219030386025002c5004500c4000d184484c0d0b0341d000d0307500c0f4100301c001c130403601c4250800720b4501e10304440030101c0500803060f1a0305941c10f14000b0f551b1a21810380b00000041c0c0a401310400b031600040c00740000b4124018060440743e080014629079842c2e04001600d50a1482140494101030010300026003c01300440300712040e0a205061644a228050880e00310341c0388400a10743c0c07041c2d0031482c0e40e080b0075010024056894102a5240c00080040401c066017a000302c00c260003203040010070003008140c0700540d0080d8590300a52400e040d040f0084c00003002c0d401468010103550100401c19044800c081540207801945820701d1a80d43d44029881151a444038010074004010000501002180a880c507408103090040c0141d0300c80c841c40310050041e20071001d00b60803020b02515240283c4900c40d10444050407110a14240903015229959040303100c7d001d403548a010754030700440614010381040e25 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 171897589 1250 171896339 171896381
    0x302030105150415111c021e0319050a210f0e0d0c0201081302031603120306060f0f020c041d01050f0f0402101b1a0609060f040c0905060d 61
    0x904040300c0d03c580d0060014213000031a0b010f8606000310002c10106040900f210841080f04070104103145507840c200f00181c0100000c490b1040144241955500d01d4a020713520300130480840011804000c081181441400b1074802600342c004c8104004003140000359044820507030513288000c00724507241060741d519207040d62580060010b030b10071400e2529240c080740f0952075001982c440c2002003200f031038800008590001038909000c491200e01201d2110b41d42e41e41580f4200240d294481c568100300b62410108000c056030200784c0c00c9114569040c0740880e480090012800c1c01d42ca03089040d082420600006e41e0712400c1e0a07101111a4400000c2100b0f44a070165449080d100307a8048500711b803050013240c05807070f008130450702910b0f0600301130246200c90018003020300c81d0464250390b0183c04080d04811650b0619096511000c110b0b2159030781e2828000044000583c0d26205000b19030300da02d01c0001d14096400e0001820000b08269211064180c40700e015050b01c014440c0b003600550 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 171898839 1250 171897589 171897619
    0xa0c0c03020312190212090f1203070f120c0b1303050705010606080615040311040203100e0108031207022b0e04060b04140d1e061d0601080601051206040b0a1b0302030105 75
    0x1154000c0381d18404d81d00c042c03421400300c0400070360110800146a01c05180e00c8074072700b1940104000d19183d480307800394a20290050a0510142d040d1030005401c0c0040e098800c0d000496440d03010b40c0c03008042c0a000b005500c0781c241140c5074042c45500a251750702e4a030011480581068000b4450207045801242501d80041030005078080c2c2c3c030008103c4200d00c102c240c1a40b070590055584003034603500e03102c1d00703598401c1402e05500080e44480c2d41c6400006240201039101c824135684202940010102c44c007548046d41d0b0b01d0085150b6210501002410444109200d1400041c20010041007402107a4540c03030001001d80c001c0c80ba00080040544101d15a82815103404640b5504005115803003802d10040108000011408580c80f650340d02222840c03a1842101c070521030008001041c0703641c189a0030b60f00d00301c070682003644a4207550701c40900000c00040c8256110741c1c090302c043c000d5220980c02c035014101a84150103410304c80505180d0207a0316a0245041f54400c41c0c0c1003070980f40382 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 171900089 1250 171898839 171898843
    0x8070506040b040e0615040e0403080f040f060c02070518180607021011040f121401020f0d020c0724021c050a0503190609090501110306060a0c0c030203121902 70
    0x140c410194492010f000400c24a8032084400340d01c6a0301801c011162030b9040c1410406910940101030b004003820244800d00d6800051a98021002c1c1d00c00c41d100d06090300c8400c80003505e154020305075512107240740e448510038042c2c04010038020b00301411280602c40b02c01e9045104503800554000240600d00802074006901030080e806a0003601d42c3c01d00390310115000e0300d420280700740003180c104800585a886070700880c3c01401c150030751042c08580c624000b40031700300520008029a005000654101c00f0540072510240303102c880042ea684880c000302811b14005034400d030742c0481001c90840d681c59100035031808685080d420f44a5140c3c92000c241007251441c02c001d00040d9080c0400030307440b401000250741050310005049070041c03655041800ba24801d4100107800b03a00e0742c440d9020014240951042034070921401411854440c0204000d8080e441c1000100b000c0c4a520209001248203900c0145030054283c03004841c00d001d0015080d408424941018604184207590311440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 171901339 1250 171900089 171900097
    0x9050a0504020a0501180803120103060c08090c0d05010f050103051c090806010b030703140405010b131103130305040b031005100e150307020106090608100b0612010509130f06050108070506 83
    0x4001c20083c5200d04100045480c1c00d00c01c01c1c41014401950408900307101c0410280000d000503907030a060075811498507405503070300742d41e18000b401160014880000d01c041400e02d90030405440203040012141400ea0161150054070341b01189014004418000c000c034003000e000d0a240c0c204186078450460450399100644a1101590001401800050b1600c402150462010300e00802d0440c5c101c1340c1c0146d284000c0c0c0d0210340740d80d540e000499a90030840300b11501840c14150802a007266031080350128030000300088102c1041050400c1054002d00aa4014240d400b0880b80c49203030075403076000411102e000f8603114070200c2e4007085070284200103141c50b01d180600380b248685141c4002c000c80b030f00007078002c0c070965407281c03008141ca505138858080101500d00c02040006a101c0040702211a0344240f64003ca100f004040c05c2d100060850034119407055940e00041e90b0745c01c1c99125050010030b40141484100c024201c140f000c02e400c1103069400c594140c550180d550020841d192103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 171902589 1250 171901339 171901343
    0xe130f060b0a120b01091802091603060801060506220b040e060a090204140d240618050c0f0d1503080d0e030a0c020904050304050303030c031b0703210f0c020709050a0504 75
    0x506a030050003151b9040d0044c203e01c481042a080185030130b1760000380c250354120340c01c9400500702d108100304039925020302c01c001c003c1c1e00001c01a00e41420085403e5200d40e401d188040e001559000405222000301c0740700410135a0241c0b901c0b06d0b143e841456907100155038480c4116540003000c1466031241c0f01304d40c100e4414200703200f031044910302070020854120030280e40e02080b048a0f6010f0760340301303003401c0b140440ca02c5001800900b091041c0c0200d24100360032a030286c0c0303400208003410000c0c0301121060f170a00703684103494040000400e0040c100c4487c1e001c01e40385080d00000b080080c034070040c24640e0384078a810700040c540041155074074050807034501c1c00294084007450140c10310900154005c1d0040080d645016204c001107440c560050fa141118000000100300000c102c2c010304941d1503200912552400c5100d85006006142c05040c62004081c0d1500c4000740881c0d95000c0480441c41c45003d201040080078060b403030702403604c50324034054181000280807100303034400c65101d15 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 171903839 1250 171902589 171902603
    0x6050303090a05300102070c1d1b041e05030105070807080115050405030625020d08070e040207020d1518020d11060714010b010e04150e130f060b0a12 66
    0x30b10303007000c004101503003034600c80c0000c4044281860303640244030126180404e0304005a6513070b42c01d00e04511401c2c803a500003000200304500c03540c0401240d4800c29000030b064100c0240314010b9508511851095034829041d01081c1440d5000000b4460000d5080356021402041140d44042d03080c0c3d5020021109400041c41d02c50043c040704030420f90491904120386011130402e5105d101103450500c0030307070310501a08000d40c03412841d0b40355001010000300140c80540754580c90040c01400859018021509006484181002c1a100c40c1d040e00c0244d07400401e1400161018105a850617000e450945811828882440d11280b0b650201007170190317000d0044075024039141c03a04005002c500d000254060400c200780d00c04559081540c0c01c840402100001d66804c4c1780303002400c48106c10503e2402641410218500c1508a186050445048a41102c0955a44100c104040307220020040909124940000c1800601c0d44022000720080d5068a400c90320b0320544828045048070003803100d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 171905089 1250 171903839 171903859
    0x15060816020619060504020417010e0708060a05130803040c0e01050f030a14121803060a0e030d0504050c1215010503031303030c03030b090103110f0108090a1b1703040305010605030309 81
    0x9040c0c80c1010003c416210000200d003038071280003c00780e80c02030b03208000b5000140820034442000303100718607100c7d0301c440017400500d00c0d24141c2916444014400022a9503a03400106000712280c100c0013017582c020101503580ca40352030088080e29540c0205100001c40000103d81401c0c0200a80ca02c03c60040040c02039000310754036510926020354140015005110003032600b400b004c0044c20089038821910318100070742e4030a00d0320f00080108550f4585062079102e00100001108035209880d078003c01258035996418268a49859406500c1d0885407141d10580b00324030200d00800b03411b01415500c442e50b6a85c408166a90003020030018018036000410030000740125011115a4402e04002c039003800740c0320000740c000c10240d00541d11281c680d0101c6d00e80b031500001d50380e41030000342404d0303e090428081d0079548082c001d00c000e00e14410000095542c0c44a1009500201813060801c090704040f101440d172650001e200803079281d070902c43c01144504d4080191044008003500030200c2c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 171906339 1250 171905089 171905101
    0x80c1608120f100905100e040f0506100e01030206130509090304170a050d050307030f061401030510231807020a021503250c0218010611010204140108090f01150608160206 75
    0x50a000d070212516800c3c000002403c408200161f030300c107034004c2007041007405c141d00307090382080070040400c50440070001c02846a1041000800d05481d0182d42a42d22402030f515100280070742da82025610074000800c20980d290008000d10603241503450b98a000382c2ca0068030355688281e08002400e58022040411000c0c0c451006941d1001c000e14001c2170340b2800e2100130007280c03000e4001c0320b05030500502c0e542c40c03560180a2550000d01060650b1075003403401c00690340d0041000c0c140710940f6030190703c0120940d191b2134070b2400011034850340c501500f4071490195442c031103d4030407409246a01d0229110741c0e10030041e28818826400c0000200e840c0742e0300c000c4c501c00110119828040015680e40140e00ca01d080c0f40b84203184900106869418008060034903026001c2000287e03004001c14006002c101d2240d042d06942800d103d00c090319a60010341c100000840010850340c6001c0c20783c180c14041640d1001101c015480b581219122407054843c0c2c00340382e54070701000d40c1c041008100c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 171907589 1250 171906339 171906341
    0x30c16080c01050910180e040309061106040f08030c07020a0807290307030513050f0114090724110f0a030f0512060d21030204081c02060106080c1608120f1009 70
    0x582c030000060f0600195484401f58004548143c0e419400541e100f0401d01825802c00080b402402590004180901e4a40e40c0c00c80c004334001c5d001000c1e814040003050404010205031a03900340e000b0081225107440d0345070581d6403c039074412040c4110034400d803426080754042d071200c43d240700c1d4480f944c07569403100c034180d02070a000380c001c003450340580300e03030307202107a814081001101d050b9400400c0b108640c801640c42d60101400c841e1640c2c01560040204440e50b400c0354640c18840390100c81c03400724141c01555500c0c051485503215006003180b0344418000031920f03045040c403a1f00c503400450f59a40c07080b10280074240c11a1310030b030b40c0b6201044203890200302c054044d40c400e680c4414a03902140c07070540110062010f0102091b000300301071010402c03d202c0920544103801c0c0401c07886030b4502c0025030716030041c031a4106000001c030118100b444c020302150b03685012201d03600c807181600d203410ba50b540d000e00310a1141e0042c02c030100301400802040c030342c0141c0810116004031818240980 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 171908839 1250 171907589 171907607
    0xc080c03040609030c0209090c01090b0c1b060c010c1809020403020a14150c010b120a0506160c0501020a05040501081501200a0c0e0f01081c050903030c16080c01050910 74
    0x213400e1040400c21000140e41b82001a44030f00c2106000d00b00094000c03002400007485900041c40c611014801c1c1d20620f500002c0c04a140c1c1912107a910444010f000030070f5452085100d0300c25907508103a249803d00c2d170402d00d8410700410f03441c0480241340d91105000c1c05c03030041d03010095200400050401400c0b0340e0f220b240d61002c4009211001d0b10145450f802410751001154158030794403558003030003914000f80402c101c12540390150007030350403954407662140d80c01004030803a544080440301c0c5480c4114104901300364003000031945d43c80103110260081c0c01600c107542c00101d141c0300250000c4059011801840d4041e10344401c6604451541804000140c3e407004192041d034850b60007203943c0e120514010000c15146071100e061010300520220016004824198012074065450061042c2d00e440c94421b50f1602c01c2d211800040020300b14491081091841d20a4000c0c807036400031040c41820071505404200e503000d20340b032801910113010704103005070b01540f070300c158208040c011411a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 171910089 1250 171908839 171908843
    0x10050711060c0a123f060806060321190c0f0303050105041b0807051b0a060204080d02061b03060109090e06070e0103090206220b04080a1209030224040f06020c03010c080c03040609 79
    0x30030181d505d0f522091007103905503032010569034000301c1401050708042c006101e00342c202080c1001100310b0820500d50a00c0b625200300c0c50400141c050b01d00a910410b0400f2020354072011380c4c2d180100605000703024103000c0c007880b4071441c9040e50190701c1103a00d120010b00005903031200c015660703070000151483d40107030b0200c404078080b9408203403101c0f40500c0644401807051000603299410480c4407407414041c4082c0b102950b0126042c031400e00112440720540064800c10309540c3d0752600e00403641c0054582c0b10203019800c00303803000c1c1a9800490010321600946c3c1e101284030344131100450596541100180d0041c200304800fa0078000e84806d100c080500f482c1c0c0c40c500070baa07140d03658515540298000c00c030541003010034108020040a6240c0e5007130b518645444d0040c2507030001610043c1d039103031070b0120700e07095122180b1003021081918002c1c580160348119480d61181c020391a480c0e041c40b064402d5182c2154043c4490007000814000c0d0b0300240c0560466a4035030341ca9004160107101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 171911339 1250 171910089 171910187
    0xa0605030312010801050105060405060f0304052406010206060a0f090b04200a08010b041508130611070512040b03040f0f120903060c090510050711060c0a12 69
    0x8211518200300034015a0182c1c407a1214940c5844125401c544041c0c20081c4205010841088140d45840c1a112904183c0000d01e81d00d8940d031038802d103030685a500d101c031140c0382003201d44a090704010140303100e82c20a03000d40303403295a01c90801a902810b401242c4040c40d981400b40450903203580040d2188002030070024004070701002040300151040015182040005079200c41c0035407103030b0120300400c0520245400d081c00c08800f500f8210010260b0010052043c0c001031800c4010780e1070344502a0040c00810002680c01d81c0126158040c2c0d42c1610f540c8111040910b9511446040300d00320751003405070f00c0c01d60311180c1d01d1280350001a0002d9a10406e14106400460b1070681c0507038040080d612003100e154174615003202a5814030104500340010000100708584810814035041100c40c07601d541d89010a140002410b100d44440e90342254022541010b840c1000851000e0940203407215440000010003c0368500030001c0742e2200e0503101d2580d450306500140a520102c01000c43e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 171912589 1250 171911339 171911351
    0x1a100f09030507030803070f0507110402070f0c26030301030c0311010203040803040f030c050402070203061513050408030a0506090112240207030e010e10080c0f090607060b041a010f03050a 83
    0xb102c51408030642c0040d529503c001080c44411070f00254400f1400d03605052090402480392600340920000031241c40c041c030340000750502000510103004045a13030100c60035400e5500d40d490381e0003001034041c48420000f0548890540e0800000a8a04032540888032003055411680c84c941119192400941548000e03c004955084140003901c0a011140c41902245103503042109000442e80e101c240201c0c0704100c001c1c05a140407034944d034410001480c40c404800c1c102c003c224482400d4210840c0c1902d00300a001c1040f0000c0700850280c90707400014850713a100c240c100418000203108040514654020040004800440101121070300224043d0141c507440b0007002a130784594011400601086210703d4550782040034039400880035070790540450201da10203005408003030040b40b580c6101145800400c42280229002610301614039511381c0c0041c039020000c0c3c6804440e03144135a040511425000c0c0e000b85001809a030165609030f80280203981c1500201405400080d41e0b50301d0710 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 171913839 1250 171912589 171912593
    0x30b21030f0d05090607052d0f0a08180601060f031104120b0a0f060803090f0402160305030f0705070215030402030114070c110405101512050f01030203011a100f0903 73
    0x300c06400700b200c0322100814189400c00f6258100200189400d00f03110041c8040d1002d42c3c07034000111410741c112804040195620b44080742240135803290218070030400640010b44650010446001c0c80d0790740425078034504038100e03050319200c0c00d00400000414003904081240d129802c210401c1614000a519160b165840c600c01c220805405841c1ca5170f5105c1884200b4550f445030f510040c0c0d11090800c11141403110721504c1e0b104690807648110184602600aa502c9904a03241d28842c585200d589012600d0050115002168241e007a03000010000d035800703000c2c0d011100400d6000307003a401c04101190303800800380c10181040e40c140d0741c0e43e003801042c6d2811500d014000d81c841c3e241c1011804480c80e000d00f00303810007070300c00d409203050000744001c005001c01d000082c1c449030302d0009a81d109840782140c0d100103014640e006641068144010312854500680c1038a001350000e110b12011014010080c01507405407940214400d92a980d125205107083c03001041c1c00d180c41c0180a50325 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 171915089 1250 171913839 171913867
    0x60e10050a30090302060a2d020c031b070e0106090909050133080c0f09041a0411040b0301090c0b1e13140d20060721020c01030b2103 59
    0x2c0e109940d00a5455140805144d010050160b20a00c0300c907050005512459119150020303a40e02103d4055414004c1c00010a0540542d001c072085c900c00c8036103941d01183c00418005070680412041c1c0540d00020800110803404107050740e4040e1a03d00350b00e864040604010b001200341504c00755624604441e42802a103803551042c411902c0410f080e03040c1c1100c01c1c20401c4150f0180845910a0321801180d4492908c0b420510b002141d0750066075a81d41082ca001e840c21510762130160b100c00d8100010845000400c60a00c401901d0421804070040d007414203c624800c406400540c0505040180203042401410080640e0013030000503a8482c02e00c8010f40c1001402e40224005080d0a0050203c4010144403281c0d0803100a181c020050726140d4841122204006940000a03101c84058446000302d51809904c00440d0b91603604a00500111511b0ac2e44110014001c1c100700042540c032900500348400130081140503484043c0b6116248461540401c3d1a540400c1c4000c0001180e2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 171916339 1250 171915089 171915167
    0x1f080610110a03020c0a080a020109050405091501030312061703070f0305040819170301030b070f031d060a050916061d041b030c0503040b01062006010f060e10050a 72
    0x4a50014183d0041c01c101b0050386c0490344d00500c42d01d40c492042680581e0f80281c0300d5045920544000400e0384510303414500705a1107006080d0a8020708000000b05540b0607002d2000740ba10318800c008030703902d40281d40c890034503180035074409a000340010804605c8100c00c8010300c034428288985030070354440d526420b0a48050b81c03280a6154940c40c003041c000501c42400c0d04885a1503200e146604603661910301b000060004000c0040040e1400000350082e030006000c0341c1088494400b855040544e0b5558160484001403880d0500003c90f850700350024034000d90114400a010319107091040c00c48408a015680c2d40070b11400c400103800685030340c80b481c901c2a00381d060700315461143e502d01406482c03c40d507801d420817604100708408620200840c90550310f451420944c04d010038080c4000c040700c46100b950b00c80c0144000001c09140d2703000341c841201c4164468074582040c2c2c2c410060382d078501a81706800309100300b08040030710b44180002038110070701c5a0390384200c42006417045c3e0a40703c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 171917589 1250 171916339 171916343
    0x308070908011503170708040605030912070b04021306030305040915090e0106060206010e010f030f03200105010f0608060a150909020f040e13050d0809100e0a021f080610110a 77
    0x400f900040c810700c83c80e009044096240328a10918029181d84d030000c4501c20ba10880c02000404030208074100340500100003140e800e06099a11031180b4103120080c3c040654080b8410702e00b09011104c3c0d82818081c0500704c03074050321490704042c40c15200701c003e060000e507030300a202c10041010440d1201d9204034401d0304d900c0b0f0f00000f121810064080c5c80d020f07040c1c100c1d90341c4c80540401000620018040141500d80c0400b03690f40310380507031138103860743e80c2600104c007203000c0ca58035500c0b04000158025412a035503d03230324140342e03950303454140d0f020701d4140d078000e400240e0403205006080307192050144035201840e2540516a0b82c22900c82260410300b04c9070115038001804000d05640c2542d95900008000c009014501403a59960f81c0d40301d80c140703810188445480041d901003010301c800c480c2408460300512100d2078050899407910300b0a0405c030710071410a001c1d0303202000c0a440324519440300f6100c40020b512031100f0401c0340c40040c10311004100c2c0e8420100340003001403058980c014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 171918839 1250 171917589 171917621
    0x50f030a0f050c07060c02152214130b010c021f030c0503060d02090c040506040b04051c05060a05060d0204020408010b0109050f0d0308190603050a03080708070c030807090801 77
    0x1114a00c8010320141072044050704016062120080002d0089125000c480081c182007050726190b02c0414030803071285807007906246012465002d880024034805c010409a050041c0155032118140c60104014200d8240c01c01c0b90000782880146059111114aa0050500164603600c5600040800706d1b061601d080c00605850b8a025a40d014003400c0c1803c08641081819450700310003141c010204c0c00d402070712401100c00828414031804045901a000c050401980c4545508a41010317610034070980d4055685600e90062005000310101c0d00c299100c80074103456210130b042c1c0005130801a041c9940314030103500d000016607841c4010402801f2860010820000000002d4685050303644001d004801441480d145a030b10260914041c90341402d21504035120340c40c42c481d90008400060407a14174160000c020720400044100010388244d40d800156070b610078084405000c29102000841c20b4160907100207070151040e9035000c040c9282210165641c3c0c803078242524840c038500c1c0001c07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 171920089 1250 171918839 171918847
    0x103080c0606042a09050402040602070810060609120501020405190602010b0108090d03020d060b04091e06030203121c151a07050601050405040f0b041a0a150504020a0309050f03 78
    0x5503806000860740004100c0d020070110030030304d428aaa03020190301d5070040c0d1a14418895040c2d028072182000380c00058821501c6913100c54006c0d50300c0c02c2c9070280e090184600c0c0d1007000082c03140e004102c1a251907646c1c1d400141e2030503052000e0300c004543d04aa095409010102e500d488082d007482c82d10702d6900c400c50b030740c510f810000b80c08c550300001d0b00c50420500a081141e184000a044151540c0500d0016560b03848039200c0001001c0030b8000e036015600000380012611980c0e008140740750013075a901c1d801501c00d400500129161840002c0d0103421500c2e403250540703156405400c0c900400030211140c1c44800000e1000c0301c0100300881c03003280c4d410006200b00c0b1001409005204002c00d00a89800525211280d991105203da14412034072503001600f00041c8800a48200b61300c860001c9540c01c20b032138290619019801480e071503010703d0300010b118080c9030045000840104c00d5041586041c0814000a03611031241101896224496040003e50400100d6603807400b0b5030142d515 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 171921339 1250 171920089 171920107
    0x50105040e010e0618070513060e06010503130b0a0908070507060908120301151115061c0206030402131d1c0509210703170c010c0305011a090d0b010308 67
    0x444440e180d10486980c548010f0381074001c07000031515080f80c0301c5d008406203584d44441451030881280c205c60340010700c51610881417040ca030001401d03194a00200302c103607503940004580500003268071000082c14684c1b2000030503030001c160b94000300700550210b050789181d281d511040d804050100c0f000d902003d410003d955100c0c24441c064056100a05410300042a81340e02c06d00060280d4114803054410a005450046c0412120020200300303548c10030340311000700f2100020464449016505041c040d02d50b4100c0d180701c00f580640d0040c0002d045071220340900041c07044060740f149099644941e01d400440c0e0000c4040c081400900042801c00b82c80041041542401c90b8040248541482483d003107a031042410104440505581042c0d4541280840c0c58060305510150820f808504188c0c1002e420500030a08a020380000740700641740300d01e045003100c00920810390640c003000440390340d0f4485440100f4181e00020710203400e10741a500c8810341c0300c80030781c03003102e030f0140c0014883c1c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 171922589 1250 171921339 171921341
    0x150b0f07060c0212040311040209090403020d030c080106090b0c010905101e02130b0f07020406151707050d090c05040c02030301060915090614160b34110307050a030305010504 77
    0x101d900c440d80b004e06420843e01040846600441c00000c10f1441440a6108903440d00e9061340c0b49402c0061a01c42182001d040282d01c88038404c006100080c1080c494070041800703000524100c811580c4c0b84034000e40342612a4600d900914075400655407140200030104000300186c201040e044a40041c602d80060700080c8000061100501c9860042c020208160706001000040340c0c0074504040c3d8540002e01c04d50840c1c03040c50300080d4841e240c580c0c042620400408a0740070300b50b00d51582070b580020800c0e01050340b5030485200000400c2048a0f607561005500181350389441030300d00c204a151210700040030f542c4441c2041e80182d01c0440108143ca41c010900c0c4002c1800340107003513001d0300d10351000300000d41a0041d042400744609011141c2c0460404640f0324410056409030052020314141c0b410480980d105480c2100380061030a840980c550b010110607000d9144400198801c902070f04c15101e1900c4400b0980024410710001c10380500800304080e109550004481d814101084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 171923839 1250 171922589 171922601
    0x40b090c09010b042909010e0a0909050c0109080105150f0a180b030115080709051005030f0a05011508060f0916090203160e010e0d0c0b040602011a19030303150b0f0706 74
    0xc0a445450500550903040000071110306c2e880038a41681b40e00001c6000c9520b11100d80c4c01985098600003115060207030100b410803005c0c0b4240c1c0d810307c041d076031805850b0076100260350501c14440804903944035481c007554072203009000034207079800b01a03a80364001e13401c0501c201d01d80c0f4150f89901c07210000d86028420304e503004010480c07035103c150400c10703995915001e0340618582c0c1a40d0304007203001401265420001400020100d0350600e28001e0f0160721a07520000c110350710340c00d1090008a000041707203d0000d46008a0092055650f544860b9052b4030307001c0c1c00f444c454015001554403012061904070040d20700c8200240c0c0d030341800e401c146e02d1684900b49810400566414108590380e1040c4e400010b46012503050302c62084504200b0020b40c665444040c50500020300044c141c5e4040d0000c801881c06031520080c034055980602114100c81c0549009015407058284002030181e40070f00d40140205107102c0c40c0076110345014841ea07100ca41c1046162300007050400c20000140511 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 171925089 1250 171923839 171923879
    0x4180b0105060307140c070f1203020106060503011a0304020d020904030206090c0103090309090f0f18060b0d080f031312052205010e0d06090602030a0902130e06040b090c09010b04 79
    0x580b8504d0503030001007001e40b502c9000e101c10300d000110051b1440c001c010b003c0152100f40d1907000c91950301c1420030404182d4500840140d420500000742044c001c100347c03812035089030b261408441044070521010360005000701d0780720180112410140e102d2145562181e44603400509039030034001502450414031240e0241010309020b0450002a88440104220b80c40700d240482e04da41110420006864005150300d50f9528201d000b5074401351924140f11060f0085208000d458055004d109104010300c6000c0d01d901d03420040074080040f414015030703100b0006460740100c070049039122000c1104418030103001075400b1031202030152a1201640c440341c4ca0384e450810303c5207000f0018200000800c01d203881281441e440000b40030f416001106500da01600465881c034101410400a203403518059018442000c02800804140c0c400c0000d40300302d1034000e00340b983c3c495076403c6c80d150006002001d1400382c0c0c5000541c41d2035070703480a030191404c001c055848605000c100c0141103c0100380c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 171926339 1250 171925089 171925099
    0xa1a0103150c050702040e0f0a03080a0608070b0f070321020703030e010b1f05043506071409040209130902100207030f06020315060412050616200c04180b0105 70
    0x2d0861015000740860340e4041e41030b100840d40c0e514510030581007001000980c0c440d4003d400340d10b0101b59005042c540b01d14070f600d0081183c90f8842513000c0e6182031038018002c40e01010007504061811401c00390000030710070310b4000001c17054800d0780d925941e42100324010301d41d0003144240c209500340c000c0c8048104800c00811034a8614000100301c44249190400310b091407403403d1030320741d05c501c00b20350103000c101d6050024400d0f01151400918000b000c410000d0942c0180182000f10101d034030750042450303980e6400400103450b035011540c3e00c10040141e210303500304024251600d0755043c10a00c80001100000c1000060041c04108050303610030004640181100740300082d000d80c01880d0068012034010385907030310b0a0400c400ba00709500e11b00c0d0702c41800b04000440007126802c14908030300c2a000c1c3c980035104c0c41e40d9030541c0214030007883c01240740e101701e15283d4100c1003400c2c140000d2070021140c1402c000d101040883d442c00a2014a1041540282c42800300b800c000e0780c010001552 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 171927589 1250 171926339 171926351
    0x209100816110a0b0705090406060908060703020703081f1a090f12030d1805070b0d0e0304150f0c021c0506090d021e0705091306050601021b040902030a1a010315 71
    0x222070f0f110078201da0001c0c60658404046000703c0c0c4140242c0d841040301a00800080307032980c4001c1c5c0280b00030321620400b8032480000440451081c001c0d15030583d0300d615a12820b403036207070803d040d2450f42000d445003070504020020b058410845000248080c0c0440c1c7c41c0e07500000c1e010301c1480d4403600089805625980a060b280e820000111003440043c81e50025142c030075802d5030b43c1118a48040035296100b4001e0105503441450001c0c031440041e030f01c0402a203e0007141050700d0740103a1040400b183d0030821091000c9028000a40d80c0d45001e18081c4d440708455800129a00d04052542048040325050407040100c00c205240d085071080b0000d005404540f40000e694065904822092403c03030380702c070259031000708400006803000801d6031419243c00ca50500f07404103004010740d913103420000417551650011450f0040c0744540040c0022000242c1d007800003030031001c0001c907018414807a01c60046034200c0151000c0c4211300e070144c5841e5145d8203004003444010b545e00703403810f480c3c16 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 171928839 1250 171927589 171927617
    0x10906080105010e010311030f0609100f050d02040905010c020c041116020d050f0a0b070305061e010822080c0601050303040b071b03060903030b0a080f0a060e010209100816 76
    0x181a8110b690901c1e1028000c0d00840c012006841c0075805000c050f003001c0305020500c1411075900f0b1240c20191080f11040d610344460b481a07081034844c0b0500300c005003d0a000c5403c1c1802c03d4090280041c0002c0f1301c4004554403a4211101c2190410050700028545982440c0c01e000e2008141008507580d801d285d81c0e0403101c4101d40d088440240f003400720079060700030000c0606c603d40520342c07c902a00e4035a8203d003480303000e068089030b440d0006031501c1c000586525004803040010300082c03e2412020a40c180151100207000e0b0081c07488000025511040c1c0c56050a00c1a81c28454a210394072540d50500305803500c581070b00703d20f00c280c10a103c1801030010041c1a82d40f5181c000c5a0f140d8109140e03014504e1821a43d00081d0901d03040040308024180c050f00100c914400075a1400b501503a52882d0715141e00c2c00780c03002c400d503070850072204002c42d25582248081c40c01060005161410003000101c00120301c41760200414140c0c41000400441d0140ca44071507101401d20300c18140c2c0407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 171930089 1250 171928839 171928847
    0x7020304030b060d0203010603290609071b11040e0a020301050f09031e0f0d09050d0f0f110c06041203080f040804060309030c1502071707020a03020108070509090a1a010906 76
    0x24059401030b113004501d101036513001d400c400e0066800c08860681940c2503d001c0580301c1c4c0e0702c2c0701000d401e072140000c030700c0b2801c081861038031481031365a90742c20792a0152180d40b1190000d5000340da0804070981394a107a03540d03e00c0ba041c0e451401030002c2808035018818035007501c1c0001c14252000c2514805c000780c405004c01210242101c201c0c06015004003410341c0b08183c0115202c81e0600c00cbc001c50240c1c3c03800c0d034551094070b00d1401507040700d11a0407000c0c811071f451003034100c2e01c1e03000400c80c2c603401d107019010340c603518002030395042640d1a400e14100400d00e81c0e08a50f00c00199120340610190031f02d0f4201c00382c01e41107404104460704a04e01600c542569200d24460f0004150381c3c0c5000b1401d00d8880c081e150001c40d4409808030345510080700250194109100c1960302e02c150007180d111040301041140c01d070700d50140c0450b204524540066492010041072042404410011710082d5034608943e148950503c0f91700180390940089802d00c5c1003440e001441c1803008108084c810741d070f00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 171931339 1250 171930089 171930091
    0x21340501140409050a02040302130e031c0603020d030305070f0804030c0f060b0a0303050901260105040b060415020109140a05062406040312081e04032307050105070807020304030b 79
    0x2800e00d06440074101c181d02001d4401e40d030100110038030b420203000c11404550020030403030b4002c551801c0d441035a62105401c450200b00101900ea200700042031000540b4502a110a010b5280c0000d40366540e4010501320a402c0c8030440c0000e03502d504004425401001d07990001e819031138480b94524240e50054040302461002901c60150654408200000c6410000f00c85074080d0104200ca5968a40906036800c4180c600e40466241b008a140341400c2410302c24103602c80c100c448a050b4a8401400010042281d0386500720008001c043f900702000990421203158990000070180d401c1e0402034100d2507510a03a421507002854140041407001a070950440200c000b5044510701180802c403404a00400b110f07000040810300000b800b9851445c0880d40b0303000c0e1511a01541c030b42c1070384a0b000040500d01c042c00c03c001000318010920607603244640c07480d22190200402c60080804110790040c410449050707440f48200310301107a01420044d0410f020303000840c2000d040d42c1d02e807040048 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 171932589 1250 171931339 171931349
    0x302130245130c090905010b1305040e03070804140301060b12040303050a1b21090c120c0f03060c170601050a1d0a060203030109050615030c03062134 66
    0x4030706000301c920765660020124504079030a004100c034050081c030103052141584201482c543c50302000254103c0d03280112000c2d45800303032840300b045041c842000b0080440c0908035500340300501400000801c54001000a019201c103620300d041240400c1609480d41600400c04c83c4000340b21400800f120318072443c0d08560b0508010415541d2903298500909040c054504c0300b543c0d0394684903810740c0204080503003090401d4034000d84070f4056002c0d02907513204080200700301d1b000300c4100b046200c8144c0d1004464400e800302c1e00c25a60315000942000c00c81d4200303a4106136124002600142c1003014002001200c0020070401c2c03410000207041802a03c583e0780500680e0050310074400c00840c505075407a2002080281c00c10b46410009549400900422100a02e000d0200d0228a4000100071500041e010310302c0c43c6903a8000b200a107500040d101c990401190f0000040d01d0f00030b966400d000c0400c0500410340146403052580780c00c180b0081d10b500ca042c107034110f80c0b130040065500305d05440e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 171933839 1250 171932589 171932707
    0x304060506040b0411091809030702060f0f0307120b09101701020f070b090607020304081e0c0a0b0a030c05031006030b03030f040e060f01050a02100b040603021302 72
    0x290391403002c680a40109914294081c1c600b14100840d582d0392006008001000d59420411120b545040c90250700c09944018050344180904001072500c48020192288a1500d690400368a80b081022079041640d003240416039042c440590500d05224209080c1c03021a00c0b16000d0130100e0f0440a220007030300604000e0341d1601c600030380c2c2c4102501107649082c1c141c0717030050341ca030000e08112000300401d5030080c4203401120041184244000180c030700323868511001d451072081d860a5440d4007200c107001010140960290141c8980d80c0701074243c001d15a04030380035502e4280c04001801c031000f010140c824080184284990b80d080b084200e0161822801c2c009894041840041e285006900148820190015000c50841041807800703001e0324040e11610300000d86d0740b00542d014007403000ea450060740104ca90264071030154220f2080d0100292001404580380d401041120700f41030714564910380c0004030303d07148941e540054400640c42c2030401900480e1011541c0c4044c003241c814407104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 171935089 1250 171933839 171933841
    0x702031e090111071202030609150a0b0a0803030906160309030509061602090103050c010f030507021b01110a11100c03020303010b0d1e050402040b0301051b0706060339030803040605 80
    0x1079001c0e03d91840d95100b60b80c02c07242603d030b69000192103000c2c0500124000d010b1b12003c2050f040c40020a805014544009042c280e50b070064458000c0200128079548880065000154104180300443c0105245c5c400740006143c040d0450703118105910111b000c151810b8443c602095100080e0741c0c00f00070850303250350703a21159030b0404180e80300d07a00c001c0d500030001c10000041040c0000d0784034007e5800e8889240c030001000094044607c111040b10140c0c1144082640d00300324840024030818050508291800c0640c54481c0340c541c0e01d0200700d40d884551002c2d43c40d60719201c007008445240a107004819410199002500c0340010b10816005000100310042d03000c100ba042960303101c1c2000341140c410350403101184007401040e24140e010394074140841e812414103000d02c40c0309045080186141d0b65030035011404980c8001c20a40311039949020110014800701e441004280c2184044022032400385c040c04180d001180d40e01c000403111a03002c00001c0c0300e8105032036010707030410800182 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 171936339 1250 171935089 171935107
    0xf07031107080607051e0f0a05040801050f040c090902030738280c0f0c1e0506031305100207050d090b03040c061b020406080102220506090d05190804030204050702031e 74
    0x41c1f800764600c25001c0310700200380319101a51050142c01260a810000e0116460742100995001030a98019000400d4030304180f00c146450b401c4403a64500c09401c84000b00d6484554904096446007801c6403003968840e450510144500d032140180700e6070300d0940c5021384100c0c0704500318002400b001605100940704481c03150003014020031882d0001c40c07541364038109184c140322903031180c000c0c0200f00820083c2481040a60b10411059800142203680365888840d18050452406807048646201d404001e0740c040c0460b001810201e40300b00001c0102c1e15195002030020700035034109240c0010107008120204218600071000c50308c850400f40046822001c0d4000505010340c00a900241491000160711304154010100700700c0d542410441000d90300c1d102e0058840d5440360b2076100d281408489280d00d4000000319030b6601c20f034201c5030004080e2003030382141110071809940012001c2130400039400c2c540541980a0301ca40302540c44e1001014040080449440c00503511401c00320724510 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 171937589 1250 171936339 171936397
    0x305090a05150306010c1406071e0305150112060314060105010e0102030c0d0315030503210c0403030905040f090212060103500f0a0c0504050705030106050c030f0703110708060705 79
    0x1241d080010b043c3c03801489c080070050211a0f03c0101141c4c25103481500c04d252910a202c2e440c010756942c1590002c903100d107030046803092550100755140380d60302c0380004002541c91601050211400b03025011661502c400501003840c0d241c0030780d0554004200c14140400c01049100095560b8100050b80c031a0010104841001d15000108584000980103034841d141c5054100e404c50814070a04441e41c1d0303c0d42900c49400342d4480140443c134043c0e001c2c022850720303411840307440c0105074002911402c96000206205c01016000c0380301d811100040c0305203d524441941042d10f00ca03c10610b0810008203071100c00d51a5004140f030030400000c08681c80d0840080d160040600c0c2c003243c29035268942c8550311185d510070101e481c0d90445000003aa030800e406450310854403a1078090842e841c2c04000d031401c0d41304512844050204008140f2450008400b070601d107070007956a0b030a4004200609441e05130550404003065001c40e00300a0650303844012202c10401c1c403800e05c801e50100130030543c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 171938839 1250 171937589 171937613
    0xa1209050a1715040303050f073905190b060108040803040641010e0907050607030302040b030708010e0a09021f03141602071d0a0207030c0b01030305090a05150306010c 74
    0xc040e065850040c8811705505070045401009a00d24490482e00d8420003134641001280d15422140d62084928401c2880104204d910070615400c1030f01c048010b5986d1030600107602241d8501c2e040206070b950511000504c601da00050a08006031103003002d44a402003400014801070440340c4841340c2c080310b41d500c0204c2030740c140c0c0001c440305003140701e0f5034400440c00d07a0402c14240c2c40d683d05000040d5180750701c072081d000d5441c09010344821800c0a00f03010895011180075010303d0b0302040000b0381c43e01c10400940c0b0441040c0d44040b0b065051844c8150395200191801c1400360500501d80007584c2d8003403010180ca281310306980c80061800d02c3c02d80c09440100d45c50181c00e0080c104000f40341ca814074103200801e44583c2524402c1381c40300b0027041c4014690f19a005010064000601c84400603801040228020305002e8103103100d65031000003120f0309030001c0700000d1011415002c00d041400c14040941002c980c00364400e10310341030040e03040c00010800790410101a540506101800e8644 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 171940089 1250 171938839 171938863
    0xa0b040f0e090102210403052107030f050c032706150406051906030b180108010b01020c01080907152f010e011e111c2f0306090907080a050a1209050a17 67
    0x141c284071007075527001d07980c00750403101d640102e0300303041c5000c0d400301d00c2d40b290394810440b0903484da003580c8030f0042c803840404c9244030b451484a903003589089011300400110b0311034122a00011024405142884152003280e03002ea402406203039140c40310740c10940004829160103240000c0c000d0745450002e008080f0240c40c0c400b00141540c004200c0c204190000000c0c1c10080e0210349110110000460329201c04a9001c62650083c1a09014507144103071070101c0d855840c1341c50a41d111020103244410751882620f400c80c22182e08020314400b5080c0aa45c0100321540020080c05003503284944041d441c5c00f000c10f0159903603081c0130161803502d00a03070b0903403510300107218150211010210000d1140304282c2e85808848140c114101154981000610128401c06803d607100c2c4010301c0031014001d846080d80340114400890901d07820800e45818600a000600c0c1c8040c00d8100b40c0e044001c3d0b000d0080070460004c00c20f00254a80d0600700c0210703405045200c68000d070041060381010240c1d209 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 171941339 1250 171940089 171940117
    0xf0b150607050105090118080d0c02011104260d02100203100801060807090e03040609180b100c03030501090204060c290f040209090c09150a0b040f0e09010221040305 73
    0x8075106000c41580098400d4480300000c00001400c41c104000a060300d560040c031584040006a0010344190428021003401303000102e0f540c2504151040c440d009900007201e60460b030000803040060104070410703c42c0411000e0004403030340840003500c40310242014021036800002245011203014166001418500d00030031003070b40c81303900c101d0300d805440c811a6152824090720644101010045604490458a84030310092801c90303812440d031004840345c0c40e060350b1040e580c9240d4603174100c0d0b4900004e0300d940d01e4440780c815240240071102d041c0c22402e461131062205004107500030400401140d00301004c290701038040500346034655010780d283d4000e180360009200c90001884c9036035005600c05c94010502d50b0f1101945a42c035011140b000b5070103071060b404140d68441030340302070030450703005042805c034583c5a404608581d17001c0d902010365800858400c008095940f807000e60002c20341e00080d40b40200351600e505003c0a9140310084203040d2001060405010784200c1d0118901510 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 171942446 1107 171941339 171941347
    0x7110d0e06070f0605012c0f1305031314041e0b03010212011410080106020307080a090e0702070510050a0504030b04030c0f08130f030f0b1506 63
    0x20a441e0003150400c080340120740d494038140d0b041d901500001c0303a07a516003040d904010b500e0788607803204904007580304100c1e10321401d19283c1264000e0000881c640780c1040c0344144a020780c0006100c0d00c80000c5184007035140d50350324030440e400341c0400048030308c008050105950f0700711042c2c015010f406c1c50044503c0b0080c1e004103001d81e00035000504000154007080480502a040105480c5121243e500d0b05d2070400c84401b460400c074603102c0d6080d4540140070b50360380990303c0c0041c017203e40032640550142c0300d561450700030226000c2c0540c0504007002c010f03455502c1350042c54000e464080030760008a0142e4201c3c1c40020565564914103459071b1905030b078034180640304904100464160501146071400c1401c405401540d03540d56420800700394814800c4c45e42c0c403e1344485e2032070700200003090b080100c9c0350f11203402c40c10148459442c226002c40c01c0c28007a0402d580440045 = true := by decide +kernel

theorem cover : BRFrame.Cov 171762589 171942446 := by
  have h0 := BRFrame.cov_init 171762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 171762589 ≤ n) (h2 : n < 171942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
