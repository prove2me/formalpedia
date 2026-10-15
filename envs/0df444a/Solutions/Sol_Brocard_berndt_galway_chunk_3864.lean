-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3864
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:53:55.829464+00:00
-- url     : https://prove2.me/submissions/f24fc37e-d34b-498d-9fb9-55fd1d53b2de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 694784172 ≤ n < 694964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 694785422 1250 694784172 694784197
    0x6200f0c0102010605040605031207031107090c0e06280903050609030706060807080703060506060d1b030e0f0327030a030c051005010608070e04060f0609180902030304030b0615040b 80
    0x41300403c0901d82032060741c00742c0c1c20180007032410281c0010403111a500c001d0341501400b0081020317040481003084048080c000d1103001069510000c2c00181c00202507048a0748280020300850821500704040743c92129180d21541910f10035100c01900c0410f1180c101408a00600f420000080c200200904441d440f88404101007641c4001c0c55803203500c90700891103503810000040000c0740441d04165001100100300da850684160407020451768810381170440044c0c1c0c58085200b694240c8502081d08119401905c400750b400d0304625200d1203400805810101100c1804141c0e000207100c8002001c0080d0848940d00c1041c10301501202100500300c8543c8a412071062400740b1602510f8121521307522405515240e03c042699950b4441c00100c1e0400d40e24030000800003810851200208060345864140d1410308490082c4944c101a00c00721041c140204040140c40c00030407502100c0c0c00030707030507006070311100000348031403102810026513000d01190219410410100030183d42c4400c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 694786672 1250 694785422 694785431
    0x219080708060c0703080f060a09060e04050d0207050f120709020a122003010308071b060f03051506090d0501060f031103060709060806040b0103020f030f060a0b0f0406200f0c010201 80
    0xe450580610481000500003aa44008640c0c040e6807e0b80d09900640e005004000041d02e81c06038000f1203885034002000b0140c1d80007800203006090040b400424801d102411180341401d01103811101c04030030540c000c88011001c00c20783c1030184440030140c80814819076540350242c00060120020558401c1c003245400e012000c6012020940b448400042c803a443c11607185071140c4a0740d4110703800607207900c100600c0d501015202c0010200c00b404903919404002d5420090090481d50000e14800049208290000003650340307005503022030740100ca0b000d41500346490160301400003640300407100000e0003000b108002c403030036100300f80307210550442d4503544c0e40c0b102c11605034a19100b00c40104240d280440c1d05400c1941048902c180c042c10702619000401e850a8501d0b4400ca07800d00d250801d1500b40035451070540c03072100c000d01507401c500342010009998030145100360310031441804a014160725420484000720030300b4098240540e50340241281c5040c3d20750441100f50303030040d46030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 694787922 1250 694786672 694786681
    0x2a0307050c180f0a0e01140c031504020c0c040b06040e090307141506120c150409060807060806010c0f050a0b01080106090e03040314031308010e0c04110a030504021908070806 77
    0x20110510401c80d82c1140200b589074192808000e0641715400030640d500c9241d400f0103001d4241710301e030049a0b01c01d030700390342c038a05074003030a211410442d00c15200d2070041100340911b000000e1a201840d100b1900058041c0310400080c91501c0b82d984a0f034110908101080030410300070000e8682c50703014900c01210010030711034080d180c40000301c10f010001001d6020604904001002ea0a00c0d840c130021244054450400500f00360340000c05c0c0380320103100103418804100c1074000c031801028207000038121035080900190106900400301810004400280001c1c0080340340504000c0c0e42007800d40311001c156050103801440c090048040c550708003140096880c09038491405150340d104080d6007441e0844c2d40d20641503900c854800c1d404d1000784600140000011880790040010740c0001880d0541e509055050600020b15a88110311b00221281d22054642c00c8030300d254024600040c0030364661000034034100c0e1258804080e094280c10100c0e160314006074610a80c0c2e0900200e8074142d58 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 694789172 1250 694787922 694787959
    0x30e07090203011a210403050c120d0e2107080708040b0d1b0f11010e06011d06040203070813140123061f050c030f1c0f050c2a0307050c 60
    0x50b0051009450119911711101ea801110400e411500c2898442d14100c40c501c0c20f03500d04110800c1000d101c3c4070000d00600310320518401e41c4401c100e040d01274000080c035070f0440245001c14001d1412240070004016040020450855629039030106040c2e4913a52903803030a0601e03404c02985600480d140000c04003a4140c080007140e003110865440c2124072081c60402c865820104080100f51344d202c131004d1100d0703031003444810f028080c2c5594203007011042440c005d1603100050005e5028605c100144040b1942c0040242da02071190070101c4d8a184803440d155010044840e0140700310351804040958000c400500410b1101c000011070149403a21410042c01e88030805085081d8408403c0c030040382c50050b005441c103200c4090a403802c20402400e408055840f005c0615240d0b404440d0004c90b80d800b0b07102d250805071090200300b0040c502005620f8052041103864190159203070303030350404800800e990010280c4c421080d281c5591080c5403003552141c2c81842c2c50b101c1c0c3e0b20001d281d13003c8003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 694790422 1250 694789172 694789177
    0xb030106050a0b07210203030906100e01210507032001210c0903080a2a0201091a04030213051608040c030f020a030203010504140f03040810020a030e07090203011a 72
    0x1400104030841c0b692070007000c0b8400e035201070000c80c3d010b01e00301d030b0402008181c41c1c15041c200d0482e801455607032400ca00c070141011030060108540700c404110511a40f416501c606042d25150005d0300b100090b030002ca1700c151844641e008155104640d00441000f030f5000e406203176005010170380101c001c400c4005503982600166601c441504417400382501150940190f421140d15003080f500258480c0c07261034080d40000040c50100304e282d080d41400c68100c0c100d01440190240720011a4040e0b68002008200d0301e10503010340d03600038049440c152100d03908032001540d0080095442401c04620000035100854044c00511403150004004c1d50040050720b22595008820514903070940e907850070f421030112010307600924580c0000c80182c03000d00c211400f0b503000d0f01180b0300c07004007602500d01d03282e54115070400340e80061201b04841040003401d00255200040301689550311080f00b10010250b03c280e10480b0720640301c1c0069814610741c0114140c0d1508034200c0f070304078810354802c5e140c0e2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 694791672 1250 694790422 694790429
    0x1020705060d020f0f04140a06140d0906180c090501060203070c03120e0612040204060f06090e0c0d0c11060619152d020f070602070b0715051005040b030106 69
    0xc80410103542c0d1084158001c001c002800c600e02030800c01140c2d00001e80ba00b0a400040160751058468461494074610076030080076546084400000085403a02050048043c1078604035203030780c4101c0402c40d6503001200c024540822022409145040096425406110700800d0030702e8400082259840441129403080c0c0012800760707018503640d42e43c50151311564880d01000340c0802d441ca550395981005003454010440c0f94429806c0a0041000722140c84c2d01240780003a41080403c56550800c5070102101d402507140c0c0120356858100501d1449010501a60742c1e140180030b8039001e401001032030002c000c0c5070460361156208420302402e1040e811a250141081c02d10403c07030034540c025080f560200b10311b001415410f2948116400074083d0220508510450120500080e410051030080c910054014240d00d490311070081d41740c100d90b026a01c42036000166440522505080702600100304c0702c0208003e00c1c10154115140c400c03402141c4c031031424995412401d180c140503e1064 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 694792922 1250 694791672 694791679
    0x80628020405011e030e0a2d0b1f050307060c12030504031d061e090f01020a020d2307060504140d02030606040c0e0306090307060b19061407050f0a020f01020705 71
    0x1071340082003c0c00b0420b01c604242c0040603100e45030542e4604007445180f042c5842940140c00100c0c0e4050301d250010711343d0100d0412180c0d28250b200109611440b480d030003108101150641c3c1000211102c1e003140d0350b40005405101e400c078002096a0b21806c0d444180e4002c941e10b03000946d0387c400450a80b0400c8e40c1c0600082c503500c5901d02d00c0c0c1c20700c04110703183e800010b1070301d4505003041c028851640b0001034410032064010844040508003800b0042c540e41c401d101a1064541640c0050382c1c41c00e000001500c3d240f4020760701810300000c0c0e00d4601d2146034410485811694802c2c008109501c10301407070311b600d4110049005d05040c50080b0b00703a82607000740500829510300313051000500c08141c205013001400c000281d650b840c107200140c0210010800340d0742c2c3c1d2800b801e28009480350b401040d8040c0300701c10740c2802d21001050f000025286c413480c10600181010411a8190080500240aa003c1d48807414841000012080c1d00c0d10302c241ea80d81503400c6646c005a03142c0d0003e09c100b581 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 694794172 1250 694792922 694792937
    0xa050904030207091e150e0a0209010c1104060b070b01081207050a14030f12160c0c0e06180112021906020309010302070c1d010f0b030412080601030608062802040501 73
    0x51070134541140c0550041420000f004400e40344240b42624202415241b034800c0c0d40e00c05101c0382403a40107480d808200420700f580350182d82c400084c403104030044090034030700620006d075016648980042c0c00a2402c5a4001d48030b649605000c0b242c41030a01c0f50043e00e108507100c14841760860015200c11680100151840042a8842c0007000350780303800c0748825003c1042074400d140414409045d4188100b11a00a54071303000710440c0400707244041000c10f04c011484080c001450380785050741950607040c064449901c648010805214441f598442e00d1002c9200100f044443d0010b8081194003c940e0101e004000490840e80003810b4014007006801c100030711105940290000c015051040c2040824203582d0100e54055101410b03d003188442000010441034050b0341c03028025112001c1014a1824640d0f41d10402440004004e8180302e00380e0001803d5a002c2e500c043c0040c0400b0066404503d0f0165150582a04c4034500b400103002d64a0341c040100b40700d00c251015070300c06850707a11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 694795422 1250 694794172 694794179
    0x6041511210f03060a150302040f0803130b0703090e150405070f050904150f0e010602280609060b0a030302010c0f0e0d03110a0516090b031c081503030f090a050904030207 75
    0x101543d100400c103e400c540595400200ba1252100200d81c0243c0ca90300182c0b00c034109008921409595400944186d00c14042d09082c121b0070501c00e0308a417a420002683c5810510b826104204164050070058941da001c00030084419000501d40300c004440c20080e0f5035400c0d80079191400d00d5200b010000d031003842195002c4c142603011042801020101e0303090b0641e511100c01e500309460308402200301108004120722074041040943c0100501a85da90440901c1c035211740340d1041000141225031035290b10414014503038000580b81c90050b0100204d00e0b03c0b82006030180c0801c0b620704c4002054884500d060500c54070a00c903c034000100900c0c0503903955202103444145514201945015801c618400500100b181c05000c3c0010300e070111119282100001c200d842c2c0e50140c50083d080340c4803031240701d1881041c488444040e8107040340c503521854039106042a00c5200d807500b51000003007172201601d15201a06803040308484400c0001e03122001c1c42003440c0140c4004005da8820a07091 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 694796672 1250 694795422 694795447
    0x90b070c05102607031e090b221707020d050d120621051c020a050c01090b12190f020711030703150c0c0c1205011103060a030609020604151121 63
    0xc03904600d13030b03280104440600d400b445504694040702110080c4d5140240010008002c0106501051090510a40807140184910502c5403204010315988605010598160f12181170303600158000c0c104650000261420740e81e683c1501c0380303003800300f2041d11640380c10308120b010704426501d1007001c0c3c240201e80c10954600d26103030380104071054041c00358401d540458134150401c00c00803590003800f00d0100307811320600f040442003080341040004102401400076810442e0041042e03540c8018140d0b60301c007100610040a240c240f011503092904040310085141c000e0581140209c0c0c640c40c01032144001c02d035071030110340310041a502051000700200045a13101c480701102c1c030305140111000341c0c0d0b10030b403108a0a4100307900288950799030205000303007445417064804101481c0745c0755040201c00140110038074403000340b03400d8a0b4059207045480e864280c40080c0f148414880e14124852006042c04007010f40c200700702c1c401c180b0203070511103074440c05286d407000030700e0514a042b1280d03025 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 694797922 1250 694796672 694796747
    0x60b180409020402040302040e030310080102070b0402120a2f0f0102061f030c090f050a0c02071a040b03010803040611061006081513150905010f05010c03090b070c0510 74
    0x341e0b8800e600744170010140c1c0740c9010301d0b00c03000d80050145641386403024a000da01482c0d5004112140c0c4180544c10000710076181d120f03005034045800143c04000000704a180c1410000000c1440c00181c0340e4200942c081143c4060085003e00f140c1c00840b0300d4828407900724040180b95005a00200209040c0d0a55502e1075810300c0c0c030f030700c80c508807280c40b611064204401c039848200f02a035900301031586403010384a05504201c80d54410311002200700d00c000e6a40e00c0354000c3c203007800028250800482d4100003250000c1010344040d58507276075111395064494001d4403400c00425841c54441010301004100144a00804003560b8452810308400312001d520007402e132014005c84050302c1d0500d41d902c042440c1c10054903040030407038034070012105599043c1644124100c2d410100140b0100300070900d882c0a44600b840d01c201d4240315410704441085242e4030004034140001003420621100d05101402e80e2826904d0144407001048115085541758000307c41d902d4042031444001c0b840b1084 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 694799172 1250 694797922 694797941
    0x101104090b193812071d0f120118170c0304120c1e06030b06090d11010309020a0b0304030207140609041d0d030222080a0b06240706060b1804 62
    0x940c45182c2007205103e00108985410303007400a020070004e0b84500b1180905500c075070989844004400146100040b0101101e6541c0c403614140d01240700584a4011302e00002c89500c00074454820007076030303200c2d900e544c41d002070716100b4080f42c61341c289010754021203401e00242c00003980b40500e001d030608041101100221000d241d2071000040850180200b280180315040b0344e00851440c0c243e014003100c1e100180e03030b4040c0c070b0117211007907159680c445010300c0f40750089444180c1c800e91100483c0140b04441c0001c1d40451f0242c1c020030101d000d4409584940c0c483d400f1a800fa0340c98070808852600741c0001c80340d100404201d0428241019042050002a41806111103500d075a00d03140c01c0c200d01000754000640d01164000c2800383c02405c01031264007c1d807010248a01385500c0548030044054080d03c108880c2000c90131a48500144114a1100c030302c8010f44000b041030444001d5200c007406690090402001140d44208032084071440ca06400ba0242c580d40c50f5002c0c0b1004d8840c1c4503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 694800422 1250 694799172 694799219
    0xb09180c04111201080d0e06131502030705060906040c0312200a03090b030108031b2e202a0f0106050118180905101104090b19 56
    0x10500c03001511180110140009010000d03511141d111024503c4032405034015600340e406000c540700e1700c1e50405040142c2d20007e4034502e07502c403954008803c6c0190642d00c400b02c00b604002009071309070b9010000c0c260180c0b26400b07a40817034031280b425640c0c854040e0f03006072140500e04070800c00203500030320b44c074240800d5040c50302ca8648544210682030b51100b99014964100084800c1015403081850014084a0031403a0541d41044c07400c40c0c0c2c0340186200b42c08003000300420010b00340e00410092003004151003200e00741d1403002d00040c558110950502021a043c00300080b600707105660f4442c0c840c1d0411003001d041c100841e002000264141215031f081c104040401c0304901030610031840030007589400481c01c01e06c0c0c40001024140903628004500c52000e00a0001c01259106041c0140c0391080c0070980040b6410090304140d040c40803240c080307140c0701d10b0f035011090f20b001a1045959004040040340c00301424400120614035903030f07004113004802800005a034a0106c0504020403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 694801672 1250 694800422 694800433
    0x12030b030a060c0f0e0405010b1206060d020a0302040302090a0e0c061c050f070f0f020c190e0f060306070914120a050a0605041e030f0e031f05040c06030b0918 70
    0x2500d90104a0f100740f0b00050001d4103075a4030100ca96000f1902010200c42a01c04208562500860180384c3c003611205040304031411004c24180c0e901c5d001503035041c2d421031408669031180f289025001f580541300032401040281c0000e044840944a502035902c07641000c0c0c000c107001203003002115840300880b074410605a1034103000500840c031420303114080c2000310107100d04001c040030700200c45e60300003d800c010592110500c90342c1e0115164503075030401c0e01c0540001100e0804012402019084100d19203440b004001c440d1010012403401039406400341e40e500d4844c2201228880140e01800d070618282881034803050802d8500801011504810385500d143d883c0d840506011100005544e0103881780c003030006029080e500301385c0a00c1a01d0301c0159a910700d607000f502c00e00b0b80c440e107041402140805c03d8803035182444094912410b4800810b040d000400a01c0020042500c3c251050805402c011440d10b00a00c1491991303240144000450382d03502c1c201d156204001c001000c40d60003007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 694802922 1250 694801672 694801693
    0x30b01051801210504060b0d020307060c060207140d03110c07121e210905090a05180d11060105090709030206030c16030c02031902061c1e0209180412030b03 69
    0x280c2620f02d50030702008010035907040c58180a419590b445840700c0c810121080b5203070050768006142022564a810801a4407105040c104003e0152860242c42c525250031400c2040b0004102c010310103040d601e0400409094082c1c80b441d071f00911281ca0456880302605211608141d041000309034451540385e00c0040040ca03210401c400040001c661190403a5001c1601680c0c11042ca099880c4600d09041c0003868a00050204000680a481c85503034400100b07807044505041c1c0145840110219400b031540030f94010482c105200010310b0740d0260340000700c0c0074070308480064040c81241c3e84100d1014116000c011951384040e003042c81100c410402c2440011450f601402d6142c0070761190280c902050050600b05148424030044852000441800581e138050540c3c510344030080d4541c0d11004a60441c00062441003000041103d12200002c0b00a9071b903002001120400d40d80d444920100d003c40c0c02c2ca0074410740f40144030600385c02078151414442d5001e019182002012031303600740107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 694804172 1250 694802922 694802957
    0x2403072304080106030b01150504090902061b07090f0213052107141008040b0a0213051f2c010309060b18070206090a0308041415091507030b01051801 66
    0x21591000b020759441e00ca040040c0000290001d004080031000d03109801282100100f00713201d2401500146a030790320740c2005544600007510240c40c00703e10a801480348099001340d0754582c0e4802d51020f5800c2900c5c070b5003041e0bc14000e0b1000940c10b80c48906c480360900007003044001d032064030302941188510b0144404242081207400510516400d142010008014458000d2103088003a0611420006100004440c090310552250b080d910058071544180076030601401550f0040741d1113009146143c41c040103054600035100003e4849907180c4c0e1080c016085103d43c881090642090082070924940d400b81d04141c000901c500000038608a0b0346c2c0c001621940002650a61010f15004000c1455010082260800200c0f001462610f440f032340d000b840d64400070801086110034100c48a2040c408104052401e10341d030307219403ca460018003155441801c0150607004642e1200800d200d90f000e4400d1103c540d1040e502d4a03d0000b40c0b024100040d210a03072003504008135000c84101d00c3d003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 694805422 1250 694804172 694804177
    0x4050a06031a1e010e09011404020d030309150903050c190803011e0f0801021e16060207050f011d01050c09150c0c13020a080a0b09010513141524030723 67
    0x1d1a0405c5c05042e0804c90f00c001d00710b804042c42c147c0942044d100380405a520703860324446a651602c3c000c1140020f5213071042c614001c07098104240c1342006096000c140d000005030400300403142c1110b11010210a0600ca0400016806485040100014040490400d114540396201920701241d065a00c0c071200c41d03010420342c460a480d9502150920b6109909541d5881000c45000307580d0410030b400f40f44151801a94500400c4a07034001100b1007040b50a103c1824030301d42402c020801c000e07107505c0b5016150b0145019071100e51034600003440f1040d042050b900c04c081701a010400c0c2d2608880c1c0c0e940741d40c3c031856840ba52440390f06c800990030748d40e000305912581d005801c0503813100c2c9814400342072420081d04800c0203034141034809405484e6841804e04696040340d02c0d1141c81000c800440050641d2407080714a0002041085160032206480690b409420f54a845085594004c125680d400c40a02e01d080e0b41820000310301800d114510343c4800c07081c0c80e5132011000082d8100c10400e46e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 694806672 1250 694805422 694805429
    0x40e1b0112020c1c08090f0d0f020708030a08160318021c0203060403020d09170c010c020114040b09130b01021e1e072c010302010503070c0f0303060504050a06031a1e01 74
    0x111649181c0790314656004603020303044400c500081080d4004c10700c1f50303515100302c1c49117502007114469416011501c00c02604005022840649a6449034081c005294100c103c1e030610032228261400d0400c103109201c2c00c0c2c1c042c003210b000303500441300580c2000b01107010038420192403540508840301503034040c4140c0b4003462180d00180a603510b0b00380b0152020b4101e5000d20025056440d02010450001c11581540307507091a05406e040c155100583c1c01d42a5050003940070b84001c01d011070181c0030701e0b00514414004076030036400c8054115036030007641e6a0384d80340f5006801c841d0f40440400b03908455826904001000c5d21111001000c00180c01201030625819070b5004107010019401c40310003900d801903c86031308030100c1c0d451406c1000d0034081840000d041080c0000000c4442d4881d100a10105610069103103d8541c241002406081c031030160f54425480d2001145111200f8880c0c0070850b82e0001c0303042102111620030110131000204140b00608642d1003001c0641c050420641c040e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 694807922 1250 694806672 694806703
    0xf1807020105160e0102060103120207081b13050621070803130e090d050a2307050114060a0f0509060f061210050d32030301080a02040e1b0112020c 65
    0x124900343d61019500f04411a00d0320500031948010122640e01144207070540b0742180d045500342c00c080718101d01c0c240182c6e2040c04079001d815540300f1100703400442d45150303800450b034078001c14009200c6e0504a034016a45180e100205071002c803902a1203101d0200481c20341d60644c0d40c645e941d0000582507a20802c410384c075492895005001903210401000d3308406904000e02d030700b5500c1c980103402e0340310350010b880c14041e00042d448240e0b03805440c50200d010850300f0b103076218019407805601801c5222030401800440380c0005030b0700e040055904040316503120f11031888900d00010f000c00c40c1030140030030350441d218498441654071450020108416101d01e07050385031405040c04074400b240c42c1c02442c450a41e0246440200d210300c00384030350f58103030380c6100d40300c412811280340d00340c1044491004407804040000540c006012640a0070a03000352000c0c003100400b0401c1c0c0c0c2d10380003081340300c00b5a408003000d4a101540b003108660600306404200500d06a099003510345841c2c40102201789 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 694809172 1250 694807922 694807931
    0xb01090f1706010b03090c0108184305011b0f0b100902091e0f0d06020a09060203040b0a080c04030b0a0501061b0308040b060316080a0516030309050f18070201 70
    0x7009400304142030040a503d00d0403403c50804c440099140d15510034118104441c4d2030121758040325808551032142981403c542468000a600031160102603130107800300440340204a02141c01d440c102c0010901c0300311043d2620342444010b4402d4000400041c034034020042c600b03c000b4414041e089410341c00382d80704203024a0020906242502160898681180113100310801526920304d0740540390461100d45001100142c04a08640b801944090784040300ca01008140700d02d41d801000545803030f554540515031503800036a40d81c4568400c01090510170040280140e110b40301c001e4024484104061526a4944a8112480c000d54413111050b0b130782d200401c29a5080200c020f24036101c02045881c5000039140501603040081000d00030184032000240e2554003405800c541c02038880040380201d842e03c0c1220707640c1c40211012102440f03181d0704880348480442030841102c0d455038900305400c1c1000305210040100d030844036000000104039840450300303110114400d240741d500004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 694810422 1250 694809172 694809209
    0x50d0f151514030c160204050a150b04030503030406020c12040e090c180402100509060703020c0f060408070b0c0307020a2d0f0b070c050307080d030f140a0b01090f 72
    0x110118041c2201000340942115030000b06600b58003a84d900c90100d1400c07540f94482202000c4211202d0b4030300035070140c540020049102959413027030b4404521104840c50068941901d02c640740f10718000601594014030014000030700f00c4e00145901ea00f1401543c101104d404401041034005070095413014001c4020040400410840d40c0c1d81031800322101c03500c14603020181401c0380c402070800f81c041d10310400c04502c014040c070115099050f0207031806030703159102d040003500d50084491462040d000c082c110581803800342c0648055a017484007170480c4929001e4100030750740c021102104103000504c4072401682e100da0a40f8000e00c040302c2111000c803480f801c9450328101002540b02e2403029600c4c180401082c0312052420340700c90500042d13540c0590f051030801580c46a0003540e03d880b607458041000c0101003180120052039480c240440c01c1c0d4503410205680040c064601c060340c041002850200d2607400c02428400e060408180e000c2d180d9001d10145140ca40001c2c0031501150a110b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 694811672 1250 694810422 694810439
    0x9040302061b0405060a0e03011103100303090504050702150910050f0108060703090b15130203270a1a1e01080c0f011b06111c0903030606020a0201020607050d0f15 72
    0x680c0462056464180303414113000028482d80a00300801040103900360192200c6d071425406507409500500120b0f40313031301e0400074050400b24103000c12400118010000070386400c0601555000700030a4001d802451800d483c41909240028000801849460120a11544c0a00c1294050f0710b911314004070941c10142c140740341c2a4064100410145044403c401190403050782035080a48403030001049104500000d0250f051540088056032000091204810200c5106602c0450315200c51290883e080070ba1a1200c0d03110402034039000c414041b5076020b09090f00c3c902e0380702d10300070808e1a0119418024404200e400d030840d25aa912200151007545451904000884000d20340041800c001403001c0500203003040f0000c1c0103e49440701c00340600400b1050ba0031701781028003030303400e41c0410f1036110026140e071000580109261410100d40940302080b030080c100d0701a0000c058940f204502151540e024034500d6920a94907030800003001030601981c5031141104007503030740103821301043d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 694812922 1250 694811672 694811701
    0x6160308060414240609220506061306050703031407080912250501021b03070314030609070c0501020405030106060513300f0c18050a05060102030708030a09020904030206 75
    0x480f107240903100304100e403c40380102260144405500300302602d42c94513021400500681003102d50040484d00042520824621036021520b0b100c2000c6c05103482e15002c8c4509442160306203040701007108024480580a200140203035482840c000602c2000840080709420040e200040050220028031141d110700f0050100381d0701605140610b401c092030980b005040803144801c00c000018201041844801e5055480174070007421456807492010340c0d01d0362698040d0004401080001a10190316184c5200340c83c4103150242c07103895180c923224400e850f54000c1c1c00e000c440c1036400f0080070031251405c0c0500c400600307064031195140c0200c0c4c5824070b40c1e10416000341e202e90300205540307010b001690840240e4131120070040d80c000c800b581070240d000c1445180140c0041480c0100190b40e07100700c9606881200e00d5902000280c80b0400d81000b924400c0e500039005920034000c04c17000c01d48010065400003d0b07081d0004e1440256404145c206004580079800b580003001000961843c8142 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 694814172 1250 694812922 694812941
    0xe0903090310110d11120103030f0206090102091503100302031605130504051905030f03160210050628030609080a080a15030609050f011a0a0e061509061603080604 72
    0x9091114a0b01076040d4a95070091a00c0c460036030b619900310305c0c401c4031002d0841301d0400c640c41c2c01004568490602604402d000c501d804010301c2018000341c1c1c4c3d108184240d03510100018400e24a0881420a1046640000d05610800b203450310000005070790030021202c03c0c10440e241c02c000d9511300000c01020412618078000d516041204200006001003150703a1125900303e01a4850712443c10f102d4994001c0000003140b5802c00001d200b43d0328200c1042d003512040c99800c4034500307544902901c0c15214180d540503049641c000302e0a280400003001d452074003109003440111540c0d6030715210195002c00200351035800001900000440d80a0600303680309203040d4090150b0b002d44403801e1401c1002c2c0c40092700c000e59070784c81d01c810028184a0f00031100a203000034482d0034403081040130303204645070005d48079105800f000541e6961507840580b02e03030b070006c0214a82545118510000754020000c2070b902c250104498419508220201140b0b01d00039a00c0040d88d00e80642800212000e000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 694815422 1250 694814172 694814203
    0x90b0319050a0f080d06060216150807050901023405030712030509010c0218060405150303030c090d0b0f09070e0c031614040603051006030e1203040c0e09030903 71
    0x195008007048001074460822a0b000f0101a6180d8003401c2c0b0090a0281d40c8410900d6400d09400040160740000c1a100101100250180d841d9454030b50000d000c848000361808183e446000504060061010f003080301e6041c0190f5000b0000c0c4014960020001c400b400203d990300f0801800c10900401214040d000650081182c0703804c000c07100c20f403080c400307000034204040010303501c0e556481824000d1101d0b80c0689251118031500c8803402c81c0c0041220400d008604c0c2c9400a40c1c0b0b489600c0b415212401c010300558603548512040e145c965201c540b59a8015084201040005444182c0c0e03e210700c03400401503600d4140409034038100081540300404160b04082408041240041120780205230705625150400d4030702e2044c0c81008104410381c040360740100e00000c0b62505604094899101c040000c8141900c0b00c90540440c0d40c900c150000f240e002d1240b400840c52140700071508a409442c0c23000781181d0312900e280c10341c201281d0040c010341000c0384c030700e04505080042c44040481b08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 694816672 1250 694815422 694815463
    0x801151a0a091814011d240108060d1e210e060702030c12010c02010b120a0f03051903020d0509060601050f0a030618021908040804060324090b03 64
    0x100c41c0142110300a010300c2d0f4004116054940e078140465102c080d040d9400030f00702200790780d198011640304100600c2d0081060151000070061403400c00400c8006d1034640f540700e41e60031000c00440325814014505038204000001d040c001c45c11528648800402c10b9443d00c00c240402c1c40c1c07543c0754003010710185000b83c40000410011710b806c10006102004140d8000740c40d8131807400040e2401300c0c18201c081d00104d07074000003109003106411210810020303030000d0002000c04414040c1e54510320701c00c03141d00d8002c1d440f0707030001541c1e010203c0c2d03059000b0700c0c240741003808042c0c100600340000245000841e9001803c80000321580c001c00364081301d80400381641c0e01e849000a4070305c0c80750a409a0003044c000900c0010309000364448030140481e44200b07240e407891043d0903002580203460422a60501241c5501c05d188685036052007142d002000030f0034103190441c1940a01034860801e6101006510030500700c400f100303030081c020f095401011034143c1002d0145420402d0214140c0240c0030413 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 694817922 1250 694816672 694816687
    0x5061b0c03040510030b0a030501020a1701180e071e0501120216060b060403061401030209091207060207030e0303120a0501080c0a030209040204021b03070b0705070f020405040302070801151a 84
    0x101c1550304a8009407410f03203810b402c01d50100c0081400b131000720f42c06201c40302d012051240550113064080110389038904840c21030b80400812401c00d100b0382550300c410510908410480c1d4004d81d0b00d2203100c104460000340c0b07659842e5a00141501a404071200f407103010422580e100d08015126080b00b03104500d80b600811090b0443e11428034050070b000c1c0c0f02c1122940c80d45400040714000c50f000325040001e40c03040c2c22110044c031800c1c402a0304c6101828040b40924038007280784c11040300216442480c02841c0c2da40c0748080e4001c00c02c140c0500a90052442090300c06100611000c40e184c21047c10740e25006910b803040710010b07000245981c1c0200300880c841c1c1c4503800090b040d6901201c80d500355644520004002c0c0c864007403c42c1c144502e01110010082000024003c05807040c1c9584140c0d41d42c20f20120381034050050041c1c4594044000303100541007a03480700390864020b00c15250500e84401545080d00c81d481c840e90a42c0500800811000f8603960400c50104024525103250480b03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 694819172 1250 694817922 694817947
    0x20d0f081302061b010204050f0307061205091005130203101131120308090607080109090c0b0c030409140f071206080a0809011706060a0c030c060905061b 68
    0x24014024a107400191242005564600e010f480186a90351080c1c46075014a5810390b010350010300c03030307103000348a03680e0f194030b0502d0046030200c01d0f40c1141d540c048046001d24030b100c0103008003410607485070041c2c1c4001d40c0d0a82d40c0e406032620804002d82d08090b48180c0c1d20506103040315030680030003002d03d4004a280e80300e080d40215041800708401c42500e90440f501c00303000d2004c003c51940300c1d11880540c0050340c00d1282070380a06080c0070351103800031503a0f10b0000b580c807080229105000034030810018010f0f048035901c0f030008a40510780180e009500e07010001405d03440070b511800c95500118080260840c13a00a45508000178065035034103051603400d10750441d00141c1444140090f4071041d62400c2d41a80c04000204410300807501d81e0036403402c2958540d441001443c0c0011507502d01150081443c1c00580e01904010742600d1414031a038404940000c440e002c11820841d8103146100805c10314041c804119000c2c2001c0c1002c0d0900f0f512200e841c0c000030a120040310000c0c03214100000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 694820422 1250 694819172 694819187
    0x51206071209020d0809010e090f130804080a050a0506011d071d0904031806020102090f0108040201140d0501090605061e2b02040509180703060b060d020c1b041a0d06060512010b01020d0f 82
    0x84400207024bc0c0d0035050301e010b400502850b0404003262042900103c180700002440381d051038007540980301c0a980b2103040ca5070700300341e6100c04040300400c1c2d40803907806440748180d00600000038801c1800c0312005000215052404d42d4242c0c0014840504846c2c03900705c4000346402801c403030008518090031407010031907242e000d07a0b00a040c0813086000030196401030220000020717a80c4551980c40c1000d1429030000e102c01c0c0074000340d840c0b40200100749810030500f1200405298101c00c41d00c0c031284080e45031964801450b0800085804001a90340940c10b4880c011240c0074032401341c6c8983c1480240424074000034480c03001620303800380704610150041944004d4a80100020540c4030b004e901050861054540390a600c0e4130024405d26050300108034540006480403081c0050401c0d0780820098234510a1071402503064200055101d15045034a014610f118803004211540c0e00d2000035201c0b441e40d6000b2030300ba510303100b404109d581d0604c14082301940904004803c03140032030b001050b84 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 694821672 1250 694820422 694820431
    0x60609030b04060b0303030705030a1803020a0605180304270c050d020c03090d2006031905060a0f180c140301060f02010908030109060f051206071209020d0809010e090f 74
    0x641c05100400c060001c3d0390020314003840040c044903928209490001c0003a44112916000e0501c3c05180d154648140c40d072551000750580e00405424040d40c44500c000c01c405003000501e5030484400e5451210300b40041c000a103401a8840c00c02c46190b0106000039921054103816145000d0500105580000990703d400f40700300001a00d44048409075881c43c0305000ca1664060b0780c410f00401040764210484120a40e4242240d03400c1910070148411400280c1e400780c11000316250813448420f940c2e0006902c5000204061003441d500d01c007584008055130001c0310140300c0041001c540300c0241c0141140200b0f40c0c130b04244500001c2c00d9840150006000c1c0c1c00410918403140c0c59018400d400c0400480e0300400d225569580d21000c2e0b0008110b54401d8061000c2412400546e9107000d020b0f02c002d186219026100c0d40c1c1e28203c007102c2a404901585800b035a440c002100540c8032513403464803403031003003000c2a512180c40e000508035203003105549100c1e21740d0000b0002c84280001076142c01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 694822922 1250 694821672 694821683
    0x91018060f110f0c010920030d0305160e0f10112104060305090114150307080f03030115020f0d021506121f020c03160221120d020c0d030b040e0106060903 68
    0x913081c0604401d4050a1800f20190095008001c7c43c0d102ca0403503070b042c5007044000c904a5030001103100c41a4107440741180d10351081b0118622100409014600314803176040000c1110541006000c000b0700c1050459003500002801c0c003008103040c20081020080524071307410310000075011b42805100900c140d009420804da201c1010441480342504000c0e045c0c154030010b8034584c60074070b0b00e4181c4110740c802d59900c07910a9071000180c0c607102094604610103020050b40ca5a800d0104c0c4d540b41403400c0118030114450603001d41d83c180c0e818800307a1042003465014000400414010406000c0043d0200788941510b42c0900b0031342a00092450303821040102e0b20303c101e540d0040840c02400f401000c400640000213484040c070040c416144030461086942d1440304070001082c1103041e40c40308600b0a01c0d031220700100704119000010741410500c144016181c41022444075082161604180780480e07120782040d030f818034150164406060140b40200202c40c41c1c0030000b00401c40c584000b809 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 694824172 1250 694822922 694822927
    0x20c010c0b0118060b0a0c0c0f03020d02040c021903022a010507120509100305010504050112020307030b19390e01050309010f060305060f010e040f0b091018060f110f 73
    0x101d01d4142c002c1401040e05171001d9031160070328240039043d00e0709451f08484440c014040801c0c2d6008088064007502d0b005421a0040000e660912004000c3c0780c6951055216110038503072000c041551141c41140300f81e000d880d20b81340d8a181c1235542d094090400d004d4040340100700b2505e07640b107001d680103030340c002440908942c03140c1e005a44078400e2101c82500305074440e031994035440e055044581220f0080da410000c6070b0381c4242030000c0d6000094005c0d49904a1402000465070380100c182c2c211080382d1413040300b0310900591004888200b502440658004425030080380310151121020380000129040b545880407001402a50701d440e1140c1409004404980c0200c4254802c1216411600081003100d07101e00304590746440440c3d60003155071700400003107030031249600524051a48042c1180c0841880d6698007020007000305a89018407815440b503140c45850f0140b101c0c08152614018030081d194241881514058086004928241030b501074600203d403040354074190101d02100d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 694825422 1250 694824172 694824209
    0xf06020901090b03090706200a02011107051c020111010b010504050418050313080f010c02060c071407030804061409100c0804080708010f0b042f07080316020c010c0b01 74
    0x2e6070300e02c154002c0c0c03422800201c100000740800141c88010b403400c07502c079182d00211010788500c0d841611042d0b09a01d401564142c801940185250b020400b44036050700c15007501d070030200c1e2010700111180599049c00508280c155608203004a44a0700418004d000059030b420029055103d0b501c11302c0d003c3c55560aa10341d03003110701c945603126103a00400b9680d4910700c21101003d8035580d809450000e003d0790b032308804060014400d6050180454001d070009640300e10b2031383c6041c0c02600c4141c40c0e0000f90f64010000110501200002d54814203416484030300300140140140194412040140001c20950000d40c1d41c4c02c1c1c5200e41c1c50a24074050391950190324001c000c5000d07075031110f4103a10641c07030003040d4880190806080a000e64104001d004034200411040da0460303210990a03400303103400c1112803400c024661400f811441c0d852442c060003651070b00603075031046501c0c81d60304101c00c0040c40c02d6507060080114030002441d1440c40d0003120f4561200e400c40610491082c900202c0180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 694826672 1250 694825422 694825427
    0x131110030216050a030806060a0c1e0812040312060e0109090f051006030b0703060308090424030807110d0b0a2a080f010609060212090301090503070819030204030f06020901 76
    0xa458041020034a0b8668600c185845a503a980050044010610210006d40c40b4104801038500100555448802c1c881e42611090303074052200c500380d041108502032000118244200501d0003403c605d642c0051841c042c00d00510402000c500310450a0034807100b081440b03103108425054400400c00041c511030540303004084500817800c002d01a004252010352034000c0761303001e542124041c443d605000c0d940c0000c22001c0f00d1450000801407803084c030060543e410070354040c0e0242d8078005045401000704500a81010441d82c0c41101e021a0005000e42008103800c005610440e0540e0080503420072550742402ca481e00a1250b01002e070b40d00c0b07a0503088a8132892000131a0403201031020390702c21203c00217008940c02c840d10301803c0080303000000e840344034404480490701503601070442e28280c02610341d1581e201c2e401c0c1c40e17415900c1e010f4000c00f250b814801421401d110301c3c00550f41e0701407d0b040c021300d4a058800801414418407003080442c0715603108071660740c3d101e1001a80d890920006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 694827922 1250 694826672 694826677
    0x3120902041401030c0902030c0a1d03060c04090b03030702060403120507020a17160602190309030816031b030503060105030c070609111206131b090203100e1311100302 74
    0x41d41c0705091641d4100e07200441a5514140c9018071840c40341030351518012803d9120940e0440c104000401c1845495440384507030200070155034019840506c100c600107481c1082c241d0341d05050b24400038042001c0c0e006403086001c1a030090340594104410740d000210030340175510010307000f400310f00e201242d0300744103200b00c0e000e4541c010084401181c442081d6080403001410b00c00880c4603201315546102040310f08078003240e1081d802402c415a00100a942400c2c80c03410480c1448551000403001407070274005401d00c0300a50f19080c14050702030800a1444c80302111103911240d4010301840401e500c9012a03500041c01c4c00c1c5181e0b00d4961078000403030707442520b001804c6d031460301c0030355020070441043c0c1c250780a40480f40640041d5005044030346074031066030304e9814080400425400154003000d640c10103e0260f00e170040b20356032441407400b41c1c0d20444100d41c1280f06a2030620203060b002d00e8540e00900503851941c00072909a8401016940e0054954403406002c1401544644a03804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 694829172 1250 694827922 694827941
    0x604030f091e03111e130b0a03110102070e010815100503031617090319020a0509041b2301180801060b07021318080706110c150709120312 61
    0xc00c80181400d82411880e14082e400116140900100daa0b0418a040440e41600b031410f0380354010700401c128100000401c504205184250700c810fa6511603036a101d8401c002103004042c92143d03106c055000a00342031154009408602c0f8940042c03040c0e240026441e0900001000303501030a0311040101c0e880c29010341d10907070380341c440000e1025405800c81881030074507101d0101480e5442030904d404106001d900c040039010381c88040005002201106000000c90018001c03628003034842d008642240300440301030b12a03481c00902000062914a1300800400c91401c40c0000300381c24888850741c0300e013070b00c0c2d1460411084103001c1c01e417035080149003401040c6c03c40003004840d0390707142d036019150402c65080e48516001645008004044e001d0780300c0124600c10078401e06c030210b594010460300310310b905a640707076540e02e0303580103c5104c44014968603c0110050940c0709140300c050803204001014403080041215080102c0301e90450b42c4900284e040c141901c940f600351050800508405a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 694830422 1250 694829172 694829189
    0xf03090504020a0f1e1d040e030705060f0c070b0114010306091d010b04020403030212031306060611010e0a24020d110a09080d0801031e0f0501021312050604030f09 72
    0x41c00c006070a401c0081100408003584035200040391483c241c0303031000d41141c17a0b80301117000040c0226840700e0245140140d01001000010140006210189103030021041113509601c00c0041c000c134040c21041c0c0c140c1c40742052074410b16205081e5503a404444062045100d0407504204841c200c0c2e000307410003030140c40c030003c1c100811001040b1003110500d0b00c129054142d4607214a46d009030406008403002c2d203408d60010700d0090540c80c3d000146600040c802d03601c2601d0701c1905c80004d541801100c0080c251551040700c9000b698103c07600719014480c0f1a18241d00a8038003030009100c07103107160920044081c6c03000e04840f242110302c01078401d492078000010700d003180690070070102e000601040d65081c4c1d2114005c0782ca0360301c4281c0d54044041c20320081214040104006040d0768540c0b0740e00092920f421194030502c1d9140d40030000700079030480307040c3d4000c10351600c0d040d14402e101f002030212409040c441c08180d152070707803030b03640150000e8108080d0542c905080d5001d85920740051030f0a5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 694831672 1250 694830422 694830427
    0x60905061617010b16080d020a08011d090a06180212160f0b0403290a0614030705130b010e0303030702010c020d030209010f11012d110c07030f0309050402 68
    0x200c403020410307000004100c01064880c03007010091842201d54a0686a031840c650345050352800d410030018012200456862604001e40340c1c0103040b0340080c18004803e070300c034805554105058441e0140030001c00c8862034608804100041d0000030b804c507102c41d00501c0002d400800b012903441802441500070390000401e2003914006100065841055445000e09140031500c4444482c1038040d148a040d0111000f80710500101c1c541c045507002400341c440024140e0702071503024230340190080b1940100d180d610001044800c0f01580c0c2120803480490252060a0070034000580d0744521b0f202188100d562008500701c2d990240190b10601c4c0d10060844e5140d1500c600c0080c00303401034201803001802480084100a4001d00079076080b000161600c09600b41825000c441900188592030300c20f41d255002008035880403e00c5071408050403c0d5100000d00c41c0c90448151020003070715408500003040710040340c000116a51055030790002009059465900701200c0c142860340000c6e42c040e100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 694832922 1250 694831672 694831681
    0x11a0a050304151517060a060302310f09020301060b091c0606090608030a020d140f07061b030e06060a2909060f19140301180e030a0c03090e06060703050706090506 72
    0x403804482c0b00e01764410112111640c801d100300080d01c445110085d006402244d582e00485014002081d43c0c110007011001c00c00202c03800d00303095806640700841c8107940d03024048150b080a010380710103070149201031450401c160010629a2140b039900b00f000351020001c3c001000f80c40c1e0043c10050030b00304800d104183d20703091000d49aa000680b07590151254001001082e8022940032100c020303c501c9043c2021741c2c10110044a82c0000d50445260f1341d110200c1680010303142c40840010b030307980d600241e0280094503d41c90b180c0c0140c0350f184641011841006100c2d002c2c074065030300300d2004a4080c80100c1604402d401400b0781840341d64003030000720f4102c0c56022003001030100001c1c00c100544150382c1c43c0605851000c5501c0000100c04010401845200750303c0703106407118461604001544000e030f440007400c640180c080500011420b550724418550702200c4000640310564250120341007000004542d48140000102881404100f00007031250661120383e0454112056504a291 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 694834172 1250 694832922 694832939
    0x10c14070501092108100501090e04031101050f09010c110a11060705070b091302091023040b0d0b120307110f12070812130519050604060206011a0a0503041515 70
    0x110f141c100030024800e0717000a00110410101d6108560040c4c440b10201403d00719040c40110008000383c0500c04101c08408008609200d042c1c801e90307580c1000303081da0a085c40a83d01b940c1c3c200d00c050003008031161140c80c600d0740100e0003083c0f503607028442150724040100425078500810780003a249000d030355000904000114018440703201d00b03c991201c00b0079840c20000480c01a01031841e048058a01005000c1c0c1c065150033300302c0d802581500c80000e80000c0c8212080c2d0258001114000740800c6100188442d40600101180308541c051203940807440000d03a0707400307a0b800107090210021a00e040382c0d03d074401485003c2c280649005081c01184641e559110300343d20421755507103c4c2d8244040d8024100302610b0070803000a5120700d220740740c81e0030821104aa030b01d0a9015100d1004000744580d02c1c1002040144281d40203802a07600d080c140c02d0600b204100d0b03001e0745030010041a40701c01da01c00b048a50199009040c20031802e104050f02e00140426500508415003900c0041140807 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 694835422 1250 694834172 694834223
    0x170f0a0608060903030105011803120e03030405151201050103110304030f0e06361e0a150f0e0102071203120e01060b0c070b1204030f020312070305010512010c1407050109 75
    0x2942038843e0270200d02c00c00440e070311000d0984406440c1c0440c80700300c038040a1007001c41300349920000303003240d0400703440700009100e0040c6d40300e000c00507840029400140c40c4909081900500090030100011210910103084900c0010002001c100140340b5a5403602e00890710b030011401c02529054a4107900301c038411105503244200861309284400041c0f0800388030039490410100070306070b40c411b00d901440da03c0c8032107002a012548880b080714040b501e0025800000400c800d19a50f40c2500300b401d54000d405074500f40d2071a0b0440d00100300511406c0b13480d600d50140795902d8a8006140c0c000c0041c00002000344d22800b03c081d5081c110001580203024000e002c0514604054031300b500d0361030680140c50f00c034411f644410444004005400309000304034034000d092903801642e10740065400c101c030400d08122021000704e42d44000508c020f0038410050440e80300568000c00a240c0c401802801600c000f80e100c41d8103141c0013511900300513080d00507002d4980d008082940c07044003525500b0500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 694836672 1250 694835422 694835429
    0x60e040c180b10052808041b12020603040204140a05090c09060d0201050c100e01062111100c05060103150534110307030e10170f0a06080609030301 65
    0x80c000855110071000d0390b115000034004002c041403c060b00c0da031000d41d16600030302100c00d40d4205c1c040b0001226401d0195020424401c0c0d40c3c1d901c0c003807500d032070458200c0030106081a03402e0b8040f58203202010b403000907900425012105551203036280d10001d00a000c6001a4080107009038041c804010b2141d040f01e07014450182c20340302c002416400780405502c0484040d94044010300001002d5401000100003610903c015540c5666007080008142d0344108280e46041c0e550307480401207114424006407501e1242c8c075090412820a03202d2035040b01d50700f01140d00c200903207055581c0c00c5006450089441d9808000c0d16400d6949042100c010701814100c15415810800000c1c00141402a04080d448c82c02145920003481154503030981f24108041c94240504000f000b002180c00f007000d045046e100b90380d0116525250b40500c01842d540544080c00e020940e80400034120105031201d40c01415219203911170b41d0740c100700e80040d01e9143e20040c0680985401d200c0b1189010000794140e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 694837922 1250 694836672 694836689
    0x14031b010c030c0c0213200406020c0607031706010504120c0e010e070930050a0201140414010302220e042108010909031e0309140105070207060c0501060e040c 70
    0x15004031a000c1e0203407800c205403d0009501d451660005140044c2c00c299019a98480000c1e001c920484d248810441c43d8140d60000202190070004c06504203d8080d5003082600c0f15814201203581c050001c800801120b200040200d0000742c40340d00c03400c1920010400c6905000011065081c42c007000207613805114200f8100400115801c020750440c14000c442e141e9548240c5458a00081200c222604204840310b40c0000310b210b6400c90b41c0080300c3c015000307801a10009500b4400542400c0c10f040c40134202c050300307110401c210490210710714017146080c200903a42d02900b04543c18260b003e00c001c820800fa00000100d1307a0300082e021a48039910a90404a100d51a10086070b4800703c0c01115100140000d030041c082c1c0700994100e00c1d0900e110382481c5503400801814400035a194401c1040002d6950031200300340203c410000d500b418003c402040035080c01c84000791590341034003610052250a102c03407410050250300550003441d039590550b106040038a80300d00203410a00ca455034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 694839172 1250 694837922 694837931
    0x60b0706090609060f242402070e071d0301050108030f0f1303060501050913020906010c050c03060903030912090603040204111b0c0f09062115190c0f05031314031b01 73
    0xb03000002035444001c1e02c3c11f42100500d15034030420b00298041e0070240b6141180135076080040c60349000784519001d0410f0382c880c07154040d80007a004000910072051070703129038104401048805400b0086449003d0718030b80159503a150100c223aa4140320311428800040304004001091110070382c00709040e900f0442c0c115407181c94600ca081d03811000100301941c41480c01c00855000d42c021000200703403070702c14415100854100800681812021514501e5030303000001007140901082c842075a20100651130036041c015050702140d402c0c04010002400703582d039034202e600c041c8255801d44004c0c5501412a24400740590743d010745483c3c521603c14014600406882860301d801e0b1500e6115000141a600c02c0c0c5040e6075250084052124282880f80030705402c0096a460780c0c0c9215100b4284809000c200303545080030701044881000004040000009429100560100c03c8030303040682c02800c2d070f0440c65a804c140c001c14040140c884018880015180e000350944121428007000340c100800c0b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 694840422 1250 694839172 694839221
    0xb0615091f020c03060121060f0504060605010f090608150619020a0203060a0b03060a0b06090315061918020a05040e0406050601120501050d022211070c0603060b0706090609060f 78
    0x199aa00203001724012044090103d01449004007403a0701c119000e0704010541010a22441082b1981584c0c285d40180c0c0341c100a01c400c2d60000003841300c4c1e05461900c03000d440d2401900074170402c1c0c00340100100c110b12904501d015030740c02042e50300c840c3c13011512880c46010b0010181d55000f1000040780240115000a4151545489021040c0314080e010f48500e503a80030301344c002071012000e26a4800780074032000c1c0385501c0401807070803a129250448003040c1081001c00a10b607250280b1064100060300d41408000715074485489806a807503005612091190380076100e502607030300034408000b2741e17a04000501450350000303809403100782c851000969001100c402920f070240611600040ba20b80300c40d00500305544101e1081c1000c1e002c10f498000e102484100380d0324400300c0c0840c1c00c1404140d01c01842812918000102050300f000c20040e4a070030b207000c00301e008000000d04215610034084003403280e00d030001c00310141d0044003081040001d008503001044841c4c1c0e819a000b10b41ca03407a9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 694841672 1250 694840422 694840429
    0x8210a02031012020103060e150102060f16140903010504030e04150501020705100e0406060302090915091611060109240302152508030a050604090b0615091f020c 71
    0x164040d00b504150090714908201c16198140b034924400c80c1096952800040d500c0b0013014014060b49640030545040e0303000c4030009143c624083c00050280140106108400c2c864002d240c61510032402c0c452a85018108080e400c4e00400201b5505942071200300410182d0142d0313480c15a480c112001c12031406001c4550083d0001401501c0c0980e1045009010f030b4500b013508401c10480a01e00721451200785070108084d43c05030341c031450100b5000f00d0b82121601c4e02a24690740b00b0251503060040c1041103001441002c40070300824902c1d2601511035940300d100340b514450400c44030007101e5155030b580d00385c0002408074502c18214002e55004040e0315560b40d442e030000300c070b0700240b05521000b214000d00304903910100c05241410108052041d0048010180d04002da02030540740d40c507407400542603030030341c0c1c00104210b100d43d00e4407075640001102445500d410440075a0080b078035042c82101d034000ca10030400398540c0710300724000038070100601b01400d84040c03510380d080e60401c1500c141030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 694842922 1250 694841672 694841677
    0x1090b071803060f06030204020c0c0f060715050c121608100303021c02030c0604050601031704150e040b12070305070b090303030a0e0102120f040210110309040b030a08210a02 77
    0x30300e00e00681c500c0100007141807504481c2600b400c132100080c00583e02c0d40003d007243d0180c0500545600702540e0030151b41307805801a42c15550030380743c00745000b101d644d80b4030003842004511903440f42c2ea80d01040c0d10003100000d40d031a10205c0c0400e03110b40d0030032a156940015030b0001c40c20010700d83c1c40c0081e0780307405203989410880b54150010041003000d011800e202140440488003144030910142100e0242045044d0080c0c0c0030308050076295045090a10041420003008034038030310100000c02c50311814082c0400300219a103401c540110b02500002d011b06441100750354414000062600b000d031001c12640f080384e22520440d00551b55802d0f224102d400388102081e03140e0003e000240940001e6044234400f403107200700051400b4600b900300382c008070003623800c0e019860b000400c02045040480480c0002e04040c28912a160710030400240e603441602c0c02640900c2d01c0c0c403200402e03524104001700c1000c3d48a8455910f07458083d261207059080207014a8108402801007002a10b0a108 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 694844172 1250 694842922 694842947
    0x506010501112d06190b010e1c0204110a09210507031e0506070c03110109020a0b0c03191806080103050d0c110d0302010b12011401150c050a0501090b07 67
    0x2d01000d003291000009915103c8220500d4600d54a02052021506215851141c80c807482004902c0715410500000c8800107041345050040c06800d9400c142d0b124045030090740340c2040c2001003065140b010801500303a0401380641910041816004590840d40b090140e9001c0e20741e43c082c0701ca100d240314112401062002d4100d0304004824400300d40c1004020009650340d241c1e8030b40e6405584d40e05803914408890180014000d464182c04250340801658070100c187c41c0248005041c030780004411310000d1190000800c0001606801a10306005030344650403c8078001d60104501d8030054200da00180c44000603207113400002c648640180712140c10703640c10a0042500000719070341515420080d5500740c1c0c030b0740745045001002d5075902d500312401c2c9129070b00101d0310111a10601c50115488151f2610356410219014030807041c11401078112900500003000004802e44250360311b22250304054002c0c00340c43e1042c028400150040d80380544031360701400841d56800c5044801035240003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 694845422 1250 694844172 694844207
    0x216032001120f05160c12050702060c03071a0a0e070605090f0a03060b310207060f090311010e01020c12130f230a03021e03191406010b03040c150e04180506010501 72
    0x191f984041ea482035000c3d0003280e1003e84164074188160b072102e86981c12251040b80d41c0314140d000000704e60000c1480300d4210b00742881c180030300e085080386d80c1c3d166440d90242c1c400700480400c5264860340c50001034106020082e09a41e100781e200d00b050f4001d842d4046225018041030040241c021032030506180722074820861419141c4083e811100c0a54000101519025140c20f1035401e030030364030700c02c0d00c14240c8a525600c00c51000d0794855825101a84c2103080075902c148030220b4100c1c40400e0345007001c80324244295480b07115460040259059402c1001f0b01c26480c0300200c0c0d500803c1c507003203401100010b80402804031000c2004161441800001d405c0700088416115050100c0c50f120281c00700102541c1240218081c0046401196142030391000320f180d030707224040d600500c01d007409806180030440c07562030183c96990819249104000c100000c102100740b02d81c2c4109003040c0c000c50010f20501c403103800410900343e00350344036800f5a0a030152900001c2c0079805000f99072049070102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 694846672 1250 694845422 694845443
    0x1c020a030203030708100302060a0201051506040501090509041502032e140126150a090b030a0b042a05010e030703020a090b121501060216032001120f05160c 69
    0x1a43d0440318920080c100740095046c0350340120069450030098400314000d41d00000e01c80c504502c5140400f030070030b000b1500030001004240034030790344458030005685d020f59440d5960703219071070318009806180364424046032003c8103000300c8542d92101d070b010b80c0d56100c80004603050002c0501d520b1511a103d20060b40c480b03d03849027401d50188001e040c40e01070b184410300e100c0400c1000040e081a04131a00180c4445c990050401450680e1010015055141040140345603401c046680e41c0b185103000f400c12406503001030100704054801002c001802004c0407070f04400914924400a01409520701040d0308602d000c00908000800d903007200d800800100d061341c41e052202c0b00414141c0901900140085510714660004010039403510701280d541c024079601d4520000e007020070401001691300710342c080400101d0380e1500c528190414900c40701040c80c81c0040140d5420042e60800950f4505140b0100000d541701d62155110b2041c01b15955010030716118111840c070045a401403021144 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 694847922 1250 694846672 694846681
    0x60c02071a0d05040501090c0303261302010c0c030f0b1b0306030703060e0114100f060c03080c090109031e0302070f120f020f090103052a06090114090a081c020a03020303 75
    0x4a8024135042401480006032820043e00c4035010a09141c000b54003203040408450088010703510040c042c0c07180880d44041e03a00306103052000c0c20605200c0641080340324018103040c49881204d06009591100103001c9903a040e02d0010991001200d6012503200c18054000c0034040b54400c0740c0c40744000070040c207180c0d82156511001404055021241507507a090b01c8a002a41050050701901c180b40d40784103c00c0c07a10703812130100501900a81d04000c3c140d07000300c000940141e5295001001c0b00c02840c0c841c81300c800100c2e9024500c0d0b0001e8000d100150942ca4040a007442004819000790b0903200c0054807440a400a45001c0c451071b401b4240c843d05100124800302c0d0f515030304904c01071907070041c1040c0000041030a03200383c0096030250000d60100000e0081d0010111090400305400740200c00b00c034000850030302a8000a40c1030040c00010514a0305000e0210b0340070350b04c010010500c540d03c80d080070781d036080c10600980090f0441000344a620340006015012580d151b030045203503917075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 694849172 1250 694847922 694847947
    0xa05010813030203040b0c0304150c020d03032a0f030c090f0303180816080606010c080d0504060915020a140922020d06151d0f2b060c02071a 62
    0x20029030a50850000b4000482c544a2403001825a4221f6200a6803241d0403c680400c151907454a0369040c0b0900b68003481c0185c84401380b10f0748154040c01c000901081148030800030140c0c00c0c004c41d40c600882c6500303a20041d0003440f02e0f098080742c0e5178200080340415100780c1d98503150303009590300e400c0842d5040000070b00c59041e403c0c1194102610b00792550791070741000e24040c4641840f503035408218505010b441d604001c40d650028003440c15a001d281644c454008034414404c001d008141c03190002400d11000da00f2215000d030b80b1501c0300700720311140084a0000e4101da060740707000440042c508a44001070000307894a911005181c20100d210840d030a113503c19100c01031107001c1fa002c1c0300b0b0002261440c0320b000010101c01e031450507007800c284401845054811a25500a050f04060f000c650f00c0e40c0246a04c00340087e5803607420b0f011001d1240041c840140152030a4101d6507008504105c140c0d000081c0050140d02260246915000a500308038646103051202442c00d01102a2000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 694850422 1250 694849172 694849201
    0x618081602030a02040510061115010302270a0b0310050f0c0915120a0e01022a01110c071d070c020d020607080d0b0f1503010308090a0509180105060a050108 69
    0x520003003c4561080359507020800351407003281c0341c801c4149291010044142c0000400389000c1c410310142121804090702891402c106010107070159420104030040b002690308000c021200c0f5101103207a1b49440e0600314090860385400038001d0042c02150450b481c4103000f403e000340c02031201ca000030b5888031003400c626003100119507406043d030100d00c8044070405008050880c183c2c046000b96160010302c1800340d82c00d490b0f11640301e0307104009800244540080c0d01c40e141c1d0400001c004070018094410f4090841c000d2041d0065400048403210403000281200894064800028054990a80390b90150204651100c003058104040c00014030b0300a4244580510041445092101c9038581052580109a0588d401c641d1681888100e24004841d4a40740034100d9500d0b49080d03860440000c2d03400103200003131610001059102040d514403c00070050280600500520b2a00d0812140360151580048540c0e5280102081143c1002c84001043d2081a11103000381e4652100034002c51 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 694851672 1250 694850422 694850467
    0x80c15010f05060a02150c160f0204140112030f050c0d020a0b09010504080304080703050d05070c0303050c0c03040611070b0a020a060b19050f150a0c0b16021903030f020d0207061808 80
    0x1046d0421000c13a841503802541303400103000d00270072861400a48144811540500b40180c0c150400c040100450740d1000000ea0780303254180361040c6943e580d0300d0250755034092280040203500824a40010b11039000501c0c50040380140c14013039481c0c84028403d4200c0b08103440181008004100103801b00c0c4c0d04100610301c0034824606030307150000d02c0d1411000c070394040d5200d000060601042005041d0306010702504083e5100d00301b0f2502e0101d04001e66a441035105142c1404030000e08400c052100b442010001c0615a407003d40e034042d4040c000f0749401c1280b004a941c246001146c58a0f0304100086050f440c140a6000381c03140d040504000b81541e81510442d072000c8a40c001008001140020348002c5d90070340c4840303200d20490702d016100b0543c018035940320381628024001c9210307070000d0304208482c00141c1016040d0442e003011000340102c81001c009103400020340c5640c000e0a64024051580606c1c401c228a070b0b112040c0c410604004180501340c1602400400354041340300c60780c603021 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 694852922 1250 694851672 694851691
    0x1509041205040b2a012d090b0a0204080607020703050d030b1c05010b0a06021f0c09030f03080f0105010513050103020d0b0d260a0219080c15010f05060a0215 69
    0xc1566481408209901608070098050f04d00d01450320380d000103c01101d4044039100091014003008002039040e00e072041c808246a03000d11404d50500140c039440922030903001409409646130200d50703c4065071188c8180142c51050b40006480d0320702c042040c40549a0010151070f03881070301c100c103d015042c001e00d1240d12030035002c41006c40a200c040c03100b040512640c00869082c0c1403c04001495000c0d034807440c10354002d014a02035600070540e09004000350781e44000340d81d659042084601e542c0d036400080c0118400c1411009054222003558070544409000c0c1c00315a8076200115200e003d0041410120341c03800b2018003007503003e5000742a05103450040064079030107290000c1c00381c1c958050b0664500c1851081140304010381c07550b420b80c80b072000308c2a928210600e01e00a5681c000740c45000a480354840090b0b0030042180100c9411100710021260405850f284071005a40c080c4100860001e0410300010142881c0050302c0c400c10140e00507010074008400c80b803181d800000c0100b0035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 694854172 1250 694852922 694852927
    0x201020d1d010c0c12031106060f01120c17090f06010f03240b0a030b06030d0e150306180124030c020d1107030204020c03210105060304020d022b0303051509041205 72
    0x4010000c62807201103203021347d544203241c2c41d03080c507090305100b8040d104074024855503a0030812a604105208000e082c0c5100000c0d20b01e22000f42103c40050007524921005180b10501c14400c400151280d40324800c00c080d1100759a0b14655a0001c03200da11005280581d0f540702c0100c1c070781504255074100340c0b240c1c00210b074990f81180000d842d07002d1a041101d50b903001405000040c2420004400b50a9660500840c0c0e00b050300009910040c9080b0001445580000000c465031903088245440d500904255840c2e541c40307110b1400c04861b01d4607030300c1c0b407070b10a010031009452290003140c4070400a50040c010007408000201d516441c0301040348500e04c1605070010040c1c55600c0244034210411001d10b4507540314158407050014003c00c042c4c2041680303001885142d542c803040303c1d00554100c9076012202e003188040741490340307514a81c00c513034180070f08000b103804050184080d040d480380d0f070200480d0340ca6486540c05086901407568100500d07a00280008210b0412600f16880310700b030030350 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 694855422 1250 694854172 694854179
    0x210711030601080a03020c0a140d0501020702040f020901030534020a150605030d0903030207140112060621061d0c0f0a0f26040b060406030b040b040201020d1d010c0c 73
    0x81c0340c01401c2c1d200c1a92640711513480c009042d4180203030b1584040807258596058909004081b0b20300704164000d02c20340c030001d0403c082103001d50442c2c1095038054024031880c0440075040000f50480a01180440c2c100000225000380c56003031020558108240c0c3c02142c035a001c0c0350070700818010315404c00d62003800c0102c1d022076000320f9034000304d41550b4004507646040c0300606050119a22061041c0404420203200003500814044191051015145da1090300c00d00100c03074403e540c068000d4114034001012074001c2d40f040ba10008003c1d42100624042e02049d440c0c406c80364a8452940048c00000c580070103224034003400c5800c041684c041906041c035890001d409139020790f80c000041801c41c4404801d081d0001c0202c4141d00c20b1400711a041c0c105110f00c00c02c8002d0051009100742d82e0390340000d080359074a80c88400903641100050002c0d24140c0f51058075600309a40503030162007900d001700c0c0503d00c90325204441842000035031004910746001915019141203080310f401d1203030640031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 694856672 1250 694855422 694855429
    0xc0c050303090601150f1d2214060a030f1403190c0203121801030b13111206040c050a0305090319081611070302060708040803030f040c050102210711 66
    0x21400b414101018103129458029401c8009460100d0341c42804012140c10520341c0d040030088a441c401900c1c0003c0c1609007070b0020703505100ca000c80054810b5142c80c407600f909100e1384401c2e00114070604800381c40c2c468500b000828580c0344401020040b843e402c14002450700c02007070168072015401c90741081da0300000c23480120038054034403000411420361582036103010002205400e0011010501d4a00542c032040b604a4900440c64103054607200c40480544403504200e0302800101c4041040c80010801c104c1d540d4040108001036006220115616241c2846018020300a03074403031501d4580003241c2603000c2e102c000c0414510340070500041d00c0300c4000c1100169902c42a568036281c034907210b02c041003072010300c039601c40800651500b12825500001080b00560390102e84640e1280320b1850000c1261103140c000032803070b000104c01c0c070411005590a1f540603d01c1848141100d0751181c00499855441111041400000030404040f0b80e40100003000414000c8207000042c1041c0400b2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 694857922 1250 694856672 694856677
    0x1b11011814071203081807090f021e040e0105090a0e030a081905040201022e14040312090803063d02010605010e30010903020c0909010b010c060c0c0503 67
    0x1d490300c1e449400301d400049420310480d0301500742c1c0c182000c507120103034400809510005200445000c1c000808115160040280c0c0d0014124a08240b1124010400c544040c0d000301c1000300c01d0302004030000d035884184000790b40c281d46412140003040c1e8038041c100800c4c4c0354040c0c910080b55580d200d4020000300c01748000d00003400b40b0740364249213081c044240c0c0d482c40301c0c20717000e0040c01e480c0a09100060b80d010032179502034481c031204024401d030074811140395005035051403c5981d10380040803004130000c8620601c40d0f4020740321108144132140d00c0c40165128038100510300d00c020400510203140a030702a0b40da103041d201944400c859111a030840b0344180b4036002c80e045101001c04400c3e10b40c24003c041c085c1200b071034124079000301030001c94079550818690000d4070184104017491200c1d01e03031102185220f03400081c002c3d109070341006921a280a6040c9000320090b0700041c0501c9014006c40e0008981139403810180c1c0850b0700c5620060a14100381d0003001a202100e0000c910704001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 694859172 1250 694857922 694857971
    0x170303220812070905092412061f0b070c05060f09130605040b0a140f041803050717030f06011107180b03010c030e060408180907050304030e041b1101 66
    0x300701c0c2418000b00103048021103601c014400c07200e0604107d4000c0d800300c80b1465481ca1080543c1044d050a00001c102015080c108106c5100700c03010440c69944102c0144c480c580b41d48500342d004d0307403180c1c58000f05124106019200d01e0807213400f00000d041800040140a0708004c01a0070038030084009440410111071420300130352234000c14407181c9428070541c104280300b101c40d007558070b2502e00b45000603207421030312603c9824180240e10040c4c5403a084403c00307030040784151516058924014041d90080f004c1910f6249040200070709000c0280126402888241281c0303055588190046400200340e01c03008082d0700406100090f41d482c0e8140381d601c0084480030201e248004030090608440c0c41d81c4240c030405081c0b480c0e000b100b51020807425003040e0088503640c0e90316074041148070f028140300c0d500c80d08090000108181d0b654004082e42c00703640320f03a5031020000301000821090317034006230884201004030b04180c0d075003900403007200c02080720300000413411041400350440c0d014001070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 694860422 1250 694859172 694859197
    0x7210c02060a080903130b1e0412060f0e070308120703050402011b1b0801020403110f0109060c08070b0a0914070b0306040903030b03060406020703080a200702030102072003071703032208 82
    0x444050381e230b0326440103190b170204098040741000d2401c510101a0031800c0c3c40a844d00340e0b5807903009030100540e00011840440310302114a259138a16040c0010360200071107180d20001c10700030448140c86130241500036a0143c1d01c0001390050403400c0c02c201d03481e0440484482c8060300354110f01a080045003401230215800040e20f55140d4100020f00580c4000c1c254410a1110303690310a90781c000c1601d00582d440e92074a006521050300d0240900d2103000d0300604a4229803007006a200900c2e046010701c0d0344913640c0d01e100b03811100d040b140d580c03075240224501c1503003d000103880b604056001c030100500900d4046001c1d0241d00c0841e0034803005840680e0b80a400156030303c149900126880e420003110718040180f20290351104e036a14003580401750b00c407600000d030300d425980c094040d2503a203904680300b00e509880f00c00329102d4511908880728064055224000360480015000403c08441d41d0081c500d155122400c0903c0c400178440340c09450000032202d0404580341d0000740c1500702940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 694861672 1250 694860422 694860427
    0x90c0602011b0302040f0e0603070e010e0402011106040507060f02070317030901061a0910050409140f07050c15250c0302070909031e030204050607210c02060a080903130b 75
    0x81d0040d0ba10282d190200b4203060040004111054003014103c0c11901400c10350181c030b1301c0e4100000c1c205856a8000300000d800d983c00800c00030700402e50103000d176100b42c84040150003070320003454840b102198064400c1c0c02c001001c004490245110460910440c070640702e82d644c50b9034442c011142101c01c00307000504080104030b2500001d10940c005821a8500b9070078030592881205a00e210f41c0c0c01c0c050146500d50705886e6414000c000b80ca0241c001c000007402152228036040d00140c0041741e01d20400341020011402c2075009000f00c0d2400e0300c2d407101030700916600c0e07490012000c80c003400401c0e203444d65100740701d030300880c1d442881d075040015582c40100c1c1c2c2260500074640a181d8101d4008245802401e60010340c1145107810480302e08000120000035100b07043d8024000d9501281d080b6100190901c20804940715009a28100b040da600344170500d00b04c00c50320100103e0000350403920802c4450340e82401003880c1035008512408503031810000e49003150300426160702c21914581d02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 694862922 1250 694861672 694861691
    0x31b1704081b100c020a0203250f0e0702102304171b01050f0105090609180615010908010c050304201305041e0305190507050a03020c03060a09020f060d090c060201 72
    0x540c004d24524011900c010302d0002c0d400e030006525040300318a85114a00b0b4a49500c9060850303420a90041c01d900b0441a981a5690b103041107a100c212800310041c040c032204044400c107184244030810940300e010080c3e04082c1c0d0300c00c00182d00040c2050300c20b03c5031540000c0a90a04500500c1c0c0140c0c03e542903036040441010036030030350b0070207011000100300b40c0b001070115844100d03545074410011a49010f40752140b004404880c1c00c9411506a280035880821584510380c034000d075001c440030303620800307199034445009003207504c010791120020700200003203030100b2005c040c40344c0300010740108002c01300500b4000030300400b440c003280c009050b00c1b0b071b040000780100c01c03080040099900d1700b40c0742c07001c0d1143d078014800d11480900c0e05091405074040c0d4500e520900c1611212544002250201900da0030060f540f907074802c0002d842446290700003010f903280c0340124801154050216000702801c1020010541c001c0084a070b20030380d40e507034880042a241c0d1050b0700140501d1300001044101e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 694864172 1250 694862922 694862953
    0x1201080106031b05030d080c0d0e210301181d01150512011a120c0603010f031106040f05090c090402030a0903020105060f1f09050a090606031b1704081b 67
    0x318a01e0030803a984440f01c1000b0645002c80d8804080b2050f241103c26596481c50044490003180402c1e4035030b0703150010b0a030618100040c2002030f03a11500b10140b075800c000380d50704114402400380d010009507024a0901181d80c54000308407542c8003558640030460391080d00c2c0d0860b2400103038440f032418003c0e002c0040d800c18030200d1880354541030007030001c800d00802c01d001000800105602410540b118410042c07000d12114458000c018a80f59580d42d680400003000711480c001030321031040c01c01100b415843c250080343c0450701c0456040c1d82483ca088100424260700406441c904041042240c00c0b5030b880340300441c442c0002d41030015100301203040081c00c440e0014081030046103110042e50141d0b03140c9a070043c40491070b03404008860030307030f42084410920310b40c460750b00023000400100b8a8000d0740c00103010f031015541c082003c0002c0a9600c0f00380750b540c4004002150b060101405030070010710090794024029003060b40f4115104e8920b07064203c0740c89a0342d120360442c00c80d0045045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 694865422 1250 694864172 694864193
    0x9071508071b02060a0e150703020102090a080703030801060f030612061505011d040b06120c04090c0504050604260f0709180b010521010501140f030a03050409090602120108010603 79
    0xb02049080020300d1001c1c2d002c6101d038400c0c40c8184040c001002d03000d1304075903035a41c2c00c03c40200b818100c1540711140e03458042d010307412080d02c043c42401186004681d900e0300003285021030343c0559480c81c1c96440d1680c1030300c08244107130504041503255400802d02040c000c8200d180705106e05400203000501820352440300c00d25070403040c1000304070360110307600892010350a03542080071200000c8003803004000908600c151828441c8441c400c03410030940c0803004c40070b801100c5c8040000d00a042034004c0440341c600c100e000f0164040400d00040c401038102014030454810b001891144809401c3c441501c0c0001300c800d11041c03540001c1d020321000c07060b402800c0c0e403250800d545507050200380d510002c5d40c4134140a1a4000c0f411102d244102c00c0d079022050014840e03581c000c0000c4c0d6190518007030f080002c410300071b0240c41684440180d07410f0005803c1145034241c1d4802e404c103403c2c0468013002d40031040003510099000c2c8000d40c990400f0b20303107690007050321100000c1c43c1c0d4030b1450325a41c0103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 694866672 1250 694865422 694865447
    0x51c12033c05241906080f0106021908030a090f0b070905060c0307111302030405010605010807051c201801020105160c0609020402160302060601020c030102071a0907150807 76
    0x2503042809010014802880880c2424902c258881001d10203d01184651200444420005120010020304241c1180045c0c0c0169111221151141e88810082c2d0752030303185e0f038086940e502c078071a03500010800707030b201442d045110004007085445480c0c6a07211085001c000590307000c1411014007032295080120030004000941d003042c10210101c0200341c5a000d0300703070701411654004159a180380e49058083c2500000341d0403c649a0600303090560003004a4029a40800d40e860003241106007c0c409075a120540d072085021703c0010074200b0000703045030300210f1003070750f116001d21582c42e0146e001410234071203110000100003031540002802d4840151004400349220700040d94002c0e031281c1d21400700e5800100104041d259032011400034450202c40f441220240390f001c03002c0540c003081407030207507109034221070400707440c0000c25080380700b01c01008100301303884a02d040314010b0b00700307000d0360100c04002524041580c4404a0542d00141030b500c8000507a44810045100d410450000d1078 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 694867922 1250 694866672 694866791
    0x61e0e07030c0e041103070f060f09030b060d0512070f0507060c2001020307061a01120513150b0418050601060203040e060f0f06160b01051c1203 64
    0x6807440e150154018002d0140c4003000301c0d042d0024040c40041005c085011074054100d6102c05c2c2d4030100344941c99200d00909000400c0045030a050901c5080d0340800e130780d00840e42040b0747d110802081042d409200c02101d03d4000d211110080144801c09055002e000740306007004418145800c506100c91a042881440b41080707415007c00c44400321035101101007024208003044900044c0c2c41c500885000800850a000c03030b900800038128841c0800c0070742a240d01c1c159540e007100c0754040c0c46040301c05108451224002002084c110000412900c0e802800043c820785940041000d940907800101d100c0500d880c030080400c01d04014840c01060745101544c2000c0c14020402c0d29100054089403040d101346141c03000700e40d07900c1e0170290341d0200102003994a4817011101c52075008000340a40762030810800000e20750071700e0005503200801c4000014103c0d030460f40e4030003841d207040e035102c0c040554843c140c50500805000d8110505003450682080503076000c03141e03880c0d40c846401c0e11032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 694869172 1250 694867922 694867933
    0x2d06070803130c1208070b06010e0609010e221d0d08070818070f05010906020109150207030507050f0109061a0a05011b08030109020318030a0f08060a03061e0e 70
    0x45400c0506590b04a0b5020740c1d592051261402c254403400e03c00d4120701d4041c1d002d1560349042012910081c15454403d568003502d5644003001503941c20f1040811b56005082042940d916600c074440c00b03020707440001c140200750030403000c444809505600c0c108450a903509c03615110b005407070103401d61200700c00740140a0f0f4a8101c1c00100368010140c1603109010300f030350100d40410030707115000401c58404403c850145980d0384080203c20160300c40c05021644004011801034410700468189d540c00408808032840c44401450080d8060202682005802d010b940b000030320a1061102050000f40041040581418542c00322032101440718640f15401da10842d803500d901c00c00c24201c403404d0903c0307102000c0c032001e07a5a2001c1014801030041e0030010020410328400c1d0b0140d40030f0b003030a01450480c101075640307081d030300c0c429072110780003013244d1a01740380700e0324410102a0360080025203a541c1a6640750340303400a481d00c01e4031040d0315013141c0c0e01c0007196403107510a1040080c0c0d900e00a02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 694870422 1250 694869172 694869187
    0x1002040305070b070c0b07020103020706020307121109010503040b0604180c0503010501060804110108180313030c0e0903040e07021606030b0114130302090a0902270a051b13052d06 79
    0x3070700c0107046c2c40f8028200b100890f00505580c040d605903000c194100c0c10540da030380f0b01814014402e071480194a07840628240300300c02c0c007140c0d000c29101c1104040e1143d13890350f02e032520f440080c0000140b80c69070250300d9012a21040780102c0c080010750380300f04001142242440105803c3d604140c00440411441404000108441c3d2134178200103002820036148980790000c0440e5240307a00c40000c03109105c002200300c0b02044800b0100201c0b03001c5c048004207261551510140b400041c0e0b040d403030961040c04284800c8400354140380d04145640103c4c2d4000c0c1d1804080900800d2983c45280070a41d141e01140d915604207400b1a140b10076036150910f071400800081d50400e80d11b0002074024860900003c500f18455400701e01543c1d002006801d00c1c502486d5505000e48090641074400e04038500442c0f030106260082501403540110049107800e9040b400345501e030001c800170f003110001050001015158a001846010700070071030304110042d031484032040022090365031402410200520f4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 694871672 1250 694870422 694870433
    0x906020c0d06113c1617160605060301050c041e0504060f05030d0c0302120a052218050f040809040f0501080705040b03121b15091e0a1110111002040305070b07 70
    0xc1e03440f0a0302c0d031704450110320541081000c0344001da2a4243d2440d00084e8010801c6080c00c401c6c3c1c050b8841c040601442d0b8600c4281404d0350802d8030415843c01042c002031003648409000445070002c140585954035584800245c159046503110045a12155100340920309040c41207400b10005030030700803d541c40a0340d000f5918550304d545094440804529640458442d404840c00c4a10412403290b0f00004056000c3e01c402082c1b11311035164081a44103050303050580600e5100c0c8800a10051040d42d031070311004e4155100902040c0e104c0d581f075000d461802c81601c1114003030140b140040075045d0070702081c07100b00c3c0d103030204c22440f96104401d80c01e4020620011600600f4401d0071402510202c1701150780b8092183c40381480c4203100c0c0f400c000c0312802c0003601c8000a82e84100d80c4032001d106245480d110f00d40c05002609500c11602c40078206e06103c6500415010a450110000c228000c1030034145106d00c40030005d1160005420800d11204000d40000b03000c80031401c500d03040c07150750b92 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 694872922 1250 694871672 694871677
    0xd05090406051008040b06010306052107120f060b121e0f151b07020a0e0a11040b03040b100909051608070608150301090b0112050d0906020c0d06113c 66
    0x5006c81d220700c0000d026030b4881d400c40d00040001a107141008540441c10520410800300351040c02d100d03507200050010120f00072003040d26081540c1c00c1058006848a0700509401d401068010440c0c00c5041400e440820500004d0b5800e0200e801407005c0c14140d235420021119940c40c116404808414004204540e0981d041000c01c1b4112016001e1004140424003440c03402942c44544c10380b00250294040640c244075100b9204100011618041d0840b12405079010b01208080140001000540b46840850b0008108001c90f21165a11500f0b00107403044000d08555035040030301c1304200c40c00309000b218040c2c121440941122070400300c0040c2032000042644100c0c03c0d00c800d1541c420b0310298801855a0781090400d113840d03840e8102c0c3c3c4c913401110b40048603a4800c0525600030a803040e20500c0036a0002c0d400b030318151f0100003c02403211000b010955400343e696001e051803196000c02400800c03100e001135800300000d4410541e4802160301116040c0b00d1203a9040d0b14041c85104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 694874172 1250 694872922 694872931
    0x6030c040e1009020f030723040506160b01080d180e1b0c032701083304060e180d020a08071e0309080106081f090201110d05090406051008 61
    0x75501210303640d00404040115265200541880c0300003800d03521500c26500442c402c400549604103007021456068925110207078880c0c0d00148240310030301182c60306100401240c910f10142c0c0c2107854503502c0e000d0300321100ba80704904560010204102130f030780210480400c000500f40703408a032881c1c044000d0382000000c09040180006980c510403210200041d2850119100c00701c0391640c03046482d120200100c0c918071801444841440e201540c030402106210b03000c004801c286510500e030a8214518203a12688510030351054106400c0d142c0780701d01001045182c98071070341800c244150505d070300441e082e4011075030400c0380b62950103074000803c500d000741d200c414a03a030b4250078246a800a4008040070003900c070803944020500d54003c01c05c2054074000c80082154603542c00740b0a5580c06c1c0070b0512800340e801c480f1a201e00300701652040158034010704103840c0d4016200c1c090790078a5110380244010030400f044580d51303030400788032700006071005640c0d080004c890f540f005049201c0050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 694875422 1250 694874172 694874189
    0x30206030402010c29060a081b09070c020418030e1e090402010c050a030e100302090a17070b0304030801090b04060303080406050603011107200f060a03020f070b090f0c06030c04 78
    0x282c1c080100480e03017001805041d80c00741c5081074208142002445600165101c5115550408000c19100004921401c00c98004040c01741051100410300c20507003c01418041031003007100007900542c49500854414624020f0442c8805440b483c0c083d00d00301e40c40138403900840720040d07070510007581035000c01160071080f51807140680d100d1004032130100580b40b00500c54029494420f007015044455448409400c4903c80441e02c0e4204007102280124400e842e4400c001c600300700010b466a6605c60406540b080a42e9142c5895008400c0164000d130f030210b0000c1d000c6e500401030102a4883d0300e01100089500b070102c4c40c60750710001d243c0039010384083c0c0801e030740d403000c20b0039076070254010424440f28040c140d4446000781082012407000810320075003140c018605200c146001d0b81d06400c100c01c01001c031414090008403c41c000d401288a4540d624400c22266010517044c200d8584641d90203401000140403041e522801c09908401d03043c099803003802800310500500c0203031001c2d5803112 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 694876672 1250 694875422 694875437
    0x71b0f05010903330c02100b0a0b070f060606020a031101140106052107051c090b01120c18060915180e010207080a0f1e140a02010207120e03010f020403020603040201 73
    0x4403120f0184c000c00802082c0001e05070130480700d0340395041c0c00c1050301641c10b800707441250040e00700d010103440c3d5400c01290310010421052040d101070704040d14a440c06031018841c800816600c1c40100d40711900080c1c05a80038120300d004041c1e02a0f9040002980d0500a1048801d1484c1c4010b1700801800303000203105022078180d280300171403803a40c622004502010b040c41e04160902038079641c01584200c04d6003158079100300b41080c45019141c802c9a002110780026071030001c0707110603849451001c50300c017804d40e01d00141c0e90702d920070361202d041034144000580e28038014a040841d0000003e1107a16650040d080020701d035226040d00d1054142c000c0490303450503030b02000b4028443c40da40200b03a130001003841002240e00c03400d140c49140b8681c5610510080c1e24003040c00314480c000d490000600613110750081c1980b020090040b0060750300000d1300f070070090368655001416284030716002800383c5e525a0440d00c0c0074007031315845144101085207010f003580c000c10400d1000070000781c10711018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 694877922 1250 694876672 694876703
    0xa0210090c0e0c0c070b071511030109140103050309150d1a0a060314070513080303041a0108120a030b0f510906040e0a02070b070809100506060906071b0f05010903 72
    0xa1400c82c90710001d03038235010450044615003e80c03458100f0700560000b5450017031310100b5030490400e11416250000002d6091480302c10070010003110040381000d82e00410700481d81c1d2103602d401441171524401d549000d21034508420b0141410b01503100004260034220005400344002c100c81e43c0150b01442d05c21b55810541d075160310300e003081e41d01a0b4210b2000000304020b00102000980b030a500050242d102c0b0390340e441080c0e80e00d244001440e0035446080043c0c41406010340d11900e90503034050404c0000040c890001544080300ca1a00104c60280c901503558401e034100b000c0c17440f11101d200d407424a207240382d41e550704032440074210144c2c540001023080e01940c03150155002002c074098220407500d403040f0b41002940100354222038981403940840c0945004140c120702c1013030130304003c1c80c00e20082001c85000d0309004d0078007134001400304515a040e403654402010014001c804011000110b98044120a225580004014003120005002c030380e82c002d51040449400203070f4250f540c0d0300c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 694879172 1250 694877922 694877933
    0x1706061f1e140a0203090f060307090e040609061d100507020d12060b04030f03020606030a0f021c02060a05180604080d11100218180606030c0a0210090c0e0c0c070b07 73
    0x480882c10000c11a912000c0d4004014201e01e001904e4144201c8050400c0c4641404180c88810105065002c1404407681007140654082d00030440030541c0c10741c540b0f0b200300b25840205c5900a95101c00d40703030704005404021211014904800411280c40c000070000e480e40d18400074803003040002500e038141441580c0283c1d029044603d00c1e5a51583c0c2c03450000440320441d0401c80241c040c00700041e1a9140101d9940130445c0c2010760301d12150701a038204060b00050b500c0d604030007500001000c0140c1c035014042c02c0d5528160710b540b1b90300c042810800420141b5030303003010300c900e800300070601484074081a4600c00d42c0c27540c1041d48119200803001ca00749005101d090241a1000c140c9002c251740200307411495040954280c0d0ba00e580866060070351080854206030030040030804520042041c10090040350340c603105494001c959560420b05447c3d0039007003074a195001d00c20610480c080a1105070700100c4104800b4070340300e8800e05198941103d4410000070f640049814800c0c0300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 694880422 1250 694879172 694879187
    0x9160b0d0f050f061905150a030f0f0e16050607081303151a09101a0912030301030201081e010608100b0d05090c1c080904061706061f1e 60
    0x1c140d04401d10540c030700400c0186003100112a2948200020007110b071138440754004041c140c6002403c4181c4c04000c0041c505030380d03484615614100356540e03c107445031418a03c10f1500e00104544041850000042c4451401d6504400b9019902680e41c1c1000213030f5582040b12034156012603040c0d1100108030785a14030316a030398070103401006507254010526007607500220301d90800c07090000707034030309102c09000d42d4000440c1d040848401c420740a03c108620414034100d100440101036280c0100791020a10515594620860070b61002c40140215130300700705182d5008000f0124000d0310300c9c0000d0000303a90101882450188200c06012070100000c41d07501030007402c1800030445d074030811440c0400040000700c801600034000c40c41452458503140311442a858248620381c010300b882600e0311003640e80310000065000d0303524000021a498040744d80c640c8025060040d08071803a04105100000030a503520004c607601d1500700403e06500301c9291920074003c09000001000c45c2030058840c41c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 694881672 1250 694880422 694880441
    0x60c0b0a02040f150906030905060a0906020f1605060708100905040203071505030702060105030708070b0d0204150504031115030a020732101a06070302030708030a0606030509160b0d 80
    0x291404010581007910540200d40780700e5940ca170b039000d5603100821000c0f2840440011700d950407150106200e50400c7d000b2280071401500e006180450f40c80748075800f54090b0f400c034001c142c4c00f0340c0c03000309100080c00b2181d031140480c01c11070514680003034181c11400403070080d0441076035154045001d5490400175000907019904998001c100350381c601030200d03001152088014400c1130008621424040340440032034031140020705896091a40c45043c2e0f81040b5600c1c0c407503681c20b00000507408280840c4860b502d042d616220f65640c11810441035400003a16424040c0a940b04104c9084401e00201c81d4400140d90005032500118900b045842c3c1c10300242c454000100000c800340e5198014080c8813000764001152620071801a0f08020340e1500c050310702030700440c42d001510509019000346126442841602c1c50034a26543d040d0307035900142c4110040b00d0f5500001c0c400150180715894001041d03000801d00440c8032400129142c0721409441a8103074042004141c80f0540c1c0c1040c510f4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 694882922 1250 694881672 694881689
    0x2a180f0b0a111c1707021b01050a1e111203010803090f0f090405011d0a0812040507090903020105060a060203092b05010f020304022106010b2a0706030b0604060c0b0a0204 75
    0x280c080300000601c8010700039641444000528017040300180005481c04180c12503d05409200340c2110040d1a00e030402c10700e5030f0030700981d0f0744031028201c03a401403d00c082032070b629200f0711a2812501d07075107890380c1240907018080c41000140085140082030720641c106c01c903017200d40800310801299200d4061f54038190845a60818481045010741108142d85004040511043c03400e4080d690b45141002018008440400505080688600c2115272045c010802c5501c0130b9900c1004204a807099003060300141d65035024400d042c0340407007a80c8003c0021388015810305000c03000240300d600c00301e00d103c140f02c500700c50340e42ca07050450001c8103002074000008002a07890b030319014001c0d5208403030492048084480d07010b10316680c42e030418134960230751740140300980c01d0180110f140e5101e0300482c003001000c0000d2a04454030803c82060001c0800b014000e01d519151028003030741d03401c00c45948039a1052209000c01548552084102900403d040000c0d403a09481c1d9002440f41e0b8009228 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 694884172 1250 694882922 694882963
    0x1d10150c021306090510060f0203040b041202120a030201090b0105010c0213050702010f0c18090513080a2f06010503031e030c04030b010602071d04080a032a180f0b0a11 74
    0x103620751b400f0521402c5440300d4482c038000d05210007007261288624004c000d41807100380000c0c81b21000108407004640e00c09812903a55403c2c100280345030000101040300180c2d141c0c1c203008100200c201110313004010a0038180d4102c0e0207a070024001005014a4a451944d20800150454401d400c101854a4040c40810441291420040420b11030f1300d000c40034041840f00004032442c0600c0740500c035118142d07000c10760702c1c150713038038508540d0002c00e803c0e04000d030303e14641b0181c0c0c1d1b51019100d610b418812008140340b240d405054200213050744198402e400c00d00585009414000301483d810b0280c605195903030b51000886a03040c004c40c0c00113030004640d1000800e10340d03000079603c41640c0d40968200440c503c40c20615a501038111030040401c90f00340000007805006ea0802461003148440081a0b0b0400744048544d00c50b001c0641c10002c0c0c1c100005050300e40c41c8450890251450445030900300e0700385034480d03000f8400c0015000400c42246d04580050380280100510395050518000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 694885422 1250 694884172 694884181
    0xc080f160311031806100602190f020406121a07201501060201151505251505010618080a121404090204030201090b0c060f09071d10150c0213060905 65
    0x5140610744d98288040c424040800c21501c0c01e2032500f0101c0d8480e80c020b182c0d1081e140c44104c1c058000d4902241c401b0700ca502a03100607a2640900c40103840501c81090b801502420594494004840c0d105800751400f030a20030415800704e40c00034055041480200d124491030000351610501c1000d100031349220400200b59154103400c80c80b02805d08580c1d82d1074168903520910b04007106440500e010031000c00c00c2011941003403040d4140001e004820016500300d91b02c0700791003a00b040000c07a45d2039540d6001404040d42226110f1250b464440d105d06485d400d0500143d91842c0781032010f860383c8910111240c4092003061818030501c0c00d44012030715280c0e1203001c50040c2d040f07408100d004c58481000411314004080580381c4499120000302500d449000b08600401070140c00740704c0034012494007154001c03940160b0101c5008060302035401d131400f508460040f100d240c0125188201c0c25203103030903440d40102c106040c203404603454114002001c0c040c0009042072b40c0092000742c140802c20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 694886672 1250 694885422 694885441
    0x2090a171e060901050606190e01050f0a0215150616020d080705061006140a08060a1e051c0305120a060e0103030c02040f020f1c18080301090c080f16031103 69
    0xc2c0e020b025464004c2c01261100070400c00507003d400f0000030062501032404d042c0d01c0c490202006064410305103941381000310804400941d01c068a24405a4000b06810842e00f01c5218101d600107c3c1c1024401c000780084000b4006212b02058030361860742d500d042505542d81da00b1019101a0711501d541d94504e01464910303103c401c201ea000c20150740c00100041e801b030180121110741c040b0042c05030300d402c200040c00d80b01d905028090300d4200059507404100c0c908804c00001d00e420f0144c0310a903c042c5028100941d4486c110007042d2080740c0c581d10500000d03004425110b01c030060300d030200e056584030f0f803003003000300320715406042c1c0d07605030100000500d03401185104ca99070023034038103101e650800c250013030591291640c500503002c0c0400c000d201c2007407142680309011102181c00305400c9030740441401c3c90189107000382ca0300007002004000c00c0c01a841075001030049801c02e9800c9141656800048204c0208010741d580c101541100c0042d02c0396001c0c0744440c021002850b06c0b4102292107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 694887922 1250 694886672 694886683
    0x1605010206060d060f181214090901030b130204052a040302060f030a0b0303030c04050f0a0321050d060e1801091115090a03030302031f080303160207090504061a0402090a171e 77
    0x260011a81d220340c007800223501281205c5086c18040c1041d201e6903c0c0d50b071103109040c0010144040c040004000301c006075180d0180078011f04540040c040c09081e60b2510342c500301401c0300302400d1040200410030050300c0301000c1d100001c4130301d014240c49644022100c8050100c0d480c1c25941404000f080100085d00c09018005031035080e81c1c040070740d041107000c0c00409010b03400054041c14415900b007405148400414a4607442441c04d05c0c205500a042d54080c0e45068115858800c0100708015015850ba40d501c20342108180081c01105030342e80b180d5102101071440c10b0300800d6a00003030b8103103842e10b0040301d03c0b04030b010b002c121540e85d8a04000307000350015a40010b5400c41c103402d40c5860024444c034a03094811101c0a149161603105d0b80000e014400c0050714294015480c0c0020ba0301510700c61729200380d000e05008034801202e0585403e02c581c5041d042da114a2041c0070881031a16041c0e9120141c6041c82c00c40c040f01d04050030168a80704510066002c1840f00d035070070000304400800c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 694889172 1250 694887922 694887953
    0x1140d120239040c02030904022a06041109060103180f03080c0c03030613090203120406080a06061209020609040f020c0d0305041e03031107051605010206060d060f18 73
    0x3042c0c9014031442100240d0103800c4400710110384050040c5407114685540f0044400e0024012640341401c0f5802041c203070382100c00c1110490075809400e5180481c81140d034401202ca0401514040c42d1a507107500742505050942030180c07111000145c0e42d6400780d40f10405081c8010141e0b100364005244c00000d00900d800d085000038a060080359400844205440d042c54865010b0b500315520780061110ba43d424880b001d101030b449078081d8000da00c0c02e0210300160424001c400d541d441c2000c50103000f04c0005002c8018551602c4820810345900003041d041e1301c180518042000d8595000013100b41c09000c480c50b07401440c20040c46440c1c0d4090340141440c151f07840565011078030034182034003251402c8502806102804945030329031030141684400d8a0720034140040c5500303240c0075031a01900081d100f180c096202c04034143c0c0540d03201034101e00414092005145e035150900118000c800702c0140180b4003030f00c407060110040c1c103903000801c12411030943d0704d1003104941803121400c001100c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 694890422 1250 694889172 694889203
    0x604110d0209250509151c0501240504050d0b06150c01020418060303020304260a08070b1003020307051002010b04110a090b161e0b040b062701140d1202 67
    0x2406094198051001d1702c8040c10700a119060a001c02d80c2d4141c5035600c0310403000482c05600b00911a41c010311720905010348030800c2ea00c255110200a0b4010607038400c00b55005205050000b00000d5031032018044055a00c4180e403515070f160320004ca84418a201080341072107138049112801c0450540c080d100315000140c140185441840d40001154a903010207001a0001c10050010541030010300c211a9034101506184a40076402b0f0303070512a03a60000c40d00450b002034050b0600244144080d00400c20000c40044a490750b80000d5840c8498490240036582c1800c3c010807040c000e500c61844240b0141041c030022562032403200c21607201c030308000f010513110710010824103841001c2e900c00c0380142c074102d0803502c016103030000300040040385c0c2106846001e1400001806c070310783d47ca00440c0704103103452843c1009810004800b100500c41101808070035180c00da6035401d000e03000e04450820101580381c1000174041000c00004540c00707842c848410629110071903001034842550903c04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 694891672 1250 694890422 694890481
    0x5091501050d1a0a1a0d18050604050c0915031b12120c06010e0106120b060d0c08041e030804140a0c0608150d02010e0111160f0905060904050604110d0209 68
    0x10040c17100d00015000311760302c1c0700c50288001d100c9549194440b8100d01500b040050081030300d5560586462411141256150054202000c580c00c0812200c0e03000291070000201040c6001e010903500d8598910549902468240300100707a100d100500c0303440b52241c2c00383c4001065039140103880b80d110084034075039442090000228540031420181c1654207c1e6105846441c00301d065401825544030a42da1150040207400f110816901c14a809080e007a11031541c030b441c003070400c01c0e400754218070180003403a42d0a0501000980c8280c54940c065440380d049100e292810b14428941841a4130040100d08400ca02194542e004048a84101d1f1820750030070094181e40240440d044d01000002e001c113400e80085a441d41c020b50042c0e00149a000c12240704403662217000c10003030704581c040c0c84240e5910030b05001501c00b41c06200e0b13100e0425039415000b820a551f64a03035811006002402a500e408420700715641e07522a44042641c004103000c90720b0034010b00d4502080d44c2800001e600c66501c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 694892922 1250 694891672 694891679
    0x305060909010903170403140a0206090708031911030f0301080307060c0905060d05093904090221010209270609010b180301090212031309020405091501050d1a0a 71
    0x140183d081c40d41c0e0690310281040b10b50480a0360710703c80640202c00744049049901580c070480d00180003001500d80c0101124141450b4441c108290358215a206400070404407800070718169141d6101c0b840e500e00b039440b0841c1840e0145c11400b81c100d9460866000000000d45c040d40003001d01000741c040d80007042423180e8000c060b5038402c841d100300c0350094800c1c00311007103d603001e40c0000d5000c207042c02513440e01c0748284941c08400b100f0101091700d1641880103001c401e1102d079a0b40c98000825541002003040b550006039804805180d14841c100249014004d21070082d019a03c0808000d0003000f1403102d00c45985584401103070880c0d1441181c1000180d03146004000c150484422145442c580928086128010510300e1105505036484a20141c0181c5a01c3e840c4005d102500001d191240c2503141407444902a80e03204544050040c0800d010641d21850300369000a00240206810246000180c0d068010000b1050030386103048403051414480d0a02c0a174060b1003200e511305421388 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 694894172 1250 694892922 694892941
    0x91203040321080a27030906030c05041a0f0409140a0b0f0d02040507021908030106091203090b0a0e04090b0406050105040e0a140a050607030222080a0f030e03030a03050609 76
    0x2d07120810000200080086a10080560301082c001c0264078034511100c0840340c040d50a01111990803800a03400701410004140e0600c95001c8075503a82c0340081ca05840d200c84030130009a54112038820032000108004044180740c1107900500100c0d80030b100142d00c0c0c6c00305000c4d6402c00c85075070a0843c1401716010f290307e8100c500c1d20700c01200506e810f80d013101c55000c4c04003d11004000d803065100302c00c500c0150b036008250001165205034000d42e52581071007030041807441c41e940480048408450300c880080c0d00040040251006031045503114014140c017201d840c01010070198200d850180b000081c001900740b02c1384a903000c6c3c00b05004907640d510074802125409414100c40b600941041000aa49244959100070612007100d0442290b41c54248c00c01005807540c0c80400d03030005119400440e82035802211a40c046038258800c0d1500411300e40b50030100d00300500342c540300c00c084c000309801034415450b10100901100e03100d40100f90040d0040c101035607000d1041c0c0e0207400091b050301c2c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 694895422 1250 694894172 694894223
    0xb010305090303071110020417100e0303070804170a030902033f042d08060135030d06030302010513020a030b090c060307080f090d08130203030912030403 68
    0x1c8410307005618540d1102e0045404408800c1d6aa03640d00802c1080c82d1002010300251001c0c1895000310719501d400002c50700d150680c0e9001411055080c030540101c40700b00841900c1c1e110505050111040c1e84600d412074010103035200700000e100d0041049080664594000c030b00040c800d030100d070610410009400c1601d4401804000100c9a40c100441075610b03040200c546400340184032400e141d01c8002c1e618007519060244040134a4007a0a4040034080110b03040c000c04690340a0031184d41801441c803400c00180212180300c0303042c1031f085151140008051360303000d010704c1c09594a41c00d5800c6d441c40600320a201c00e07001036080c01c02081d40814500d2684041c07030b60040c90003542a14541da0074641203401001d05110740a20070281c2c2440d11681c00442c41084156101100c500c0d00445025000c03001800c01691548008100109150800d101036041111061601001407403440007925510520b0001e940180d0311602c914148a070010241080c0c910411100581c080c91820140094 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 694896672 1250 694895422 694895431
    0x309061e13020a0e0f090d170c1b0a0813080115050d0c0902180a060c0f14030906040f0608130f060c0e090f180705030c12150c0301090b010305 63
    0x55400002041440495107221601e00d880034004094459a4180760b8081502c110b60844808090504005105800780700803c480c00d102d0803d4104145001d42035219848002d00b0030420140010b8030b0040800e814031030200310f01281d41107810311151361500e180745400410f281603440d2903801c4040b0f54160180610751000800e902d0031003e0174a80400c001c6c00301d140320401c1e07a03240c40300c6002181c1603c050006000d1541d00d0400d60241c6005c002c2400000b8560391f020f0010840035028000c000340c00e410103d1040c03504029040c4505145031106421032040410b81071b80040000780014121840300440c10441d41d80d5100c3d400c0a0751004900e584e24140c00c0c800401e0611000d044000046103580500c400490924010341c40e00303010000f1078101c031000d0312440c1220030340c4001c000102400030b0002541c1d45007800601a803a00d0700700880e903690700c0744020f20f10901250f940301422103010082c02c1c0c040c401d4000c5400044c20060810f1000f58800c0c0120700703080b41400f02c0e000c0c1b00d50081c01800d006 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 694897922 1250 694896672 694896721
    0xe1804031d091f120b191107050a020306070804110411040503010903030501050415080d050313020d1104061a0711060706021201030b010503120a121103010602010b0418030806060a050c070b030906 86
    0x13981c40c40000c12285101590341e046d40784e62444031035010a1258003405001d07109800602c00080940105031070414014810800c02407603104100000e032004110070702501c41aa80420748848800c2000b525020b03a400c031680640ca00342c110010b042e41500164100c034403d64042002e000c0c00d0038505903182c1a8081c1c1242c0341e1101007280301a5100350011903100b03075015a070052030140e9500040d4040e00d03400f419204c1c0303030400e81a904285801c1c0b052400403c1e5080d411842c2801000140042c1c2c001d01030042d10503a081c1c1d0a0348113640b03c290444110319845a0115540d05540720050802c5500713020640d8070301c41d00400454281800038000711039208003042c00e418000c01c03050032580750901010402215442d141c4000f12000715501950180c13041da000400c1445a003003d01040ba40c80039071124140003101554004a9046120746d5000389043c0d40690b91140704c12026600d610882c402e10340e051081500009804030400c000c0d6000784803d0058071000e4441e0f091094600a400744540f25 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 694899172 1250 694897922 694897943
    0x131401051f0809150a020a0305060a0f120606030b01260d1e05070f060b040c0203090a09050606040b070c06030b0d110907270302010e1804031d091f12 66
    0x8010300030910b466005050604844840d0485010142440019030300b81d2040c42e00482c5650380d550309070144640c01402500e11510f283d01d400c50362400000d03113105503503007490390107441414032449410581c051500070740501c04c0755a50789840d0350700c061280404201410031118050710920301040c43e005181c0141d554641160422404040711b04404450106100c01004000006801e140000700d0050007030000007642c0e40d00a060005848075007400318215001044100c08030744e910500b00040c0e802d078100000341035940001140c02482250080011020f010030344000300041412200169211580c0a0184003684000d004031b51402a800520414610201e80182c0c1040250694440840c0c540310000c58091150070101e1007214140301600b140e042c500344155600b200700c0810041050f0b40420304c00e41c503140d40c07418521010f40700508009001122b45d031000e10f2251f4452a10030010101c804500f051b108100542082d0b5034203030202110040700141d050406006440c1d150782210300d01c1c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 694900422 1250 694899172 694899229
    0x24011409040506121507020f07050603010b030a0b280f140f041d16080312011205010f02210c030903120a020c06011523070f03020c13140105 62
    0x140000601d004d4003c54258482e24802c2e0303080001ca1196001000900d00c2810709680003818024180031b00601d941c01044100565100d5504603411034010b400419100d46801c0030500c083c10f01e00710200d034050000781d0000040300c80d0305610000005442820324949a8540684180c0342c07151162242d05d0345841d00e80b0742c2c241004460440c18680003000013901050210717001c5190070b00782d06c0d100029400040d020480b40c5044d0005401b034055003004506104404919104c1d40105006072059121540c41d41403c010003500800034100c10010150340b140321300e540054100f0f0025003000101c000c481c011542403002e04040300d016500090243d40b404400c0d0311a0456020090654110726138204000b803c070035000d11900d406480c0d110342560300410201002001543c024001c20045116611281c2d22201d0b801c0844041c564802581c0c45200c01605003070382080815011680c120701d40002041c100a001c0c1d000010101e80c0000680590340c0341e6080c081d41c0c09512030912140102c80e060503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 694901672 1250 694900422 694900429
    0x60f0c08070609060e010e15130f110301231008070603180f080a08100821120108010204170109120e060f0a171303140c010f020324011409 61
    0x100740e914011140070400e20155035880e4101ca0b100f2607584406c0c3d66404000c40028401e0041002523200c45070000c5085c14408610310b083c24171840300034428052100000204140710340042d400c2527000703008201a0f03920440103600340016035083e564110000e030001d010b015a24402078183d85004008000c0142062002e4008002841c86005c1c40c1561106000001e1410594040d40c03030302c5a08140c0d195460500f014011a0003d000440c0d4030240c030500307011040340050440c4002c8000b241c1034203070414080074022503200d107040070070b0401042cbc7d0011900c064150018802c40e5900c0f6013008031000e01000141c22034103480300092055040000580c61140700c0c00d107034801a0002040d05103882c0042c044400d00754464003806011501c800c0324000c00b40c15520213a5440003040c1d440000c28542070703600801141034800002c910308004100c4c41c0b0320680035800840d403d0241c203011580e0303081c014100d1020001480c0b611480003c1a01044c01d40d501c036054030406041e100005904003403040042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 694902922 1250 694901672 694901677
    0x5071410080c0f1b0318011b0b15032d160902030621010609050f09035502030a0507060b030a02060703030f06050f0d0204091403120709060f0c08 64
    0x2400743c00800340320109049074020048602e8141c010010b580c1c6070500412600442030140100d03051010580c6540300c1c20b034000500003259648184c400c0c60b1640e0762084447d1603047e01d040c607909032103410540c104c021130340c0f50b4100d20078850350f40700c200b012092001d543d9550340c000d52403202c0c0909840d040006c200740e50082c40d0010801421189411100d002c5070403202c4406c0000c0440f40c1d100e0000700301126282c4511908005800503c02092800310324543d500d00c03848407400b80c5140800404032801311404180340c00050a0806045e600f07a804848494090700d01d846588810740740000005880e00010899030700c200e50392522070800105440748001418007502c4a0f805001d010841d0740180d4505005004441c80307520001601100400c01004441260300141e01607804440382160950b62400001140e5504031030100d40c0c0202c07442c007034000c0969031031115803900c40030074881d8201003000d01040c429511541c41b10f40040d40c40d0800c465030441e0090038008a0000301008000c143c09100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 694904172 1250 694902922 694902937
    0xd0b06030304053a0b13020a090203100806150913050123180105010e13081317101e0c0e03160f08010515042705071410080c 55
    0x54034140703076881010400712981e0100424110f02d80d50703010380500613a803820381401c465107450341c0c42e00308032956440805600606611504420201c02c103003190343c0c402c4038002601c0481d4043d034403410481901844070006016040c0d05015110000e841950160801c4038104001800300381e140d10b800102800c10416524151800c0d5201d05041c101945041c0c483c251151448003102861f00d0040c00014142000340e04042a40e41400010080070090124240c5c201c0c0d000300f25a2000700306498040010310403d11403100d0144c1c0c145000402c204019030740a1424041403ea4194036141d640d00000c840801807490004480041e00b40c41a030090345c40304880c458107082000d005610310340006e2509850307409600c0c0c3c01105150034800d080b01045444018600700d002400340d82030080c028100217903c07200c154016a6640085541140041a043c523200d00e0700d40320b0407070507215041c40c0d03441d48954003481110700b55503040220035043c62580c4100d249026a944240c41d11802d0400910794003185 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 694905422 1250 694904172 694904179
    0x170d0305040212030304030804120809120c150f070e0907050301150504091b090b180f0a050d0305070516120605060f060c060f061207060f1b050c090609060d0b06 71
    0x3c2001240083c100b0086024500a03180d2140070321342031401c602d07425549181442080304290500010342c0b80043c0c24000386400051013525005400e03052131900e0584012000c0c0ba00440c0240300302402804a958000da0070765a078001c0b031906007402d00242e08000d079002000a41e082004012540f900604212070030111320302039183c255035411030f1082e2001070714840079451005080741c5101d5000320606009000000d041e9081c074074101c02d59200c841e00030300d61500445150701c0350402691003000200c05040c006011030749240d824100205a43c1020008440c0c030b00c250f80c500d42c0e41e483c1080c0000c044801d0401481362101d01d0366151005030002a10b00f58100e104ca9007040390540d641c1d8043d00116140600074100343c90040e044078554400509010300640c90540e1b00411424003203660f405480700c2d800e0003410801d83d20b104a03101e8840000007418004562240800c006000c05c01c01c800e20001c40e19a44691524420414220740c1520031980c4070301c00781c07045030006000c0c8425036403040d0000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 694906672 1250 694905422 694905439
    0x150e010504120b0f07090501090302010c060207060c080103110f0a03111203030a09301121070210171305010e0a1a010803030c041a0d09080d06170d03050402 69
    0x5000d03020781c05500103401c54514200030108450413006a00e815402002864a155950300d0080042c0181c500303400040d04201ba4401001d0500545070111425994081410130200913944401444d110f001e00045445080010401c4010f10340500c1141b5403e00c0105104442846c550300d40c00c411f0003114555410086c142c444480c801800d1018510440780c581003c01e500c1c5851a100004e1800410401000100c00c070045614070b810b0103080c111035016040544c203c110031030301c10b03181c002540e00314004c0c200300d811002d0041601c4400f8244052081d581816a010a4001070700d42a68503c07080c150002010006030720b074030301e00307407030690840c0124000107035035011490342418009550307c15160140030960055501805c0d4605600400914010350700b10f00b402134241700350303201d10b119480034450500071483c0950040012640781141011080100084a14045a868101d6030304008038600e4600000762280440004800c03800000c00584440c0380007001c10b8004003030260080c0d8000c03424 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 694907922 1250 694906672 694906679
    0x30a0e0a060606090611070b0a030504031107080a0b070f020d12060807170d0c050a02010c020f0306180f010b060702060304060209090a0f0b01140909041b0f1e150e010504 75
    0x36100b41c8000d00a2552400486414040081c19903252120441d0b510340c8400c0c0704100c141401030613104048807a14001c5000e0300e07141011107440c1c03000c40e0016540c1c09107900018501c03400061800c0817912440c0c00e04959520500300391413151800c2c44510240e040f103021591250320461045042800d0064000350080e12610f00d10324041c0303e41c010002001d9280418a100340e02000065403444851501154a0102d9030303e0369260b201240c00203061160a514020440d039550980000025024013242c070325190000a64141d04440403103101c0710302401c1c84090f0b04031018002c4520084000d00070520700210780c7d0034071034544e000900039100160f003441014040d9503031413502401040c6025011544034003980c05001104c0f480080f140c10f2040300d181c4001c06166030029528920307012039000599070303194242903040d40306000607280c5d00d407280407010445840c0120944184c8030780000b00341c2c0d0001040414100780c4403a00400d03400c0542c0b00100b1110920645501c0d03c60107042c5440c40c01d250780d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 694909172 1250 694907922 694907933
    0x91507090801061e090516050903150702010b1e0a1a130f080f0105040309030803041401021603140a050417030c0106120b10052112040602010501031707030203030a0e0a 74
    0x1a1a0441191800948007006860440e00003000c040d0507003640c20081030402c1c1e48044124542401007c05120000ca10000e40f83d070107020b110550140d0024074411881c040c0c900038002c2000d000f0962013042c01ca131650314520f0304e0040688000303d001c0c183c6d407540c40c20110101c0c0c0300f920b85000007610000810204816040603a0b12100800c1c1c0b0110099800d42000300e8507007403140b41001c00d45642c0c50700040001017035100501000316034100c000300d5581c1e201e5041200041204c4009141c1640c00007900f00800c03c0214550070045002c0e68511340e110740c0c1ea000ba2000707485040c20340344c0052400e000910007100800c2803201740760316000440b072030031450800d0329003510080e40c8282c84c14425402c508051041c5600259403140d00c2c00b003d030600e01e00706800a881041c545505000d090600c0807440c8d006002046652042003d0810660f1601d99035400240604800d0008448024086441c0c01103440503405484034694140c01660541d650541c909004201201c01c020f21031240f024140301088 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 694910422 1250 694909172 694909181
    0x4020708071721160e040e1f060b120c0903250609050603092509090804090e030c071203121a0f12150a020f19020d0503091507090801 59
    0x32000020151103488400c1c003d04841d0202c11101d5044000c001000f20b404181114150203429504002c0d856000c001d01160040802007029040d0f0311955032001c40059405580c01c802c0020240b0078400503031590300101d5140100c042145c040d46d580300c040340006210f440039001103940507088490745001110a0216010114250029400c840768280201540300c608032018003010340e21149181480d454181d03450036964100200c40301240f0b05c490712a0710144c05c90b4014070840c0d0f0280144003240c14184d103254400d200d000c0c1d41d1850046c52031000b08010080d28040c0f51180050034960340350545290f40180c0b03202045040000d011807100303900d900c911032002104607580c0070740c010542c284203110318801940b80c4540f048040070581581541e000815238000035400203007038800c1c0c80360341354940640a0800503004820001c1030702030504807a860140701d1400d45a08440380700c900c1c500295914401070b00c00c2c018640280102020780310003c9031041d0000741c41d180003100140c0d2918403d0848 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 694911672 1250 694910422 694910453
    0x4082b2109060225020906040c0c060f2423130c05040e15180613020c01150e0901110301240c02060315030f071d100f032a140402070807 60
    0x20a10100c1300c42942016080282d002e40c00755000c1080d074000501c064038030410b000004200136111400400281903607008043c900c4219500d2000c040f0020704007902850301402004d0f0030302c0106239036810300015190440703280800500880800341d002c512a030060410304c10340c04140b0504000c00100c0d2000e180c449486200281c6501d0517100c0c100c010803c08030103c9221140204150003400038507601c040744100c66a48102005a841406d881031601400403141c4560011804400c0000c0514511203114403540440000f0030070940da1b10076001d80350100b0b004800040c40ba01000c0045280480d072102a214603d04011440300e0301a4009260b6038800c0300c1406002c3c91a0100782040d050402801c410001204080c009540c05c04521881d9003a08010881d12005040081501c501413041503101074200319625490898490416181002805d40110682c880500030800c030566480c4803071054524126a44600070807a404100c00f82d00509810303a0080006c00c800d000040d501d030740e8405e11 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 694912922 1250 694911672 694911727
    0x1206140a0501030510090203120a0c0803010b03090d02010e0c040902130f0605030c01020307051c050c0d0e0108090a0b0714090d05070302010216121704082b21090602 73
    0x466041d86800d90602030060320060141b4108011140140e802194408090481001d416260a4000800c1b54191a112009064598008004614403a024000f5845042860100c07180350010a0701203088802c2c1c030f86004c05035040703909000728174641a0001981140001c04270b00176075a407401980112210420600f40c4035940d0f00080016083c2800400041c03402400074508140d4103413a041d0300d03400f031a00302410302c00c0580c2d02c40b81b07401d02a03410344642421420403070f0301d060321028015004c07000c1c0c0100c560100d290035000805004001801e450102c2c0d000c0c0031001a501c80340030541d944095080c03c840702d01c800307001012090301c4003003c422030320f80101d0040004074a0f6000281c18800030b4220340b080c00c0c104139800d0203154001c0300c031248165441540c0100200e420403981400d8042c0c1e421001080c092981c030781e1020305406120407038019000203040000c401c028000d0703640003040e1450b52205d186c01c82240c04c8203204c0e988810890390240602610b03005060301144c0695200301c503503212 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 694914172 1250 694912922 694912931
    0xa020d021c0c020c06040501140313120807031b0c0605070504091113090608061b07080406021c0801230609041b140708030a05310314131206140a 64
    0x202c1079410055000540d4040c1da80a00c1c0c40d0600000030042c1c0130001241d04510b000101103400341d41c68444110310107400062028140505410040104000343d41c41c4000030f0824550300b0328150880140104038223240c40380c500c59452a5140c1000c2e0500070284c13014070409000025569a0070700881207029102510340c2e54030640d10120342d086426940280a09a14204003844809000501c06410100702142d15034800c001c943c140c89140f0400c1c0000707040b0040031400142c0b65070000743d480900c0700f200d00d8a040204550200f19074008003486030000010310118581c3d032846150078601c03c00c40f400380c4500d20b080c002c04003080079a14600101c001800218140d1540a0b921409180d255011451180e16042c1103031580440c50101502c451106940c0b000801c0851415002e0841e1459124500d0014400c3c085094400c03118040d4040d0003042003600b54201c4181a038044031400c008040a241400d818240c200e00030444800d0200c2d1110b9449503003141c0e680b20300e0300b100d114254091000c00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 694915422 1250 694914172 694914191
    0xf02010f0203041a3310030b0310180609050c01110a031715040e0c10050301030c03080307020a0812071709060c0309010b040504060e07060212030a020d021c 69
    0xa0031200440851012540706000f07200000380800120031641001200d1a5125110070601052281c100c044030641c07015115485241494061100719004100711240401c0303c4600070160300380e80ca0f012089a02d504803058000d842c404640c440600c90076a0b0b10b540c050780707820b0303a1000c00302c0390340043c241d80b40c4d80b20303044903562036034000d0341a01142c0300034000d018618080e9401900030600c440010103900c2801d00000c00908031902064121880100284002c0000310030450704d40760b204e00758078002d00503180c03d11f60301405101182d040f00c4d4000012610702d481c645030a006a04060015000c42c0110f0b0f01d1040030a050601030031007103c941c840701181c1e00b0300c18400b811100c010f5a142102c2c0000b0b0003008144c070804101264842c040e400000c0d03032a529501c94600600909076529803152500c41400140700c01903101041c0c642d41c650440c4c42d01c9032100c40980c0d581951341b030a450295001c0000800582c1343d034014200d40020040c001d4103241701608442c000d00c07403140c174040d4015a501e0506 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 694916672 1250 694915422 694915427
    0x907030b1807140409050a0f0c05060705030301050f030307020307143c0301020c190b13020d0609020609040606051c053105011e0b060406050d0c021c0f 67
    0x1250000c0d01150022035944441090300e40b1541c852089003049050004031000769100c0ba04901e6520b03512809a6000765030a00e0002845410004160740750740360341d8004101030800c0c60849401c82d401100440c2540c0c82d1200b0813455010b02550320b901400203020306001600d00b00300c00b402500420b007103034800b0320f0441c00340400c85081100c50b040445e12030541510580c51600000c00e043e600304030004058840070003080c00780c8281c01c41008140300d0380001c0e0140e20601041c860f1013521903246404c0c90b8a4850300070542100031000a50320501e02c000802c000b43d0181c0c0200740c1c8074030140c103003030608801d00e00290807903d0940c42940852400500320001c100c9068600c40071030603429042003103082c030001380d0346110b88208092060b802081341000c0459001c6950600340f96001c0e000344011080e0242c644280544420000009814841c00c0f000074502001950300b903400d56a030701070401074680d1055024010f6444d000c8158081c002c0300c500c40203101d4000c8803000301691954941e418240000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 694917922 1250 694916672 694916693
    0x1f030b060a0504050d0201090f06021e070501080105130902060a0f03050702010501150f090305100605310b062a070e010e1b161212230a1103090703 65
    0x10244200c00c104810000c490300602074400743c40c419140e0f044440141e00c010303591400d43d0740003000c07500d0540c4800650982e0000d002c1a4194403110940300c0c201c40d1041b640c0d51984031f4016140880c1c1c03081c0044c412820300e043c2440314041a02c8000c23640a110360003044071a405030341d08500191543c1140c4c0c480c5030305402540e030003900d9840204420343c5040240140d24456005c0c2000700722084005405d01e612139a50000691381020a43c7c144405103550722004106a100d218015180341d441c00140c2e5401c40391682400d103050554001d490305150684d4001d050302e2810550102d414081e0300d4140d50042c0f80440c07919005100792000303045003c0d405241c00a20b5000c0304008801d00018882c00516184403904016412040b40e080c2e6180d69005403180646089400a1600440e10009100d01c541009000e1080c42d01c46440914440d000f5005450004101c2c1c03030031101c103c00c2500070382c0038260100d0b40400840c0001400039204100c0032015801680c0400440c0c0c4070607030500038060040754 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 694919172 1250 694917922 694917941
    0x303050105010804050a033005091221100b0d05061302070f06020a0c0f0309180b010527040c0305090114090d081f03050f012016111f03 60
    0x90110b080d03c3c04d5074030266610040078000341003002040b058500003413440d68011200304136110f40407060010b0040c00d8018a0304580f08101446034407400c4d0302000d0803808030f81810401e60090503082c210008520303611304025000100c001c90305980001c103401c0d00b02c00743c141210324200224041c1060010480941d40244c500080c0300d02c100302c0e10700010480a840080564004809038403100d4280c010381700358110510107003c0d202c40c0d0001504040c0c1c031200c14415516243d9230b4003a42e01c026105a011988a1210203006c90010042c01e00e4160684030400308030303104002c101807561a400003080a8076104140007010030f846000f4428560f40a000e00b42000c1e803101b03140c2c0d01c1442e103e0a640d0340d5140d036074240424400b0301030101c1e11103450104e048a00e9801600782d02c11690380d0380303050b9945000c8404161030319440d044040c1c8084180c003600340c0b425071400442d5418088441c4003101e80055131201200c0c0b1046100e0541c1194591a84400340c500792540f00c0c28944a1642001d0240c40d40001c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 694920422 1250 694919172 694919177
    0x60309011b021b1909090f031119080d15060306031707021c0c080331080c10021c0306030b0709050108011802070f060204050a08060c07060c1218030305010501 70
    0x3d4140300c4034029040480381e804000c6070520003034840e03c850511010702980040c02030a0030b02e44001d00344070810846401c058400c0d642c1c000e000c0000c148403600d8000002914401e0000049e04d031021507220301c06001c5070b41c4500b03000101030418134003842407a1764551151001c03070340310700003003041c030009501c035505210014003130510b441c40950010340014030351030010400f0046080c00100740040c0f5410303800900009000c0b607076200081c1984200d0011550440f0034410010038400d2041016010000c044401d188010030b441305446c0b0130040c41038481c0c1000c404510440b440e049050002c52048a10701040d5100050f0342420b6051049082c10014540801c0c480e00060412203640e110300c0c15811154614036102026046881d000c0183c4111030000e04240c2400e04107170309104460f40104101c1c1e404451000da020340e140381c400d440b550b040760790038094107090102c1c40100700250090641c1c0c029034a0103517890000c5148110032954958a000800b8403500852000c15806101e010302410090 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 694921672 1250 694920422 694920433
    0x102070e090606060313050106031a06060903060103020f0d0203060f04052b0c0c080a111c080910020f030f121302062b02040b0309070b09010203071101020705060309011b02 76
    0x60780c8654455001d0a280d002d5007000000030500440c0320400c60b0466440f1001b0b011050b1749040842040700300100941103100544041402450302c10100c2d034034030802030040e00c516072231902044203801000c401c03e50070000c00010030006076024400715124110803506400075007414213005142c5407800002e00200c1e0381c64130003014001d018480e441c186032010b01d03241c010760500707181c40001c800241d40020003a21800c800e4200700500780c021504031360025912509100d52000c1d40c02581b41003484040c00409040003900c0c400c0c05c00140520800305540121000c042e1442c8600703113540d201545c8002c007410003284450416642d403903501d0f008480c5075000202e215058000440e00d202d121740c0c3c4085000a0f200305001703641310507100c0403090810541103460307954a400d000c0c1d00f940101c403102910b00440c000450407400b07840688040280607401103040200c0e03661144202a6006107803070551188003070028083c3d580e040114800c02900e400401c000c03d2000e00d02c1014010741141c1d00641d0441c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 694922922 1250 694921672 694921681
    0x4061803020312220807081c0b040c0212070605060a08070e041b140405100911070c0503030703091e150309212f0109050c0a06091d071701030b060102070e 68
    0x40d104e51060064201c0b6810341c0c0d5284a02d007000041c400c03d40b00760075006802c100c05403101040e51103e01030f400c0c01c0d102030001c0080b40328226201c8400202c02d44540105002e05800300350580c0c00b850b40600080c10840550b0b46403e40c2c0c40c07070803100e5880300103074184000410042000c0c100c2803aa82d280d07105403280c0c00b2400c01d00300724007021124103218000c44c0d807400041d81902d800c000f1100208801003040190100c400c0c5004002da0003081c003034600010011000603242000421103000f0380e050b9480190107130401c030b518080250344030589070000c1580740c40030540e14024078814000c1042510006920030301490090b00010300d2015104a03051707882031342000d194222080c01950080d0350500302e0318251f0321000d07113890050070746102042c2d07207071500000c1048000a90b624080c00704603480d0f0000745d66030200720340102036400b0782d42000d407080529091000c501d01c20583c00041a06040d50a4a00007042494540d030991041d51050506801d02c40596018068040540400004041503180 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 694924172 1250 694922922 694922971
    0x7171309090f060e0705012d0c15021812010209010c11010201110c01140105030a080708030c090d0f0c050f06160503120f0901060f05100804061803020312 68
    0x4103403003008449038031103404404000e07203000c015000342d03030240702000398203900c4100307698600060003810b0115000e80000040029602400c0c586c0710941c2144240c0344d035440004494080d4001c4c011140303210030b1141d0005103003082c0040c05c0480074040c031240d8400035001c02c100d25130a07401000c0c04164410007921040da40e0040074107080c43c2c2c1206002070101841c2004034010305111056113401c00d40414003000150048d0403074110050b00c94481c0090b030362a02c0406444004448004100034000c02c12000028500c501035980080b400c1707030042c140380f41403022079801c2509500840d03448181804801c100130030f107048400034200598007c1d2010008002040302c0348200742c141e107507403d0800e00d5141003110400403528884000340940303c80d420141d014020310107007030300c1180f11542860004102145035010110843d03100521000080ca55584290750141c07000e003066078001c2d200c00480d80c580c945071070310700c0540b88241c2c01159a0310000d00043e2802001410181b84010410310500c00c400307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 694925422 1250 694924172 694924207
    0x301020720040c111510080703060f14130308070e0a060c03080a061809080d0e07060f05091f0c02030d0903152003090c031005041104110301061202040306050901020717 74
    0x200b4496441c203e442e0031b00d80c2c00c01c42c54240e02000080c89010790120811a02e0342080c00110845a028425804d003c4d030b00e000e100204686000e402400d0300200e10100b40300e680c800d50004e2082c20b024203070300004408542d0006040e08850b02003400806101c003003540c811400c551001c4020800c120890400e00c01d101207410340300c1401d10032520b47c0f04243c148540c1408448441c07041030820048600e0b002106510782c0d00b140f10b80740108455800c0c007035200e80520215100c00d40b0050445074201309066541c05081078007807582040100406948005807410000648001d4064031103003071403440c0d0b29103d5624640040042030440c142040da6141c095070180401d00303442ca00c60055125503e480149240504128443c3e40c184610002c107a030f0301c0b083d944081d00a42c020f0204038801c800c4203061005440705140c0f13078000c0ca00f0400041002603c24040f6030040c0140350805807a0a0390794840d8419038400342c595a039075075130000301e14041100e0fa85001c09000307100c86d411400c001c1242441018907 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 694926672 1250 694925422 694925443
    0x50d06240906140c120417060a020306090f18070e16090b0403030503041a16110f0d031505040e03040819080a2d020f060a290301020720040c11 63
    0x80a011408500407403040c06080e2140005c55842d0b030311035031303a00301c01002c0c40c01546000000e0b0040c2d401040c1c1655240c021280b1841c030140c4609159140c1d01103222300c601004010002d140c0600003004182c11040c0a040c0040c000b00e0900c2605081034805001074030724102d4558144500d280c000c005020039103003034604583e0541401c5031243c0da42c2c18502031040019905803074940310407040000d003944980e0b0b03c01c0300500030756a085105621250b866500c0d901e111590302d05038042903110100d02c0c480c0d000b20611480910002d0a01d60b59000414203480220b80d0065036a040850140403200c03082201000700c0d120a40001e144414640b20300125202d04c05c0c0510410026500c0c0000c14001748c9036110690895413110300c0c000c04040f030002e4540480c50f6000461703014207030114000b000300b4010b801003a41c2c0101d905501d103400108000910f504040201c0e00765409121410216801101c240186821540300b9070351304030b40900f000201c91041070048103004419603400001a40000c460305c03030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 694927922 1250 694926672 694926707
    0x1090308060d050705030d0c060b0604060e090402030c130614010507150513080a1707051905160525150806040b0307051509010801051c080a050d06240906 68
    0x680d90701d06020381000c804e07801c11600b621501e602d003061182d100400c02038240c043c4204008a8502a0270029203102e40d1080740002420a42220707041d2070540851500b1604c002c3c21a09030740420350104050305124032484140c0c070355496082201d09800108042444003d1070081d10b84001c542d11280400e0290b1840c0200300d40e11030000707038084c00d07a00f05025682e8101c029240c440d040007170020040038401c508603411b1140c05000c165190b02920584003041c5030450440f0070304401e0141110a80c1140950601c202000400000843c0b400d00829100030140481901000d440d40000f080b1000c8903444004000c3d5801c3c0300c0c543e83e40d840008240c20180403500480d0040100d00081d28020b1184c00183d444564102c054610011300001040041806e803100382d01c503a61001041954402d001e03005409070303c02002c01000880e514002c203400211410101d01f8607442e60441000c559843e0821865a5404601d42c4036003034010603485014107061404490385420090005c0040502c2d1400418 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 694929172 1250 694927922 694927939
    0x130906090212060a0e16140409020418050411010e01090504061706090d050a0804020d0b070302030a180503040509370b040e120a090314060714070818060d05160e030109030806 77
    0x14841c0c81450fa1040d01f65024039801d840b0742d12282c0b410025401031141029007511840e4070b0320580080d009041c4101d40003442140e6a051400c010348200c81800120390402c4000d480220300c640d1944211000380c1924a00f048030a611800b20514100c40601814010390250a0050503964484101e8200c1c1140e481d00103031039250351011903000e1940c0e41c0014038040c8030340304000403c2c0d13046c0d01861044844000500002c0c50758058480031008a40000d445600b04001c140b00c44d04106050542010110b0024403181e0481c407030200c401818800c44030008001c1592503c1e281c9014007a43c401170008607400c010190701e4a0800d0b9848200d82e05014880b000401e04542e01805000700500464002c24102121908030110fa9110481168800080742c2c0c07111580c4245a41d11080c0c900450b40903805034504503c5010100c4a0000390002941c402402c110001c6001031a0081d41c2c011441d10030141080614a034016058107103502100c0d0190785000c1c402d1010a52280f00c141c0c02c05000d80b203214 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 694930422 1250 694929172 694929211
    0x1020d050f04140103060b0a020604050106120c2d030602180603011809060e0a03021f020c070b071506030305030402010e060309031e0403240f02120c130906090212060a0e 75
    0x174003074a4a50300c94075041c2404500d00000c02c0e000302e01c0c41d1141d481407008001154035152034600f070700354508021300030098401042c0000d0103101003840c0804a00015800f40314401e0b03800342c134900d0030b940080350441e0300030641c01401c1154614807105d044084403d581558100b524481491741c0c01c0d00070040850f10f441000c130910006a001015560b2180c0035501804018180655a000c01800f6100c0d03a1079510001464003405200303680c80c0840141c041c10710b0a241680c20541e40d008a4401e49a45000c05204550343c81144a00300085209440d86600c900e4240000350001c240054064020030003001045082c0d8800301c1140e44081510400140b000300c00142d200351802150001881140d403030340780020162070720b50301405140d20401d0030300c90701c07107410300c40c005034050b030f281d08103a04480b4070200d90032911600203824054912a2082000c0f40c0d5142a5030507162070b41d004504041d80041d00304901c0500d0092a030380101d065401010880ca002410350b40c0c880d0003440c030441c0300d0440c450300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 694931672 1250 694930422 694930427
    0x10050114012708011505030c010c030c030512070906020c0103111c06080f01020301051e0928051602010f021603110304030b070e12010516080709080703060b01020d050f041401 77
    0x80440e42c00c0c0e0a8900190315503a555008211072503455840000609000540d45000104032002001c10794500e441c44d10641e505545100320500214140102404151041044111138510803d802d955841032586003801c00ba0a00c800c6032195030400d8180400a01141440750845210200802402550503107600e0700b24001c02044d00542564090711746261000e44054014505a41040780c411004214000c1c20412048985016680040f44000000c4051815401101d25102c0e55540242c02c124090b204e08101c4008980c0d13040c2030003005854040315942441400c0d180905017904510301f50516810003030401d5070940003000c0002444007006000f0091068400450f80401d03001c1c3c150508032809401c000803046050300a40400b1210030b001c100500541b4043d4002c60105d90140c00d648504982c00b01d402403110341400b0f0040c1001405400400c0320000840c05030500243c02c1d0200d10009040c08030b02400070702000001e0000b0113101c42c40c80216802ca038410448100c8451150006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 694932922 1250 694931672 694931717
    0x501031e20041e1407170402090c1606150b0c030f090418050102090112090305090d060e190b0108060c0f2107050c0708010c1205090f0304171005011401 67
    0x5203140040b030039003c407280c0600c0e00182c03442103618031003a40c507a841003412070b100d0503902c1000c20700e045541c01203405801c2074040d064100301c9c0b0f64001440c00e00070300702c40340c1a1880640b0841e0a280c3c1d40401d28011140004910058a101c0e04440e01c0d21071024802c640d13038054aa4503400040d400140300c0200e0303845600a131061507440c0c00c00c16140b030090815034000d4001c070440d60701080b039012841c9800c0c462441904035095154864a0416566406100204500310707421180540d131148020010b82040100c0c0e03000d10001200803040d440286088a80808181c2c48814507a2140c000d000000d5803280983ea60704540c011b40c1a1034420625010b0006c407007c4144d4031410900074244841698084003c0800b00f14020840d8880f590f07650351542213618064003180002c40c0d82010b0031072030840b5004103420103844411103040c0d5600702221406c40c0d006a1104100e940c0c040300424440e03200b401154980741141d0000c01207903142c00c0100030040b0f2200b08180c1000112040f50740c90300200d610 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 694934172 1250 694932922 694932941
    0x81005160923030703140c0102280309271503050c060a0311040f03050f0a02010e040e0a080a110f0724050d0501061d03070f030b0903070609060501031e2004 69
    0x1200c0c009175a0f41016920440c0c04071841070b103802055002d5010307500010741c50301c0080244444003404541c1480c0d20f440c213070407494110108140e200c0005250700010403e10032044040340d00101202035151500111903000b4001c02144015100070000f29034040381c001c42455060318040e50342d5031000e208500074414800c0c2e480c01900b000c2000704070b40c2d00b0340c1c64003801e4900c00c204441c00d481c409440030703641d2800c5c00c2000740019000100715144d805c1c80e400034509070784408201e03056080d29a4442d4125000b6000c0400010b0300c400c11083d0380e81c410058121500c4c1b40001030041d45040501c0807400345e0b03841d840c240c100710840c1c0c0601e0344188503108884440711000400c001d2542c484000403e00001c80504120701c40642d00707101601d01d80402c007241110340302c1c044000c009180d6074540c00300715801070500d1854001446508003107111030161020003403003080005020340c118a0031003418540c030302c4012010800300001000066540c04052114060841c1d811040b042c3c1500240242c0103820 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 694935422 1250 694934172 694934179
    0x1501030917210405070f08030c0c0112090b0108010903032f0702010c060510090516020618070e0a0609050a0603151d0703230c0307060507020409020901081005160923 73
    0x101003105000c404501001620b204446ca01c22259440354004d03a07034007800ea00885240c0041c1d00c00f83c019800354162500c01e0b083d1810100b10080035888440c01c5050903070103190075944070841c0c8420140d043c03141c0f06602d0010b0340ca140d440040c0880c0e034410050702d61480c920380e240009600080d6030144e13003d00d212903403140d424031035807a1103010f2060b000c04900c83c51520310f04200100c1c520048203400d50450f40e02c2c84c0d005103400d40d2403081121954030782c9188403100380250304000c1411300e20050940d11908040b5000f049240c60300181d40c040740c1000340410201d83ca0540e003800050944103000c00701180000010400ca100c44c2d6a052000b00c207000c0061183c405d01a00104000d000700000b2540700c0159000d00288000b0743e8032036100e204580b03010340e043d002403105002660192015100c1d076400a07100041c840364076404100241000e030848d1000f40e0000c405040000064024564450030001e55290080000100605640c0884c043d1031a407100d9124581240599248820000c0c038008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 694936672 1250 694935422 694935487
    0x1b01020a1715040c0e010809030c0c010e0d0b01120c090b090106080a06170a1a01030b01030b07020304050603282702030a081b070e090601270c081501030917 69
    0x180d000e0010324170b2402003400700e28604000341c02564040141d0340708504400c00b814941d54910011905e820603804c000c1da104d008032071b007040490250315400d80a002e600b41201440703000d40c01c1c0440d200c40164846080541840202e4035135413901c080460441c4e8083c01c01d4000d40e11003001c0314010b48500e030030111440548114000400740300150031134145015201ca000b080008082c0c0401d003a000340005440014884010000580408a066484000c601c1941c0c03d180d01c0348005421684241e900c401e4220200c003070f104240076189500d24104194140402004001c110106840c000088480f441004d8443c1d41c08103545050105100c1d1951206000b56908d03080c0c000300f194020747c0c0d4100d001c2c52056005c0442e6801a2000f01c1d802070348803031b000303003041e030320b40780d8100c1084904100a07034603401424040e01c02041c0344c2c006d450410129072113007841440c1c00d01c4406c030b042c4210a05d0604150808580d071b00403030400b2007003501c981810501e5954405a079114034410982d00310380e01500e00da10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 694937922 1250 694936672 694936691
    0x100e0109141014090c0d050307050607050406111b1504050316090b100804060203040204181a15012a2906060c06070309020109050310021b01020a171504 67
    0x80340624034500c4080040090f00d6212211400142084400e50102d604c112084c3d5a107140031480d10300440d01c1201101c0c0751040075500c2c00d0800005846000c0030980c049018024990040c80800191203408014a20054141488540000120390a60084000d01402071a18803807608a4014001c060200d68038580c0220601c074840d415031040c941c01c90b02d0900021254540505003001a21150f96101000c3d195511a14002d500181089030b200b0303034468402440e0300100c188018001c0c020190f42c0105603138280a0114003c000305407140e0500c041c1a4a0103507a0045041c0c8459400b100d1020600500982d410710341c0c0b11101d0001e08142d20004420020709010742040703c1c041050304004409846130000e10280d40600000c1100d00d400c0840051102c0d8820ba1210050600501d415482c150b51200464100310b5010382d0f141840380c00003216840700303c1103902080c604d101d100c0210302e000c803585001880000320010454044100202065840300381d59820019000c1c0100700300000e52a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 694939172 1250 694937922 694937963
    0x311040609050a14060d0e0102090a15090819031d04020c160b0405060702040209030a2108090a080301150903080d0f0b0d020901090207140f0a150509100e0109 70
    0x10207101d10b40c07103001042004602486481001103100d10301821582c20b0035981d03402c0b10003426011144410780d41d820305c03c591642e41c510b00c1e804024811a000c2400550012000400980c41a0000b0002e903010803180303801083c14070380c83e1101075010b04e0410a0400031000600ca00c0711040000c0d40d2050021070666015440869412810002e08101c1c80080b5030b1140c084990f4002c41c0b02e820b070701000510819000d805c007030f0010705600c00d004080c2d408507080c5564450011014400103943c11a182428003202e0b50031541040e0081440e100426018582c5c0c3e507075540f0f0f440b050003151501c102e40000142001d000d02c01d90340c06994808800e54460301c2c0e03c03210000400740001d00114690601c942c002031818010700c50b910311034010340f00c01c001e0303030030185104080d522440089881e17440e10090300c2d110010a06c45080140e44007005003070522120300b00a5448084808050880d5140400b800705020f00000c103041810034034400030540c4440f5094542c01410142c401401007491040d10301e42410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 694940422 1250 694939172 694939187
    0xd110a020d1110030c1b26091c02090a1d060c12060103053304020f040305010501051215130605070801060801140612180307050f010507110a1203110406 67
    0x9005503109611001d002c4002c8003038505e9001004080b5a20fa030141c140f040d86404e1242e030b201c0c0941c0d040700707031010301c02101e2800c402c1c40c540703400821318003291001c424606865280122400e000314020b102e074854000030b0102d075020305070305c2407540c0c0c03001f03008149404900300241c0380a90905951680c80c00b03608a02c002c0e03003c910ba4070034035612100010324560103446014000c05840000c8056415266107502c00c2d0110702015a2201000700e001044640e507030700081a407105d958100302d4880e40703185452400d580041e000b040c41440480d140e028520700002d03c1300d21b103141c820324501a91704c90344182c000c403401603400039221900b4081000804d680141d405812118547c0d91041c80d6aa2511310a400071b110b0340b507032580640d0030086180b10a52070702c8041d401643c404103040d80700c895280110f2559106040444254000c02c001003803110f001e1142560010303050401d02c80074410500e4203178846a04110050952142d0104408031510a80c80b240541c3e00918010f071ba1a40c65110150810 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 694941672 1250 694940422 694940453
    0xc0b0c0606040c1e110f070906050f010816092c0903090310020309030d060e01060e09130f03020c030d1d06070b13080d060905040218010303020d110a020d 68
    0x1889200007188040c02c0c60b224010405800ba690964151600d10720501c03e031800c0102082000310003a0b2075510311009000613254070817100700a01c9040c0c60300d4034280c144ca01c01e6106901c141c0403420308042603608080d44d190703c010080d107146600035a641c010360f44210207070030400b0780c1c00000a418440b0381102c0c140c0c4400541000004201d80c2e1031280503540d030700c40d2080e044e4040d00b18189102d1044019009940c1043d80001501e09240190710301c0402c40d002c1c0d03030080c07015030165401041202d4100040c0307120844103075101c3c003241c60a449101c042d003456840041403100d08800303900034148203003c010710303150300281070386d40102c526000140401804c01c00000c0780e03400b00d24104100d24010040340c2d603103580107078429155522030042c55a409080003080e61484010400210025841d224802c05810411750000b46410280148601e04044642d0358007518003a100510210b9000220381e0000310756460141813044901d00100e05105a880000350072004840c08031040140e03125450b00300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 694942922 1250 694941672 694941697
    0x90d0507030c290a14071d040b060a0801031502030103111507061e0b0d1e0804090f021305060a021b040905070b0c0c01021c080406060b030709031502070c210c0b 71
    0x1003060041d60203000d18411b492403c0814501e010780501c4010134000e14411043c000d10000e2041c0310350b80071404640c06501007400244541e40103200b000b017034100b01d48107860308800c04c6065605640e18a03054240c80340c1121b00c00c1d150701c400c20700e45c23a9121045951155100e5014009403c0b095002d01c89945130559180034141400040c0955007000c00d40018a03a81086006e0794040a80c642540c5221440070b0a8825103010000862012014000c0081c0505503c0e030040e504c03c0040d9041e040400d942c0c1020f48a90f800300708141410750300103141420041e081c4000d20102900f880054014540d03030100902d5405200300000c0c2d8130401a000d000032030100c0b803d9518440c50103004a03280d040142030314121091906110403103e02c142d03049a0f0051040d0000070740d458481424001c2608121400000522010382c1441003095080c044855541000825401c08034940d540c041903244a00a0846180d84208000283c442d500f0202d0f40385900981d5001e00b80340c0f6084000100d40c0900041c2c00c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 694944172 1250 694942922 694942931
    0xe070608061e0d05212809030209240a0803030f0a020915180409020a09051e092410090f0b09040510180f0803180601061205090d0507030c290a 63
    0x402c005c5030441c0c1d43c1000d8604580320030b504508086420074669014042000300103500400180c075980c800a0003075000c200207410719110081c003003212600801d0050700840c2c0d541400c015001d4008156a045584807007035901a0b0707039043c4240000c2c00f54600080d0310198000328140d000342450010304020210121142000c0c0341c00b400e00003038070482c01000b900100c3c811070800100f082688000e0304000d4400c0d07020603818403a00d40180d070740011f50301e44115400c0701d410011f807a02d56030010368000030a131180d0607141c0b0300401c00e414055039600c10070003c5502c0d082680c00441965026041c00e05006207466841d0629003406981c41c400c100e40400341d5490081a4580102c0b030f6801140d031290311990365050242d0301d6071030007000e41010b0300e00a0480c221b105085d803521014400540a402c19542e241003181c0000701c0101a60b8025202a0f056007140a1201680da03100f0704450000c0e401d4200070344140410f02e0090501c0300800c0e0300f20301c0140000c5a41d812072141c0030a8902400e44800140b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 694945422 1250 694944172 694944223
    0x100e0312120f090c0d050a02060f091e060a0c030504030b0f070206090313090f021204030e010f050310062007060c060c020c0f22091202010e070608061e0d05 69
    0xb00002d00998005141d503001e00032030080c0d0328042c00c100c10298070a00664600c9104d690104035107070448039454440f00c030042140d0f00c42c3e06100c089550b1030101036400b101382c11040400f00758503105c0c00445404000c4105400014540110211001158804180742c42d40c40c0c0485002190708003901e225005000c0c0c0c1000c036604c4500003003034070362842c049961020b24920f8507851000425009000c50301d200e8003403000c46804030119000788d04c118020b49610594011180004244d0407441c4031640911405106129400c0075122210003503036190308000c100000689040400c040d01610650464400c1c0f180204030280d000c01c035141c001d07110703c03014171210040c0c420590305d5a0031041c005401ca490f1913984a084d19015006015816119952508003001c4040c02c078103444a0f808150b6504811a001009180c0e0910a07a80c1605600b805040c02c1070900c00d00404200024007050300c80c4c84840c0c41038030074204e598001c055003034004003068540102c520305107880d0a071a00d501e424a0760f0716005031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 694946672 1250 694945422 694945441
    0x20403080c160e161b151b031e09030e09010303020a0c0f062f010204080307110f090c07030e120a06050f09100e070b0301060809070b09060702100e031212 68
    0x18061104154210010701c0190b03401c484485c0782000c41368001411300c02e004085484041401c80c2c0b808140004107200d10207501c44070703da540030200c9004040c5800350241e0b601c0441c02e10004172410300c540100ea1071581e821304490700a4403017415030b07014051100000805d5000a43c0349006440b40c42e129484650356030a0303545500c1e26104040c0420307151207a5810781e0510f240040304840700100d5050044000c184080d08907085a0402d2800383c1c40091085c0a11811100401c0c600e941250483ea102035200c001c038140d094003803c2c4030044107020551904060181160450701040030708003c941401075807200d580e4a4440205a692500c0c290200e40018401c1c40d5503807107070707202000a200c10454032049074010115066054024020170b000440e5140c2d141008500908495442011904101c00c80c03908260f1660300018580304c0812101505071a60026140801d804440030041e080010300b05681004600c441654540100100ca5807569841e002600d03003000501070f51070583d44d401104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 694947922 1250 694946672 694946699
    0x803130911070201030b0a0816060201050108121225050a030b0315130c030c1212180e18010c050a0e030a0f0b040507150e13200d020403080c16 63
    0x5044500c0704001c0b5902550003900b1034420010003800905002c5d41e1800410300300360b0410804506450340190800606d0343c2400780034003404041016003140c9103002062000d600c0760114240c00c6024400008401c401032a40102070146150300c04074042000c502c0c001e005034070040703c0c10007180c40c4c9080c40d0340d107042c0011403030301d000d411002d042e440340c842140002040c07000000032640007102d5040800002d003040c11580041c5131019441d240321960b8600b00c1d40803007101d0425410044080071450303500202410210488400308172a8019880328050415020104d007030050b860342c00c140b019180c0b05d40c003000802d040c2e81e140e85e88081c106002020540c42e0395034140c2c050003801c41d45c00e03420085002c00c240150002c1c822030803500031540e65207040d20314205a040344400719036604004a007604000820700c80343c0c100c0405c01c000b00100c0018110b5250b10501880d06006c501154442c10a0140d40c101d5000c0c60700304030788648900b040614107035506086400070031140071009000a08082c00b200e03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 694949172 1250 694947922 694947941
    0x2a0b030a0f1514131a0f09040b070507031202031e01050609060f030a14070210050703020f0d0906022b06141f02070e010902070501060506090a05040218090108031309 73
    0x1c00c40d4040b40381800d00d41c3c06902124816512180300d410410300c400c018860b1250f03009002a032150504140b1041080c859030b1001051302401c104020480000e1101000380c1d4449107900309907444e1042030400301c40014a100d881d422140c4000140301e0491304184010211584807046821540c0c0c07034800b4031180b4081c50b515103030050380a20207081c440d5200c0c40030350313484a40e4000c00540c141d62900c080320a020141d0740100541c01c6840c90460040e921700841d50722aa0310b0405600d810207100d003a0180d8410207a09107503040c0c1d1003200b90100111501101d41c0090310701e008601c00c0c00f0b0180703041c40323004424030b50f000420700c0c000700001c4907807600d0217095010a00600034640494618201c5001c840da180701c0000318010424003240351992080b03800d020744191040181c80d4102c904e00107013152001c0d00101d108480908c904c002c542d0346c401d06070003510f4040d140903850f409011441e04411010101c10741e8010404800070608050000140c44020480514030051940c0c41031f441d07007203800889 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 694950422 1250 694949172 694949201
    0xe010509061f060e06160803010e100f05060c15090309030c0f0102030f0d0e010507270302030d05071a0405030903061308091e0d0623010e042a0b030a0f 67
    0x4404010f1203000390244050290003030480c0d131812101c207101400e8030007051b404442002c8007000500201c1c50000c02c01d907112603040c8880442c14200112801017250340d01c81c940c800e46001414072020a414041d000910702d1800c40a80a0f0810400715901c2e50401410580640303c0c0400240300c5182080c03040340c075202c06801662402c940140c2d1503400d503100074400c0300780070b0f200e80c0d4400c0b0a003000d200301d503c2000b070341d504d10701c0000c640d4140d14507800394508900310511881c201840035a0300030451040c5120710f8107103913550390320501d440c0401010312488503445c003400608000030302a0100081600750350403001c3e1901a81e03076548401400c60481009040942e043c48103d1140c00c140d0141e80c4100ca4407001142ca4190003000a032091640340012241161103044031b401140c001020600340d4100080080ca41e9810a40b0111451310f00410140450481d01d080706100c0031041e00c8100c0100035200f1181108c0c0e11019141410b90003a25000d448510f08a00f12864480602c00d0210014504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 694951672 1250 694950422 694950481
    0x30e031218010804020114030a06050906041e050a0e07080a0507060503010e04240f0603060c02010c0e06072103060f0605071a06191409090105190c0905040e01050906 73
    0x459061900a0040781405030301f0300c40381600c3c0c400d0405903128421154000c61480d0a00b0305000c2d0205003d040319004a0500c01c24000b110a003503135400c101e071113407100040c1d155186080400500100030211801c3c0c041d6041c041030070100801c4251965005d642241c1c0200e9550000f1102031200b4441d9101d00c3c2c0c507800c0850005105802d5013581c0c1c04403001d07510912005584004200e031070011031040125034a2700100300300102c9008000c00400f0600017000440e00d2920090140710340300250520031800022580100036012a01014002c554a840800b141a030f8034094010016030090902128076404c002945070320075800c4800c003030390203c221940c460b40c04a554543c40c90103042d603903010301000c2004104150032890240203105140d1a00c41c070900f001d052104007a07020300310042590516080100c000c10855203015081803410340003517008110b4a0864441c0170036086554082e0030445c4124030000b054000714040c3c152039083d1082900e900410030a18018a00d40c40c0504841307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 694952922 1250 694951672 694951717
    0x315030d0219060f06090219141206060c03030c070510051b0a0e060c01020403060b191802070203150f060d12030c0306030f030314012102060906090904030e0312 71
    0x2580000d81c0365031240d040800d0031001348002c0c1c0181c0c0c10170b0700041505580441c6903e00d51005100c8400c0c900300508040722880700304a182c500c0351040b030711034091503d4640c006c51003540b9610112018250b00c2c034261385c0c590608003140705e80c540c4260380540d800d22840c0d41c401008c90207441418010350300090882c500d0942518410280e0f040103c0030424013403240e00c00b44031611040700400308945010001a6620f0941c54141c041314900c00d26940076442003000d01c8022140304040c03000382d8241188c10241518101c0b014406403050032402509030140040c414402d075206001396010f208002040400740d5681d030140000d0f0075110f1005001001c0140c05502c6c20750181c0c2c014140700f0102e02e0041621b64483d140d240001c4004101200000d42d284030003020600d007010740b00c1c007401c4000240d1008504a040010300040c0041000e440340d40006542012541e40d8001c9510140c4060301003101071400303040107480195502c0e800c0303001e800f441c0f0010210031044003c51b0746a846055660b08030100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 694954172 1250 694952922 694952953
    0x90f030a060e25140904030203070203060124090b04031b080d0e1008042003070b04030f061113140402160c2313090305070c03080d0c03060501270b0f0315030d02 71
    0x4006c2c2c010f07000d6000401640d0090788050004c140078101002d150348c100010406000070500c200d041080400000c200c040c8458032182c0116003c40c1c0e0004040740c0310b50604203990710901d9080c1c0c051002c6108058035000002d801403810100c0034012542c5484c42e44001d48207a0702c4000441c1c00500061000784040700d40410080c642c280c07194054201c2d100107481d03d078080004e600540058484202d60400c1d2401c10811b4050310300c1040051451030309119043c0d907001314206444c000d10143c4043e5480c145000c0d02d40e0303415144240c52440103018048000d08020344869014001c0d25105596103c00380a080c64402841e800354001030003600d0b5041206013003030018030542da0203c0811034200951030200300c10660300006503009460040d526110300c0c12403400c45511441603810316050030802c01c41a81c1148a0180c1c0c182704070201c4aa0b024140428000d01410340c00030f809942010070304a000d941d0b000c02551194180c0c1111407065901c400405581700318080c008e40050340010100240c101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 694955422 1250 694954172 694954189
    0x402060d0e010204180b040b0f09041712070e0f0a050d0b132307061b0b09070312020109050606090c071e0c0e06190803090f030a060e2514 61
    0x304640c1c0014205925030340c1c51203205005640b50f900e826110014051300b86014410484080350494580100f800c00f2408111842d0f401000900708455604150318901140c0080f03410150080480d4001c07484d0000020346500c099000060290641c5c012220042c01c142c0300600a80c0c3c401001000c05e107040d0f60340c00900c0d00005001d244504004140c480c00103181c44611071019120b01c2070812005107241270140707814455803001c0300f0401e060892250020580c2070f06040250010744050903551911106803900c00983e000600031028072015183c0c6a5040d8010502240b083c0103440682e1201010032011040c207403222022a40f04100d0540011800f110b403c068480c10180c104048070151160b01307403458140d00100d0101c04010801c05903140c0040c002019100c1c1200c600711203410100c80b5540c0b8015100028003510800150440a580c2000b4400c1c005c2c0c4c0c001c4040c00f804607604031203603c501c1c0305040c00821150740041c2548202c8001e81d64800c0d5440a01e1100400a66404010455 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 694956672 1250 694955422 694955441
    0x4030b15012f03030406060e24040c020c090a1a03010911040504030233061c030e1302031602070f060c0f081b07061e0914041103010f050f04050402060d 67
    0x512020503001d0b819481440554840d90161100180310ba1800280b034810400c010240e40314030b820380910085480350000344021002e000c5e2400030750704103c124268a004c18249190761f014a260003040380f071003216041584501805010114036009400c145800c1e664211002004c54100d400d14488504156214a9001e4002c7c4100c0f2003040101c402c0710800128000480e861854441824102000c4000040d404c45403d6a440c0c0800d00303118922240c1000c0260000d04001c400b80da0104c840d541c2180980707210b401c45070115505d00740307010b40b620054070b07400c0e0798405401600c0c00000ea20b10b059100608840164070350300c8140703005079951190400341d00401c4408110030301c000450303002d1401c170b5030304001c4c481c600528055040c041c01400c44202d400c01c4d2080900700814105084e540034030400212101c02988003014062540050003810305403400d402071100200000a60280142d041c0048410a586041250755040c4c03d002c00d440e01210701070f40040c820007050030180306503400320146 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 694957922 1250 694956672 694956737
    0x1d0307080d140c0405011b080304020906130e070e06121005100f090506181e0402033a090e011215020f0d140108120a090906030804030b1501 62
    0x40c040307042c00c1d003960001581c8944007600c01003020300555130888401c00e10b0a400e00c01f1f00c8545403140c3c0e1400c015100080000740148803460100c1d0903500d40b0300180268445540040c00300c0420300c540c880d901c081c54841c00d03400745030500100b82c0505000c0028201c0b0043c20014041c40c2027100f1215019040282c170341c080800c00800c0000b18002d016032100040c1204a801250b681000020401100390014400103682c003030406020b804d6225808088070440d060903010000d42d6580002030800800d0000f14511010903901264a11385400c1c00c0c0d8a111040700c14100030040300380049a030000513010360b459580ca108010f0082c14540407210007498410700701446418090080202039801c11200142c1c110004151010312035034501844141c0e402150310342d04250700d400801561031044000c0a001160001010380e0340c20310808001c07014000507042402865641c0c83c1c020040c0e80035210661b400b001c4640410401c80700940c0c2c440c04004140c1d030764000500d100c60408500c502e040c00c050030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 694959172 1250 694957922 694957931
    0x6040807050c060d02030f10080d0c060f020d0e1203161d0409080903011a0609012007081506040e060705090102150c030a0b09010b04091503140a05011d0307080d 71
    0x101075645400801480e1301024002d41c032070038a1444004046d0000d00130321040684060144250400000d4080110103545032107003215125040a40c0200b64002d1101d00072400040d0741ca914205982141c00c030b031005e1701d0849070403405410807a1811300094805001301400306680901c914864016030000b00c2c984c0b400b00342001d240c000018112950503408071003030400414540070b01d203020704c00c1001c250301c50000c1101c4140c01c40002840f81c46002c241a0520a401c8041c601080e0340c84080c4803c0358268040302c84840e100d22480399144a5041c00201301c1090328001112410540074a545007108640249460786a1135800d948170741010400d81c2c11440f82100140d0800501c000e418003801c1e03402e18241d0b582c24100c000e6070541d0f1100303d1841c061140800104065403030b500c03c6408581550a0006070365240d580390100c0c030a040d500151042a0350454409580c00101c0d05901c0284100000c110381c4440700c182c2000351200c10a540300c2d64006000c4d0201240c4007500070302d02c05c40740400018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 694960422 1250 694959172 694959193
    0x909110301021b160503030d0e01060305120d2306010e060c1608070e040308010e09070b0712030b031b0904020612010609090c030b1516151e09050604080705 69
    0xa08a0300840041c041e102d00710180f030390707100700180b00301c80807900c1800c481d106807400c0002283c0c4d01d00c21841542483d540e181c1c00c070502c0080070341c4014091940007041c0c80c901185041e21a0854201a0b041c00c1403c1c580a4103510410015014061040381140048401c1c0d0343c51005440d007484129040d50404010081220403030014020350017444c01c0340c507a080d126401c1150541c5854601c0e04402402c104000c140030109800600740c3c1d04440d50700b0504800f030341e601c009032401c0001c1c0f0362004100440204010007000307149220418601c4243e6810403648080000301641e650341c1140c080150300822600d2500d074200940d082c0d40c400d001828091900746070b0001c4c0020464240e02400010302c40c9802841002151b024810006080b450141f003101050b100184500c070500842e0340360b03000005800100304502e4000071b05860342040480c03800c410090840b00103000710b0f8091045245906454002581f241e1241c400c14a402034010702255546a682006a03401040c0950b201d118001710079 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 694961672 1250 694960422 694960429
    0x4050a11030112060f0e0322030804270605130b010504030b040b0415020405031c020f1b01090b070b011710020a020c01030c0806030a080a0311030c0912120301090911 73
    0x214003c001c5554500f44044190500008890b00d491207540c900c1d0810342402c2e04c1010020a580d01d1000d800342c02401115064141c031050745180c3c2c8001c0c1081c00205001030103090f861200301c4880ea01c0324041e4219034500400000700e03000e5000d1a40d000b0038400350300c0c241c1c1c003240e44183c46400060411501d031644980764202c0300d400442d0100c0e40100315404000400018512028080d00443e000303508090601001035103a0000c90011143c40e640710180501c01ca1003004050f400e050304c202507804180712500d8116031001c3d041c21181c04518404000200203864808444540e504902d2070b4001e41d003412004402d154548402c0316080c8580a08200c078044940700500002056030000c10821101d0400901561004000c41c818001504204542900c0102c0d110b80c405500c00c000c580e68680c1c100040d4020248101444001900032080003601c0b102900200a41c0740111b03161681203c01e07811460b510f58040c200302555501c1400104002210ba402048660b0310400c802e000b41548174010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 694962922 1250 694961672 694961677
    0xb03070b0d06050406061d010f0e100c0506070504030c05150c0607020114160c03080402060d11120c0301060504060f050f4303110a02180f0601030207020a030204050a11 74
    0x101201c090b41d4407001c020074a084c1c841e030001041030b41040c115044005040741c40070800701c405141070102c04030030048814440c41c2c0c6003041c031000600752903000c2c912040041c11088440801c0f03c0d140b0a541c04100c0041c010130035102200d60108401003524141018085042d108544440d5082000d20001d06018414046148511481d5000140000d80380b600c00011200c050081ea0b0108100700c0d03201c4070141c0c03100c40c0d00512601802d1074141c40c0c40302e101198485c4101c501f0b4419903071914604581458050f8010072030000c180d00e4010042c2c0703c00c0e078081420311081c801c0102254041008010300750003509280090009820818140b60965104107240c0e0720110201c07124000c030300c1c0c1541d05220000c0142c4480454503005002c180002081408031100100000d41803051a400c1e141c4e84020400c02120b4595002c1c11810050040c90191541108155840504030400d0000a001c81d4424425100d07460b400174561490246513800b400000c16001d00071494041d150503000c00011f101c1c000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 694964028 1106 694962922 694962937
    0x30216050f06030121060c05071407050f010809010905072d0f05041a120a0b01090b0f010c032003090102070603050f01030204021c0c0504060305090c130b03070b 71
    0x18402d01d404e0460001300311b6818650201c0e019039101026100d560f107e450199801c84e654680345886264034090300c0d0b000320f40402400300c258415100c59400074201d10000814051a45800e0f0505103c0e4000d00c0030204d9005100c142d0088109041c0d50010200200c00c4c8082d05249200107079006a208580c0301d980c8a080e0b014441d038109100c528001030041411029428040301c00d81c507a6061001503038661585c00001034460300d603010385841c568000b00442c0e810169500152441d40001c0744c1a02044560b001e0f40d046181901880c0900480d608000c40d03c2d045940c00080c94641190015000c0508250611002d40c0070101824150f0740e044402585404c0700d14140c4001000c0700d07489420140c20000741c0a49140c115004006450391070f40d003403149036101103200390303103249840701c140c3c20500c075101074500304c0013681c8180161003004080d1031641e5500c16510215810865 = true := by decide +kernel

theorem cover : BRFrame.Cov 694784172 694964028 := by
  have h0 := BRFrame.cov_init 694784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 694784172 ≤ n) (h2 : n < 694964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
