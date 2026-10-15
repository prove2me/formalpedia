-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4011
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:19:17.769167+00:00
-- url     : https://prove2.me/submissions/a5dfeba3-cf08-4fb8-9c3b-09fb0e7505a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 721223021 ≤ n < 721402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 721224271 1250 721223021 721223053
    0x103090609080c0a111e01080702070e070216290f0c0601031208070c0209150406030507150f080403170a0f051602010c02061e040323040504050a0b010806040e 70
    0x120f000307800e1201910390401d050403c0418812844440da008910455100300007007030300d038940c600c054000d00b000c44103a11245002c0303140c01c0d465040a501a030b5036070140841560001164007c03000d00004180d50300761620903000c3c0701c000035808098003000c1084000400e01c6680060004404643c52650074620200001032400d807082e8025281802c08a04a8044a1b40034111650107803403401d15550104040d4082990140010920f180354050b83d4200d08a030755803900581d0081d500320302165407d5031182d407812840c00081400f440442c0390201314641c61402941843d10864041e100d030820054a42541080031400401b4141070581c0c4102204000c8030360b210300c40c01580b05014282910f1281075010b401c48414404482c20355100b00100080c00501d4000c1c92420b40441c04031400710340300c3e0b1405072080e51003030303c2c420002503400d00c0c1c1400016942014004840d02210f0a210b207894a200c5070301120808100035002401e0030340040c0540c20980c1010365101c003c070080301d5181751201001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 721225521 1250 721224271 721224277
    0x80702030705101b0c11011d090f070e0108042d140703410a0f0506060405010e2e09020d050f0702010c0f0e01020a0c060513060504080705010309060908 67
    0x40328441c0d031298074400f90201c19a000011303045030300780003000c0d00050305c030340900c1d80e5680c45140c101700a55a00ca1711840c40d4501140d600710002d804402c250501d51000e0305c00c8941154400d0000c1c060340880c1a041d031050302d0150285411400c0003021003a00400b0000b0445200711410301c840c024401c07080001c000000424010990001402c040c40c15072074402c0040800c1c11000200c1c841c0c1c1d4160160b00e00341e050100003080800c0100240814040e0300150801a030030001030010384000b490300040c8400400c0440c031400701210100300c2680c840c000d803007808000b522003100e01c02c84040510500000c8403c2ca4502c4040c4002030540569584003e0050343d0140502021003919142031003004100020140d030060400c1c00240a6400310341002440c0d0706003c60303000d042050700301e07030362186034002d01242d10200c1d006480305400d55150389001d450340e4041030708694101c941190028070031744503c09907410350b10b100700a003d00038a441c00450240400480c10380b461aa00c800443c0050180310003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 721226771 1250 721225521 721225543
    0xc0b01030b071202130b1e040e04110a0e0f04020109030b0702010e010e06040b130c0504060e090d03060e0a0f06170a0c060f0507060c120903020309040c050910080702030705 76
    0x194405882e100e44018800d070781c00016002141d006009880368800100120030580764400040c0d40c4819991502e071100e102d030005680b0b01c04800043c0030801c440c2002c41944554010707035900524242c040c0a01250325040d200e08100800e40c03e000c80c84183c1c801d6400b6410600500d4144001e90312274580c18040c0c2400c0d520240541c1d950480c1c082e85075004c1c02490441010300001c2d00c01c138641070300c500444040042124881001003104503003004014101a000341001030010040103845501025030440305440a14040c4940040400b01034403070b0091800765428224402026101c0d00078120203024044181d191054880e0004a04440741091034001c0141d6040181000d02d02ca060602c541501600800c04205a400e01544e81c1c0b9000360807641050340c45807000031050040b500440d2484004030300c2454031400d052119050690000c060180384104030b50030411030610500031380e1203100d011400341e000000518401c10043c042c6050030751047c142c0c01503928000031a91201d080141d2004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 721228021 1250 721226771 721226783
    0x5070201030e100e0c1801060e13020f090901140a0b1614030415020f06010308070206040b13031401090218070e10030609060906030f17090d06060924150c0b0103 71
    0x3a10031340030340c108118a5004002c0c4c50500b82042009001000102c05006607020f020000305110095190a40c1d040b1603000c080d0800c5444041e41d080b02140d17944900100303440784ca06a0004140482d00e0002100360400c010030f040b0340780d031030100703001c003107811062405005100055500004c143c1906009003088810b00c06140e035182045542d0b4100074205501c03d04660100600d0380c100080050100e05488d000318409454505a100141c424840d0350001800d01801003011202110284100002c1da403156078070103120005c50451a0880340c2d1040044c2d0300000301099034100e1590130a00c25089940c51070680d00c5079051501207416560030846140000340d0f200f10411104c10345218440c0540780004080c8011171070f684507030725003154498018142101c02c111240c4580702c45811103000103c0640358484440660401c6402015540300e00b08210b820a860b804a9141d003035031081c4038003400081c2114035070600c00054141e030100c0314800203200c071960101c0c0c0820007507902c00c1e008521800c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 721229271 1250 721228021 721228031
    0xc110312041805091e030f04080c12010507090303050714070b0309070602060601122d1d010203010e16030905030f030a140405031e1c092009060105070201030e10 71
    0x1450b403801800310701e51200200c1d241074184151500c0205035003801e40f514141002800d0741250030b041c103511400040821160000600280120000c034501425520850b40000d0410b40c0e507101e503090b0f0b001115124009074202106200290064025108190088240040310b030302d801e480c28076118a5820181010b1004410042c00000400c40000030b801184082d00c0f5a060050018100304403020313440707003950342323400010009480c9022800d0910000800100d82d10040c8808170b0001c1c01040e440402c1d110f56007401075801c540500840303040301d00c074030070400495072080b1013907803070a103101d28039400c0580340c02000010900402c003810a551008110a540741400762030b4204036814014003100c1300b100d410420020480102c1940d00e1041d09903000048403082042441c1c591080d5144c079288a481c44100e508800c440c1e42c8542550b0740303d502c41c0c44024143c2d0090b04030300c43c206441c45a00491001c001240c42d44164040c0c900c0510605011035942c1e498140e0341d04004407084c00c40d10441c2c1d94 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 721230521 1250 721229271 721229279
    0x301080303041b1412010e01050f0702070f0e01050114210105120a0b061c02030601030f1101110307020112090206030f04021c030c14070305030301380a0c11031204 72
    0x518032a4007160018040c03e5000c601c1c0c40800c000403003080113100c1c031440c01401d903008000b800303420001c00c40081c403000708050718000e00d944140d02001e0390003030010b200d22800441c42c44a4004840c09984003800d0049050780f130100111035a02414203c942c41c14024001d51a0300b500c510905c0e00380c00e40c02600c900c2190304040922040c03042420056502e5030080d0103a2003c12801c44120703401006c00d455007003250f80c01c10f1103890008141d01e4000d4140c41200c0c0000244422000001c51103031045951a47d00d8070040e004681d8400540c40005c802c1c1c000b0030101d4010b40c011090a4603542c81c4410118100b840354001801a80003201d1a10894405c039040004500c1d125139071040001044003501200400d07500c000780504100c500040001c1400395101303084482c20001c01c001180c4c071030308482c0d9a41c1c513000b80601003510242c40c0842c0d1a07203415460a10151480c11014000c1b10107019800d24002c0d00c0200c07505e01f41142c00752141e0070701d40c504c02001d480038010125441c5816280b80d07511807030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 721231771 1250 721230521 721230533
    0xb0304020f01090623040b2206210e150a021803010203010b04140d02060a1706150d0c03110a0c0b1e01030201121803030b030609071406071106030108030304 69
    0x12044445040100c1c000b800d00c03046130080821140760f002c8608055220700e045d00e00301c0d224411504408000ba0000c100c455880c0d6040d02411012440d403007a150b62217940d28410b903a40041d502040602d100c880300c008020400340d502000c07000e1580300c04c5901c28020624500ea19401c04d413945c4e113030796800003072144144210060008036041d05034021407941d0715041c03a110542c025400703808041c0065100001244c0c3e5800704084900b82c004100f941d68040040006d0311180c4c000030803134030303010007040051200d1a01d009150f0f40321805581081c58010481d03865001480c84180200500d50b036040561406603643d8058600c001107a16590754184044c01d090b00405c00003411080c0006411485800401c10b412030141180d40c20300380f000780000d840140720060000d1105101403443e241035081d0a0590503000080680b0302501031340c2907030b215580c03407684410241c040c500c802000003420f8841400d114005103c0e09006483c10396240f000c6100007078031644207a01403034069101109220174050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 721233021 1250 721231771 721231789
    0x801080607020f071701020705010606110607050405150a02011404032109020d0f050a080c0d0f08070914011202071103010b01022404140604121d092e0b030402 70
    0x80d00d0004003601454820040d5641126001741359404070524903066641d402501604c45107540403000b13121043e02c03130400501525090070290a184240d0300071603103130742c00b030811201550760160080c0a40c9041e0100d100c0d003903000c9190101150743e180600300d00035070718a40e014081c9229644030345003001e5804225405d60350084030301010340d107040072000050b6035103284440d449500c80e4200080b807203607080403418014070a0000d040d03000c0004181c0c6060f20081141040c400c610303180c0c410040d070951400c48005204680c5000400c040d00402e01c2184100c41903100702d500140f400588000382d10701d06c0c0060741c01241d4100c44d121203030b16081080b0b213030078005c1ea0340908d0300384001c202034002e06070303030f000d41e514919140b04040000c6004501400440d8070b511101040c120121005400c0a10301200d40510340748104001450b441003c0d513607070280d00100100c48030003c00600442c2c5804461a60110740d8020403207482d000c0c0d040000c68240041c1e6594001c050a42c000f68691602d801848178a071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 721234271 1250 721233021 721233031
    0x130b04050106031a040c0201020405030a060b03070b03070e04050a0209031906050f0709090c0507080414010f11150903091009060f0201091a1902040f060909060e160210090308010806 80
    0x150400621886110341e84d110040c2419086401280c0004982c20a034020b100b0f90308095014080d01700b248040c008a60061070014030250101c903c22a640c0300e00941d00d0000b500c59800084151456034190b2800b60021a004a0403000041ca020350140010345404d881c005030001aa056071110010f2042d0b17481102d61261422081043d076150421006083ca103d034001c20300a07941e01d201d01074840d4415016200070561000c1959502c81d1a074101c170031010100d108030390014000c1405148035a11540130070440c5140600282a022006008514407a000a2180541d44001e10841136281c0d80c41d80c401c03100c408a600c5070a0000d0a00c00028600c5107800801415a0704164005001807240940311618281c0c96003080e03016240d80043c0e400000c004514542014000b15022400401c07140a1500312002034039030082580d0b40300d044000b6940503104941b1000d04450010701c0c405104000e00002001c1c030710640d100011750141403c101c9800c20402e40c00600050018420a0001c2108035046 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 721235521 1250 721234271 721234277
    0x60d09060b0a320d0b150a030812091f1a04110c06010b12040609031b2d02030703020105031008070305150f13080c0304180b030c013209130b04050106 66
    0x403c04603008200300c101c2000000380122680b50014901c1051140c0281480e01e0013002d11752034950301d083c0705200390000c480b90b0030355042d1980400d10350880011499640034021041450940c03d0310b070803e000b07208000500d9604d056100360301060b943c4600c034001070502d441c08d80740d440d030104088241ca07101c0140c012040e05101081040a00d21840200035071243d03200c18007140060b1185411682d00d038171114001c0785550804810760400481e07151001c1c900c0c40d110600f0302600f100c48100c00501709000c00194040e04807410520140d440b0308021035120440c6c64071101c00b241d0301c0046503d000c64030303032003994140c01c0741c030342c0b483c0500c17403100481d4000d040000c41ca00c00303041c14203081100003d0090000c08103800011419061101070040e01c00402e5441c1c2500c5420414651140c05010102c130858400d00900c861326480350f0181910889402210000c0c8041c51101d82602504047c3c06410341162841407000f14a15900c4600b000f0200341580380200c1c0100c00300c424001920304c107800034018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 721236771 1250 721235521 721235609
    0xe1c0507170c0415240c02060a0306151e0c03050f0c0c120a050105060916120f061412010501241209031d090106020a0f020d120f12020306060d09060b0a 67
    0x7043d46c0500300301012601180da46555601221065000f09203e50128040c402c501c03000c1152242c0003801d41d585060600e0110000b94003e40f02114201c04401d00140868800d200d032004c0550000041c020180c0401e044070030340c0031010009141403094a06032049076016110f41c40170044203014550b04858191140380301410140c8400d07440203204900300e0f0401003250b103c0c00a00b4055044065100a007501c00c110007622090310501000740350f02214060290f2601010702801c051003444d040b50178108401d0034400c01c0c5c5151080302c00200050904208484d0108543d0702014030560401d103101c2c0d00c0320028040c0c00d400d900c0c0c0c20030108101c1c174812a020401040300d560081003040c4010390142518580c1e0f0074510015548003030802020b80143c0e4810303400d1030040e8000c2800c2c80b01400680301c1d00103680d81c9640c0807050b03100880700303240c01950600c811220704005400c00c4103402d20071900810944100b0010030442d9202d075000b4919904180c59040c41c9203172402c11080115070038840110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 721238021 1250 721236771 721236839
    0x3051c1e050a050903010609050c0a02010e0c01020304150e04020d02031501090305100f1b0302030f090a110616320703080901050702030316030e1c0507170c0415 71
    0x4518018281c0b000300303110300011558103c2c1c2d0b080d0b1000d800f8100150301004141010b4040801c26086004400090f43c03804c5004c04400c0000511020031440c168025490b003030608070050205842c45003008248181c04c00300422594490024004403d51100016201e1405100e000c0011040c8150281442041b003402c1c000301d080032a1541d82c031203007000c0125040d1034007211007005146440310801000003620342031380410741c5500214020441260074041c1602c840c2e42140c0c45204038038008000c1c5074034a00a800e00d003131600c0a044928055009910700728050b48401d003404004040c0c803a0341540035030b42081103103022030303800c036995111100505d00c0718216511030b8094071800d0241814028045444c50856504004941400c0e01c1c0703210309030700001300e441d020301424090391440b0f1182031805103003004460b60044010115400c07000070314007549000800340f2a0358807420403200314001c403424102e80d62518054000505107100c02c0c82c2201c3d00c1c0680c0015a5141c1c0c40f00811007608003203200c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 721239271 1250 721238021 721238027
    0x150103110909160c061a01020c0a12150b031c0912200a0b0d05220f030e0f1c0204201b0709090f050106060912060e0703051c1e 56
    0x2e5024040044000f40024054410f50781062400342c0102402d007040e0032402c40440c071451901e860340b800c0e0221100d0303188242c100052120540150701840b0014141c61000c03d000888150708801c103c035000510702164004241040401c1291882a414854415644c0c5030700900400060203135800090518026580c1c1c607100c07601d41246038403003814401802c1041d030b5031030044c0307001024680c030406d03940c0c141c010062001d08000c480d01131118841442c4030a0b039200040002c111140d01c8030441404482030ba03410f0300c4003640d5182c041c1d00b100c9144000b450b01d48034640450b00f100004c0c241c0011407241c40c0704010685000075a5034a4a8941c42c9481101c2c080d810142c0d445030003410005101f1015400d40703246024000e5220010b0a42081d940c0414881402081045640603000a111043d1101e10541d0900300c1c078840c51141c1404244c5005c04260035602c03440802c0392175010303507004540e20b4441d10310f04001d9681814100e42e01e1000001d0094011044001000340c0307000201040410340030103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 721240521 1250 721239271 721239289
    0xd023715200a0504030b1f030515090703020112051e010b180406060807051606050c071e05030d02090a03051e070e0105060304080d0b10120c0503040c0902090109030b1501031109 78
    0x4006c485000c01040070705e00014054804124006064444a0364074100a036895119860f00c03001c02c4048004900d0740307000854440d00f640d8040e119601454038241120700200701c01483c99070304460390603840c0e5a0904041c0d04600030a0640ca4003510b0700080e036030035131950300d00b8160306102d14036100080010302c0e00520174070b030b1104241c20103d0300c81d09907030b02c17440d0500c8031004001c0091303180c0b0041260907204480900003182c00303a91150b60b02a0210305074480060340480280141e48144205540020281c000300140f40018050004544d6a0b540301440c041d099042507100d00803141000913015000c00c4988000d00e00003682d00e0a0394035090200e40b0501c0042c0002c3c240b1880021413100c00d060a03040003500c9400501503803030000029100411030742c1a5640401560304002415140074403a406580c09540c000145a1090b45172180190007540103000c418140f149260000000c180c602c28801d228566a80140201c45641c000040890300c04419003c450402406584110b498131010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 721241771 1250 721240521 721240523
    0x10509010e07050c0703061b031e050c042102012a0303020307031b020705010906170a0c020c0604090204051804030806010804050f0a050106080d023715200a050403 72
    0x11050785512141c60480e4a445114003241a074070031000000100314103544020100021018070b910720001c1690200d065400c0004051181c00161a44008506859012540080300000c6040c50035546c1c100c00f242c0c1400620114071101c107010184030965030807888012018126440080b1070501c12103803102401e02019000c1d04055011000901180c001d0780669034020b000b170310003a92010700d290020b5568520340541d0f400502c100e400014500c1c055a815001e110a10012003001c0d038408140c1c60051000700d20441c110321451104a40545605000b003024000e501005030707580e803e050070321900000500c001d103001040741d070410000c694000982a0009005d10780080552a1400d046240c808030400f46100e5018844010003040015441002110222010b81d550140f032440c00340d882c0c0c0c91807060b580b551030050035460841000d0b81c6215007544000e100040e0b0751482500d41000c144426500c15049640d20303040b20510800d00401039403180003210710b00d031a01100c07130002002c2d0b002e03600c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 721243021 1250 721241771 721241789
    0x80f0721140a02162406260d0e06071a0f1006050304021507061104080a0b100e0712020c0105070f020f010504021c17030c040302010f0203030408180418030f140301050901 75
    0x101c5c191081d840c5180c00c9402000000c000c1c4019a01e50364050f030001f2502e101d044568081031080c415101c804183c0c840b80188988a11000c544107006001155000303480840c5e19501c0200c10790602300c01d291520b4050001c00810300c00600e403a5000345000c1c0c12942142d000c1c00010b00030480182d4a100062030501141c5100a444500c14030300304000c0d0002c0d402d03d0b5003442c1d0108003c2181c040000e1016410750043d03850503e5602c401907881c0004002d8018400c00c075007008001541e00d40501d0f070010341614030108c01458500010402421603805840640010700614506c00c00c00c0e40c1044500d0b102680380c6c000b0440ea041075030000399002b030601200c800c203940743d8a1103c01c4c000768041c100b090452170184a0307901c1c0b50892083c03245600c140012800f04e40111489060381c0c1c80001a2031086500c8103d5502c2c00b2003680c01d003101480d0180e9240c0d40241c0381c030354400c107540040c1e540900d440e220703440c0c1c9202400304000c068041c1824182c20f00c038042007030004022656410105174110f6840780 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 721244271 1250 721243021 721243043
    0xf08060c07030215161202040b0904090221030a08070e030703030f030603170909010e0f0a05060a05030a06060e0c0c0718111b0709020a080f0721140a0216 68
    0x101c2c00780d0400245000d000c8a0000b01000c00c018120070f0840000b8005042e035501c026050f403000480101d001d01d01a5410300141031028085c00c5c141640103c0c0050300040809200c01142c403200c0500318200500c10340b550b0404100c1030081c0e500264202e81001303550501d501d015071401c010a03510482d511018081020080c9039011107406035100310045d6800c08928803102406245194041c0d10440000d40071b1030000e400054504e006030500d50280c09440111012902d4400002c00504405401140c3c80841031030001019902007020050301d61050002181252401111880c400d500514218090b1010428202d04800c0450620f00340d50f5528034010440380e1070103401d4000c2094203038a1021200001d08031094808a0100b40300003010a000c40d10302c191125000800d038090761070910045030081c8040f69540d0b501102c1039910002a00d48010314004102404100400301810092069616072001e41c9104509100ca42c0c800004001580343c0b80d151301200c0420480e180010348a940c0710 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 721245521 1250 721244271 721244273
    0x301150c030915030e120c0307080d060b030708044404090204060c050f0a0f020d030e03010c0e030708070312051c02040603060e0f1501031a100314010f08060c07 71
    0x5a07a4000107400d0f0300303811034181903815034042e005001003418a102485400800740c0c417000700404590b1aa103030600a942001d615a985000710b41155408480341034a419010540800d207101a40c841c140720307a90407850341010b0800800f01100e007440e00e0140c61040d019a0150100d494503011061110039122a031a04182c0d610043e41c002d0344c0140c44864000240090740e42e81c0910502c03d0603001d84181c8034490300105001c0c0e130b00d140602c0000d08001030303440004090301d803612604040728081c0c20701c4444882d0040c0083c8c00c403007140e40c0a134049110708407940b4103400d0400003100601000380003808400e00399121700c044100e58441d00420480009403000c0d0f80130207094210401109800c041d5141c60b1107603001703000342c131072805284500c18170800010500550002d9280c050280300c0040000800003c1c01100078043c1d035824102e200c41c01410768001515101e91002d01840245d030002500b4080c07a07810403002c081a44091416181d0440600c14418045596600501020780150b076407889 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 721246771 1250 721245521 721245527
    0x60525141b0d020606090907060e0d030c020316090f0b06030a02030414240c031302090705040e010902040f1502030a031a09160201060f060203031303051c0c140301150c03 75
    0x141d025500c0d06030103008000759141e40c0026205009000c02c4400311040c4d82c1c0d8a11850b5600f000d0310503000003e402c0d0404003020306048480b03520440c0030b403500050620306500801d1030004581d140307900d42c410301c003c1000a001030388900e00341c6501d00342060180b4840c0310b0000e5924000a03101d4810f1550000102c1c0c100032080e0411490265480d081c0c4041280180c0c0c005a1090404008104516401c002541e1b20b2155821288102d0060b81ea141e8484029000c4c0102e01c0b000070034050501034100808194824841c5030140280000030700581d5507402c012582d0f8464007036070300028031244201c0712400310035004426110b4903120b0703180020342c42c0181e03a0381a286a00340300c24190000134030000e1022540400c6c0c20041501d0303040e00244400f582c0d070b1582801480c6503100d40c0d00140c1042c8003003142c5104070303452002d401e402403401d54280300e420081c810704c80c0d0160f94010703800e6070303150b05201c48035401c0120042c0341c0080301e405604661400b01c50103500c1c883c003c0c2480c20010031318600820140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 721248021 1250 721246771 721246807
    0xe0d0c110a17061006090b0a030c02030c0712061103040c090b0a1203080703112b0609240e040b2e12170a140c010b03060406052514 58
    0x106560500c0e00602d4191841925440161400c0b100540c0d41c41c00407a03094003a0b688a8101c0d40c80c003c4003442d00c00e841c0390490080202040b40c0c000c501040007101d02c10b0390104a114043e1880344210440300d2400d1515904541550805012000c0144108004a00702c43c64050440e0390029000c90079005101c0007410605a80d081112000c160ba40da00c0d0900d5400001a403080b01036440410403100da2440320320160007450620503009010141a001c1001c480030300310300f0080310000201c0c1e0305803903c03601c006940341d110082c828200703c0301c840842c44c10384003a00d0006004000e0311403c11300b4907440d540c0344400014001e00042050000007041c0491000d4440e001c102c1000c1c0300801c442d03d0b002c1416440c0c143e15000c1c0d0f400510141c0008500c00444102c1d512039181e1303110151070302600784c001a0355070404812030710103550310307c019030381a1024060644594820013000500b8a01317201002c03450030000c1a4138054151075040d030032403190003101105d400700401e02041d0715102c0b50040300003a64 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 721249271 1250 721248021 721248029
    0x6020405060f19020c030d051321050d090f030b04111216060e0a0501030b060c03070312111e090f060f0403060522110402120702060603010e0d0c110a 66
    0x20000240c1c4401c2c082001e001d40510015250a4509804125812a95005c5452003640e26800008041c04486c0c0100000d01100043e410000001c40d1b0340e285540404c00804044201c010070801a441000000d0111152001c0ea0381044548036003040162902d00c0c0b150300000740481c51605c0880c040c0021024112015000100a0003426000111039503c841030301c2c820440f0b04403044c0c408135010b800707010b060702d071904050b03d0010203914040044018096018907190000c008200e03400351136a0a00041951703d010361a201658280405014121185100208000d070310911030607280c2407800701a00c0304c0c1e03c9101407550302e880c5644006980846004010780d8004d00000780d0495403a50100900200c0740039100401a5598490344d04d0001150a040c20303440d05540000c00f0000740c003440b4080103007400544011b013840840d01d00081121429100800580d2007c0e0810460b4038090240d64034940b002c1000d811103080035038014002500c0102c00034080c01090070850516103a00416400074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 721250521 1250 721249271 721249279
    0x30403290a060501030f0209010519030603050a0f0318121112010c0207050f060403080a030f1b020a021011030a1202070f0b010306060510050418140705270f010c06020405 75
    0x50704041c4a41002031001e441941d0100307040114a204400700c62094880306641a12201d1408800d003181c4104942003410704018580d40b0b00c80030009c91000c0043c106090700c1141520071115031410042c1083da01c82809440071509504140252030303819035000070b0307164410b034178003050f2050300c0c0001c00818281340468003540c40c1001880000760300180032411110156202e8140325100418004c1c980716074000640313076110030810200c0b102d103e5071108581c031181170400240d041c1c1c2442803c00710702c40b403070003e401603010802250540c940344c004001d00700c03e542450740300b610101020541381e0080a0f20a03060101c12005a8140000e6404444003560300280d03200b81c01c0c196103817250390249d003804141c840526145010803181442525a00d540c2c6441c3c40e000d061620740152050800400000c20340000c2d2502c43d4a0410321890303038181e02481c1c55031503568584c0380b61050461400b0080075030844000c4c00d00c5110000b80c45803046412404401e01c1c0145c20000d25003041c00191207268442c07508 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 721251771 1250 721250521 721250603
    0x6011d0103093903111e040615020c010f0e0f013f06050603040b040812070203031b040f05010e0321091f020601062a0f021f02030403 59
    0x41880300c410005940101060f01c01214800c000d480200303070803203000c02022400c0300030003074080340313014005585c4440342400c040b51518a6180460186c2e042c50740030320848156010110f034074a406104c100c1c0401d20030b11780000703110310810000700325041010380d0f18000e404008402003a40d10444039221808080304400c0c0e05410b129801402500e0411b1010020700545280d0210b210307024026071080391401001a4107640b070395150036078610b0002c0e00840e4044000c004511600501c18032480c4280d4094025588900d88203c1d90501c0a08060740c120901d1400c001c244030425241205809072007003840c0900c0484064808240b811056170080c1404102c941144a40f00c031498004100451056503402000114440f0400d40103500350300407400b50b00403500603c036191040b50f0300c1000d980100145400300b25140c401e15850f8043c0c200603030341204180e00000546c2000c100c000c0b000c000e0340521018210424100035107c1c0180e0000400e400d5403004940340341a0a00003260755200d081c42500b00f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 721253021 1250 721251771 721251803
    0x306060c022112130e0c0406021f0b03100e07050402040305070308030901241505030723090a080106230303040b0d1b0c0212030307020a062f04090b0906011d010309 72
    0x83c134025240b291100e40380b240c40000c0e080404050a540c211072085c0c00500c81416040c42c4001c1110005a042501c15900d09103110555410481410b680c41841d00000e2488280c13900d580c1401c3e9250001405540100320400000d0f03c0081c408040700c0c3c0100016482e40c0750030500502421000e101c1d40d00f150002c045903c40d08021401000403a45002d000c4072075800150001e80f082e010455a01010461f0140b41e20410700c400301d0014401600142ca152404440400150007081150440b0401e0b80d035a042c2403014090f44d0001c0041102c0c52806000500840d40001c1c1e500d10850041a50740300c40030803907c2d60341c004c1d42c116442d84031308246506203603200c05000904114038a41d090b4032404c0d81707a0108641030350200449000b445298003802c0d450700300c1c1d00c2e041c014003203101241c02030384035581c2110b0802c40ba0300e01c1018001c1d44452590380c0e482c640000c20043c0c0f031155031582d200c0c80200d01404200c1c1c0c1c00107020035040b216980e0090002d01d1210040c1c00400240c00050014031454907402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 721254271 1250 721253021 721253047
    0xd03050a0b04140a05060915041802060d0c0206091606180803030c0d050f0402031c050f0301080703020a0f08030406030e0316050f0d02060108060f09071a0a0306060c022112 76
    0x58401c0b10a003004009a91b00c0300d04003c1d43e0001a0b400d0110030100504a0f0050706044d04040d014030452484c0104014041d40130954035405911b01c12500c5a490050004d8203505100e41500104400006c3c2600c0850394010342e05204c140c0f00b0704083c803900f035410780503074620209404010118202600d440e4941045107091a80c800c0700140256894900002c003c03120081c00640559000303001000c8844407503c00f55864108486808140b0074188042e045000111000318040c1c6800270207484024518414032040800c0c03904494216007040e8400d218041001040d10219a031918020071442c03141c2d070b126401c40c81510348680490541c29a540207000c000189030f05814240021911a0383ca62003040361603960a00540941d50004030104196a012242181d08030646ca000e45161075a120000c42c1c9501e01c0b0481d502e20072402260501c152034151007060018455403d10040441c3c4c1603002516064008007008102c03480a224900c1800080140b050f45211a210b040e41c0c1c0d8040400351 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 721255521 1250 721254271 721254311
    0x417032d01050913050d031d0102041511030a1d060705030a090e0a0c0909090813141f050d0f0216060204030c060309050a0803061503360d03050a0b04 66
    0x14500603d803c90104420220307503c20b0b1034032180c0043c064007604046c09000c07030242c00d242c010100035140d01090580107450a10041009102030441e02e02034044000014100800d101c11a4060f42c00038080c103408180c0101c07841100c0c91340b000d401850301c0e40100002e9414045d1400180c41c921012030815181034201022400782d1390302e900c1c40546503841404000503550840034100009524000c108212142a003148102c3c0d442000682d0030701100d08210048564103510403004240d1a20443c0250b0900f5624580c40031030001803200c544c0100e46003e01544500d02d40144441e548400341e40000020b62b0641d100e003421100101042c00781400c150707000c1d400c1404281d600e01040500003a000380244610060381c0d600c280500b140a2090300d905031247c000400d4150804402855175005c1450034004522480d0000c507100000016001140c0102d07496413400f40f4141208007804110781800070342c1320000d400500d004030341607a50b01031500103011100b07801d80d04141403050002032080c1d04802 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 721256771 1250 721255521 721255529
    0x3041e0605041a09160b0f0904021c050a0c0e121c09061403010828020904030f030c020607090b0703030b120f060f07051c0e0d0e040608060417032d01 66
    0x1100500744c480c00d00c11626030300d81c00010400c86910300f804101b100c0300c1002810058100300b13111810528400c02007000e9074420000740858a249401c114a02c0b10148070311604181202002c00000c43e40703900140400b022200799520a5580c41c0109503c3c41040007406460301c4a000345030501183e0324400713060304000c2d0241101017090f1540640190012001350ba0403034a601000b400012004020381c018402c4851030541c02c80661805a40503844514550b03028a1090343da1111803544a0310040071194201e903080d0841d00201e0034044a55070103004802940c40009481d40d407412039140c150004d2041c040d40c030750044070441c500c01000501003800d5041d08010310595555581d401a44860017100300c1c1d4031f001007217091140da20440c1034180540c0b0006004100050722102c10521940390544078030541c00091845000700c1c0303583c20305009100007416100024012401c26079038003880885120f81c08011000d011002690740e82108445044041040d500c03e075680307241d00d035500144030342405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 721258021 1250 721256771 721256813
    0x60e010e0d14040905100e092d0604061a0301050f071107081f1103191805060412090512030403120c05030d051902040b03061f0503041e060504 63
    0x400258500076440420491003150b2001d01d05414124404028100036200e4103c19030301010226107000159013440c000c003401c4006286043c0b0300d6042c5007403d10030a032101166580c840c203006d2000c50000d182500142d100030040b49809541305040c40c210a51611a0b5166013803009100c121611110b003180075801650312039840444c85410b00b550b0700e81034800c140140e482182d5145140d92801941d80c01781650400c00f20750240c035841d4201d0307540c00c180d680340440060003840840c400618400c5031070403038054440c40080c960944400341c49510042020b03050200d41207a81c400144140701000142900901c16022060031144240d070b00c0d00b06000884404054880d0b00745001d0250a21305200c1d54044001c500d8189204041006032102804501c0030007540309080307007100694009040030700300b412165030700c078540071042080c400008640c0c031121134040143c0c040019809001c1743da10a801c0003501c0e040c6003209188070392030028164080c081a1400d4180010800000302c0c0e480b4210b4241 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 721259271 1250 721258021 721258033
    0x122013090b01020c030d051e0d0203091c020d03020708090411032a04050d060f0c050702130204030b0103020d05070503100209010206090715030b0a150807080c090d060b0607060e010e 80
    0x7005a03500da5015541c0c6601d40e00418054620a02c100010b180d111985094965990618076168842d40c0000c0011800c40750080f08115425404000d1251b182004040300a00ba04401e18069103c8420750003030f1040680004003c0244401da000300c030f440c1d4002800412005511480d41c1c540d030307001515400c60007501048501c00030044a4152007040304510010761034681380004004c140080d41701c0880e205074441c1200c19160b100b0b0b00c18540d00d185151030340c5a40b03100341d10410110040d41003408100030700c1813005001086102003d603041d6a41510314007007410f45410054904010766201302c0d4140328003401d00c40f00d01843d401404413050280c007110a40e4680e402d800b43c031882c0d035001d13205442c1c040005541c501c80c400c1d0040c0c4104070002c2d240340702c0c01d501d420b031101c1210001405003002c129444d0902691076803124407594402010001c55040c40340d8040042c0103480b00071805080b0175102d02880b4000e5031030b00111a08281d10150070030007070840e522224080d08114442e08520300600d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 721260521 1250 721259271 721259291
    0x13606080f01060f080604090c0f06030e03120105121528020a0c03081003020303030a0204030c23090406060b03181c050d1a1221070312201309 63
    0x203804076040c0c8142c2d440d54502941d281c0c104a6011100405481d40503031030b2110203010520307036000d150240500101128803203052250180540b40100300c510000e5008101011905821900e46415601c0881d0544462710895542900d8489040f070491200b85010007440000108005043d07030300c0300700b1500003444085820a102c01c03401182c03115008101c0c0d42180d400000d10445c3c3c450750001d0000398520076030303449401091568004a40c0c4a240070360000c4c050003802803160ba020020450174459441c40f10264224600003c9205034542c09880548045420840d581e00442c0c060400b0390704254482c0740a000002c0303030000d2105002e0040c064501c502112100d482c3c0c403400c0c0031449864951a16101d50201e1004220004800c614540032142c030319800e60b100007401c0c40c030902a400030040100b100d00c0e00011030401a16640d2211030030044c0800203500420345c003403171106e03201001540d01d00000d940400078003840c040d48c600140c006402c207034410211103050300340c0e0b0181c2c02c104420040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 721261771 1250 721260521 721260541
    0x130309060c0f02040e12070303090b0105090615070320031306051813200c0106060e01080f06040603061113050a0806040b0c0d0513050f160501360608 66
    0x100803024014158401c82d540160809402041c10f5084040c00c54802c904604e80842c4140c10041c0704800007502d4854103428400c40c0350a45015120031101190300e8200400003411050b102260640700000c0450703107100703160103011703400d1000b00c1d00702c4200c0c500344800c28110740381e07401310700c1c0014070804183c40401d00354407035025a91421540e50b185070f0342c14000300c10800c841d0300103401c02885c0e1361100c1e54105038005034030340b40c402d8100524020303031100d41d40c005c09425241150403003010845005115035080ea40401903a422030541052003a02e40c440c1c90108010742620340003d81010300744507000000c01319110041148070100500e109125864200b00300000799584216500c07540404003003404502c0001c1da032500300308840f000038a481c0e20f0300c440c01c090310303030480d081076040680c510003109200d0705200010701c03005414041d050b00c00307c00610140c1c4c00c2c0f0500929042000c50007204000f00060150075080140d03000c1a000221180b05008020780018020000012840404941c44100e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 721263021 1250 721261771 721261787
    0x9051e030607182303100c050405040e03160303020405100305130b1f1e06020a020a090b01051b03040306110a09060f020c1f0e03160608100e0f060306060102150609040c030b13030906 80
    0xc61f59888a107028549010403001d80007443c90790301036000402480640e80b8400d0190001144070703490260300c9528003c1008410100c8540d41424142810f0800c404090f0021a03c28a540e115800d40f14507121450344000048420041c182d0081103642d01040c240200d014040a21100250f050a050b85580b070880e00c81850301c41c025001031030054113020003029a080342c9a01403040c50301d02d041200807041c082174004450100301840c4c00009080c400e10586005a068941c4c403240c001d45401048000140046032034401c440420401414004559100b4001804d2100c3c004191280c80003555090340344c0ca4030002c80c40c0b00812008040c00d080e60402040408900b50801c440040e800e140030401e4a00310001800002040318a0070041800e092800312140680d40c250504001440c04200741468000301818490548d0301c2940051701403e070345e4070419400030040d41c480360a916a03107400d18030a04240c10042102284104010f0440100903180c48124025030b1050141130795800141c071011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 721264271 1250 721263021 721263041
    0x4120b041e17030403050f0f0a09090c05090d060b0d05070f1a1801050f040608070e0a0f030f2111071d0a021308060709051e03060718230310 62
    0x140d9105115082031042c0303000340d6800340c020b040c40c61803c1da600324030b81c1e420303440420424100440445e481e51030f540d015040728045d14048004100c0c0d0129024082c04a000e04032200f8400c031a900944020414290080e100065001d003030205410031303d182158030340350301d8003516400da0364680d4009501035202514056241d6041000307484d00a035000c0300b5004910000503141880410407414400711500ba0050004060a40e00d010442c14034903002416120b8410011344500a84e420503c40403030b48154460444e0780c80b03c04100004543d140100003842c686c0c08010100381081001300e04641c0019102300301c4030000c070a86484545603040307140c3c0d4008098070714407088040000640000d06580c014010300301039100b15100700c0e03500d0301180d01c0d00004a9002c000180007000403c030324144942400a6806411000840c0c2e80810007c281c0c0c520004110b0000c011400c05040c240030300f41d0140705d0241024007d4496141454103180c5144900038803810b000c0e220391210380d5602021407180900003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 721265521 1250 721264271 721264283
    0xc0301060804030810120b0f1302030c01180e0c0c0f011107020f1807110712050a0b0717010602070e15152109010504060b030d08130804120b041e 64
    0xb9101e40d01e00b119280c5005000c00600a070070000030031690910480b143c2e0b158031603002e080c203524007500c4107001c000014002540d62007200702e80c8001a5004510380c0442c000038070704030703a00c2d0400301081ca202d064564040340b02c1c00041c04c180900303d801600289100d400302401c03110a603109010083c01c0711f50480268a1140052044600518200c2540c1c4c00c00c02004102404403295500c1184030300400f0358031600030441010a4180c48a02441400d008103201c06000c0706038507054407030070b40710b1201000040075509070f6400192018001c080b103080341c508504d0b01020541c1c440c02d0107560b540890045551581e800c000181c40d40d42e940b6081c258801000d070000740c145040e02e12000a6800240145040c1500d442c20050a044034040c2c591240c2403c00000c50181043e0800c041200d00584141c1d02a400111b40250a00e4008643d5904600300c203031400341082c203138100340703040707000c0d64000c000b0389401c0d80c2001042c04060728005020354018120040000c2400d02e603c9100c0041803002040313 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 721266771 1250 721265521 721265537
    0x10503070801150c0213061a0f031f0f1502060c0c1c021f1a030d1403091e030306010909020910050f0d0606020f01050702010510172802090c030106 65
    0x920030b222041c03802c43c018103040c84003114540c001402c4200030002400302503a038020411905c02c1c405403146000c143c20903c90b01c0c10b111510103190910004104881b41c0000469042449a01c1074026008040c0514030007003141e12550503034400d039401c040300b01c01441213070041203441c0c00e12406c90b88205401e01c02031001c1c0c00019400401508440c0134002940192000080c1e2803a2342c900c40600410304d02d000240d006c00c1071400741440141e6003003041c0294001400c0d09501034010405400c64145c4045e9161a039440307058903072810165801c94084411129404209480000080c50140c10240c0700c82c4284d41e141d425040482c0617028000e980201c14000108501e40200002c040403405201010320b0a100000700c20140c9116520107401039100c2005504804020b00c40c040d00133006200030321035400c1c0483d03006100c01007405500b40c5044060745101c074520701004140c0044d043e4000d08034001108031400080360f0901d200990048000b00005504003407800700300e9040c1c605a480d0220 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 721268021 1250 721266771 721266779
    0x50306071209022d01031a0a0e180a080c010f09110402090406030203010921170c0912150106020c04020c06040605270c1305090c0127090c02010605010503070801 71
    0x4003034410050705a800a18100408502c000d450941210392805030202413403000e101000103046990104040a681d0740d004110101552001c1500c01243c00c1c24010000c192a5506100ca0014035180340342c40ca40f00b1410510304029032200507003a0094000000c202d054190711a000c00d890b04d400e00102130300040c0e80045024a0958060042c501c0d015000150141d1130364042401c45007a44001e4820064010010583c1d03c1003104c029418180361406040c0c0c41603410704525080c01c0a804144281e001088009080e10b80c2911310400031407480c11240e03002001040c090002c0c80030700400c8014043d0310701c0e00e00c0303070b050500031510102e000300d0040855948039120340c402400b01a048061740c80341900701c0c0c3e0705214443c0c000c40100356120007520320941028100310b5000000c2283d00e202034200802c100d113183d008101003407d84020b0a0401c42490212031121032030780903c20080611006090124039100c13140d00510104c001078000708405038556006403003900003181c00c0e034005448040140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 721269271 1250 721268021 721268057
    0x5060c06011a041d0a05240904110d110f010c08121803030109020418060b070b0c0408010614131b030b040204030807080d1104060c0308100e0115020705030607 70
    0x102e04281c0518040d06058403408146129982c2030040380090381c068083c00341c0078005200383c54126403c00d12940b41c031004080411009040015003174030a211240000f014807400e40380060700313100014040043c1c2d0a8500e000c1c91010a01d1126a0040300014402459940a10860303001544c004c2013590800e000452030f00100030004010740011030040741b882200c584100013541c081c20800d0005621a41814640002251000c0340c0754036043c18010101301410307150048038070b12500500940c803590f550362948031300d5100d50b0340010300c00c6d868038600142e940b0104043c0058803008981c2c0382e040d40d180750f08280076541c8010100c1c54200c0c052910034009400390380001e038a101e01a1002d4185540c94541c1c880da43c01005003680d080c0b03400240458030a8031407090070b02d1010740e0f9000909050600c000240012100100142484031800106521400f110b079840300804040403501d2081d80c40b040c071840c078502099141d0001d486203202c041107525001c10040d21440142d1b80790308119460311503803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 721270521 1250 721269271 721269299
    0x605030910180b09030c0f240402041b0e011d090105060d0e1005040218010b04090f060e04110a060f0c02090c0d061415030f0103061d0f0607080105060c0601 69
    0xa05010b10707604101000041c21202d000344102480d03006581c0310400701c0f08103400e1040300b044081650300300b0004840c0300c01c0d41242203d15012005040c41a0b6a00c0740702040c0282140950f607510441040301c47c65000c0c0d8400000c0c0015803003a619110040700300040310304d500d020a403444d40c2c23024003800140500d04112010704032118500c040800c0c01c1680241c200e040c140700442103209151200100802e5003407010080490300303d640b404174a190f251101c058040d000340d0007110f10040c1c86840a055032042600104050800500e08dc001130800d460314110514000c1022800360b01700c1a40041c2550041c0703070200140c440d030388030108900c9665080045280c00144011050314040c042c0c400a8403107842008081d0540c102991400b45055080000a05507070a240320723401002c0081000700206010080e04483d172040c804581182074030b0700c1e140940c0880c0d50520310707071258100d0007000c503100049040c0201071320346846000c0d9032118284240d07840380100c0c2d02c032190f00010040000040d9580a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 721271771 1250 721270521 721270541
    0xa1202010c180e0726250210020d090204021c0b0603090d0c080c061005121908130816050a0906050f0d030e03030c030d0e241005150d060605030910 65
    0x40740788109190004911178001c1000401043d2265034100604201d041c01c84920080c40a02d0003507020020000c000d540c1e2980700359080c00c3c5500416a072071340d644140c00c0042c00381c2d4014800c1d5203555450b210001130300d0018915107416400c0480c503100b01d0030b00e0002c4034060118400a4881140d90501c15103080403c00070898008404104800c0c21000510449006c1e1808006107540d051a24040015000c1d03004035151543e004000c161084081d0882100c4401d03070700c40f801c0b645031510610080740884a0b035000700ba0b83d000e9418185c0c20f203000d003524541500c000303c0785203d038a0340701c1c0140c1e011200640283e80d002103040003411717a01e20b40840c801c00c04034400c0c030388603000b102103001090071500a0f03020042ca070361001c01c410041b00354500401500030103e0b8000c100030054400c0b000365026400d50540310640111001c00e4510341200a5003019180152055003542600c84141c00710354070010404042601c0c1240126201d44034004980c01062800c0050075112402903d0740020403103c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 721273021 1250 721271771 721271777
    0x5040206040b1c0c0503012d1e03060f060308090123041502010e010c0f120222060206060d02151c09061506090b0a200a1202010c180e07 60
    0x100040a150724401840c0c0d402940305048107030060f0403940000e5682185900302440002c1c8014000c01d008140c1c10300d410070540d141d900054130303104030320b0904850386d42110075170340041c1c80c0b80011a02c4800c41c0d001201d20540d800c1228520301e0031990102c98542c00004c1c80e0400400c55080e583d07200b4034070050b0032002c0600c024070442e054615070764680d00c20791144c4840c2c020702603d560220740a11814210f840c0302c0d4000d0240c444000001861000e500150741d0602000444081400b42d20713134107545440c0c0c502c0030800520101c40c20004d410000c140700d510014070a000c006002410312910300800360381d01504081601c101507005074855000425608a00210501c0b0002680250f002e08030100d4044e0500040c2441d203020030403041d40d4103820840900000b01400c00c0316218400c1161a030300c00178500155843d078000815148108451301c0440c40d44580c1281505100e804200c501d01f4883c2500200b20480c076108041c3d581242c054003005207068076001c2002001c104603003032039105903245 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 721274271 1250 721273021 721273027
    0x7030c0e12100504060c1d06070215070c32240c0303040f0203060c0a120b0f1801090b011b0204020c03130902030105010e010c050a030c0302390409031205040206 71
    0x303960021602d048605440355916800351b105000c2d0070032051144591081240035800b002038010a01d14440c0701d200034041c02159084101f688810340907074455540c8110b0307244486680340c0c07059000b52700000c0011603595640000599810807c6414205038030040c000990030486042501d25012201100f0390088100b08107000600200307000652189104201c0040004003c0c0180742c58201c00800c460100c802c1002820f2103150421031007001c081640c3d0021514511800110380280080c000b5641c205a007107440d801c206927203d0710360341641e200d82c2040150716444030044940110000a8007040c60700104482d025082640060a812540d4421649004602211079960480301e51000411540c00700044c00341b903a000d080e00081c0c1800b441c01080500407500c4060700c603c0006002024000c51074201e104241c000c0c41000340c40c6200ca520601c0e41181040a0010340000c071000700c00807400c01c4040c083e54946072184c130403200d80543e1820401c45181200d40f000f4078000e4002d9a02000c14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 721275521 1250 721274271 721274293
    0x20708030f0d06080c1c05100f0e1b0105070f140703050f070905010501080105101101050c04030515070203190c150b1306080d03020a0e040f06080607030c0e12 70
    0x400061520085504816a0b2803031280392540c102c620680148015800851681601d59140b8030440f840300150032101481c04030340d2410502c0d01120882d1b400748141401c200c89508881a404000b4620f2060240d80c1d0700c8514401000c200d079031800e203a50108409010340d002082080030030881041c494183d182d05c84003107818041c075041704c81d4021505031380300c01d4000b50050024010200240144c903000e1000e5410040040c00107441401007e01884141101d802c00510490800001e100d00000800c03560410402d0410903910901041d40e80340324a080c1c1c0308861a55641240c0710300c9855011314200712245440c030101c65a810814020000c80124140105015018214984240003000182220501c040c03001118010074582030030752510074200505407002ca0302d10f04010340c1f07217801641ca82d00c0001c1503403084110504503420038038001d0003220605c0c45038800d8040d60080303401c03181503a0710218202c05407980301035008001017082e28ac035150f03030030031a0320000c5201489094580c88050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 721276771 1250 721275521 721275523
    0x10b0a0b0405120c0a05100309020d060509010b0d081b071d0a0c02160504020309030d110304060e16030b13050a03030605090115020703080d02040f06090e070507050616020708 77
    0x1504400000c00000408118a1910142d220035201080300a0130002032550005451203180c1e01c616400385401d00703818000c1c03911075170080c01480c1d4010600c401a002e142494001404200c6054031503620303040042415284c100140c0300a2640109458540100c20407103900c4039402803000d070003034814140d010803000c0d210040303899070612188952203035152101c10841503407040708031a0195017210350540004420500c0020035103034181d80250343c0b51075104070b042c55845020754449145e49441c40e402c900b0910b00303004501650280109225508035215040d0320b804048510400031110704408000042d400d01110303612128200340310604000940350b00e401c00090280490000e0782d9880c05210901e02350070080d016110850342c100a80e105c40d0320182d034030145408042e080040c0421000d60764415034048030050144071044820241d034074100548211200c0c06000c6811610344000360880d440f801c02c3e100c3d10398004000b050300d40c565a4042e641c0c020f406111000b180191b800115102e28 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 721278021 1250 721276771 721276789
    0x71107230f0306090a031d06031f080a050c09100b03150d1203020a08010e100306020f070525050612060103020d0902030102160c08060915090c040501030807031e0f0c0203010b 77
    0x451004c5d1561044625000b40f10340701a24143d040310292408001c0303e51546000e03203511a0702c01205410b001d21600740c1c070302c865485034040c0e041880303200d507480c1c1001004182d950b00c910040d529842c0c282c80f07100c02c107010310294ac0180341142500340b000602c500310310140c401c41c40001402c0005000131a0b2110285152040414000300e50000796103502e040d03005d404280106241450000300d030502c002c0804100e011440b002c3c021980204851907a4020041100c000d1030784401203070001a20f112004440c1c0f0991074003201500c1004074006103601b40130040310303903450f510340044c095641d0701c034010340003504044101120780703540d9400d000050310248020a000c011558041200354038030318250b5034001c22600b20b410b19070041c20601c0658680003400f0418000e0280c0582d100d0385d10320018a24011300c0c1c566840e031080c02c000000061254880041c80350703a009503181c04450110800c040005c0b80010b10020019900340d2040702018802c41000504a200070008207210350404000f1f51006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 721279271 1250 721278021 721278031
    0xd050d02070203010204120b0604110a030c140316140a021c021905160602030f090d02060f0d05160f0f030f090204050103051b011d06070f06050a05071107230f0306 72
    0x1a00100390380d000d1040c2340315000da01000c200c4090100e203110000300d14480c000c4111803001e0603102c500030308a040c01070f42e00c01e5419600e821001d4580c40c0031403510304102401d84e03000300820b24820b5035161010841d0212420b12085070024003454940c584a28140104c200c0007104502030030749000812448240c01800c1580214020b03c007140348900a4488940310354492070966104000800c4540038800641e07821103000c40c0d00c131000300c0c09400410380c90300c110f660842403190300140d090804512a0f10240c000c002e101501d2801200c0d0764020b858407021002c01d4004076910f86c45202440d032280d0442c480310b002c5480c021801c4106580810140c450a80080342d01d031708100f0040c80c982101008656081d00246050f100b030100d0580d8181300420548101e40c0074090015200060012000702481400d600500c20070851802c800c41000400e415512030000550001030651384403000109001600c43c400c00440100c80c41d103407c1c0510a00c2d407010b09800c04c1112640701c2a59505010b82c9102d2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 721280521 1250 721279271 721279289
    0x1b050a02150901090b03060103090f0c03050105060a050904060c1b0609062f03040f02181b0447070b01080307030e04020a0309170c0f070501020d050d02070203010204 73
    0x20500c10440d055254803014200c600061001442c0e503070f80f2071080012600c89072405a501e841e1a00120080d042c4940050680ca000034a80020011284031140442e80948001c200c2e40d203070b4504110078003c1c80d1282a41c041c241d1000308021500d0340d44104901c1035681070500c3c00c100700324198000f45502076016981c0503910004001404414011040001502140c039242c1140d0126080c20001c5070700701180c2c200c9808000030f0200003040d440f40810540090084058503a86041704000c0c0300129003800d185544e89400b041900280703815901502d40340c84640c0500d80010a090700c0664065001020003d512110b0b8030032041092200068058424051580e490350b608221900000680c0480104c1d4001c111a0000c070390300c540082c0ca070b424229070143c1c0c0c500000c402203000d442000005800c81c00000300480c1c041c0012001070805030180d034295220030700840c000d6038840c400792054a0150300003000030b0001d00d00c81c00040c00108413040d0018100441c0b500800c2c00c9800c16045102e0b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 721281771 1250 721280521 721280533
    0x31401061406040506041203020a08030a051801050702190f02061233090601030e0d05041e3b4b06040e060a05060a0f12080a1b05 57
    0x9510300114181d601003030300350340c07081c5000d00e04008221640b042d03118490501559828900825200f44940075080360400710880e00c0741403200207103008003002d64a12900c1d04440600d4000c0000c10b0088910904c0560082d0071007080c40341400340d40326801c3d80219401e42d400448100140d44110141080100101c2014200c2c9020441c58884001c0b02118251510315210030b91122051081b01d910550416902c0540a8542c0c1006070060485603080885074020500405040d581c440c0c040c1089858005403110014003402c0790074610b440a0040b030b407480e816018034400b82c525400820104604250301c0007081c1040c1000b4101002007036600070f20b90307a900e101c20f03d003500c055038101001c50405005038818400f0010070810441a44a903d4403075224800020030b15502c03580004400c02d070b80d00075200c0d40d01e80081d0b20802040121030043c4640300300d96000c104039400481543c1641c141182d40b00c0c5807000b940381d2011940140c54003104002200f88d0040c1001c16000c51942514803c0d001880 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 721283021 1250 721281771 721281779
    0x1051909022505030a111c050a050903010e01050a0513050616050c0607030c0207090c0f080a0e03040902120c0c070b09040912020a050709021801030905250e0604020306090c1303140106 81
    0x46c0c04950324040511b40c02002204441c45040389410005100c50400c250740b02d040360b1007070700d0074020098841d50551a0401160022806411041c42080c440a0801c82541c41031b02000c51301d8071521018003aa440040003c01d1843ca14001c40c8021400d03003455414003030800b22483c030b082000c130346500009407182800840a03070100914800340004844c01c5c060b0baa44101e0044c655007c2c07690402c200100c7d070010030034a030059403003150003440310003d0b82d64030364445071038401a600960010310100d1205000594031040502999222150040901013041c94010322555039000b1314038007540306541d100a54001400d940070302504031004e8018098907840c0c1d041540c1010740e247c6c031540505004000c00c0264841c1c40c09030040c44502424000344616550408900c0d0a020250344202c0c0d00f540360140d8450412044d40000f00c401c3d408460001d59110810303c03040c0e02050380d500340c11170700c10700201d404614180060001c101e690980001e6443d500c0c0c41d00d106070100c0c0d807200d03805655686c500740 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 721284271 1250 721283021 721283027
    0x150c070c06050307050a0c020112060b0408071d0402010c110301090c0501021005070f0f0311040e011502300c0a060f15030521040b0f09010801051909022505030a 71
    0x3000524103418002d0442c03500c000060114820744140204004008209508680c003d4a0001c20400903090400a150306d8066042c0164414000d400c01c602c250080000c0d10005071600c2c0340e04052340c100d000c00a49075507005540843c490482204c0c11a000100c508464800f48600e0410742c4c010020f0640d0203107408000382c00c103c00c942c08001000e05040411603080c2c0c10021100e160001f074a410119034903242400c034010906085040c44d803003c0050001294042e80300c001c0d040e81c0c40ca6000e007070402c184e40c0080c1c0c0d44008030109492012000081600c0c0c2e0380c80d01c407407071608c099104505407a00c141c4032000350234000400700440b00d499440004400301030a902c01c0c2800f0f072240700200d107a89070a45e2580b540d60011908020f408400d180c0d819081540a20b0990b0000e10b041201d054880031159410304164000c030810a000810000001456240c00c00902c03185524005445480d14100f00380d0f000a540007450411302d0341c50b411942084039401601030554580110095a00c0e5171900c4001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 721285521 1250 721284271 721284293
    0x20a090509061807050c0a081303031710090b041e1406030a050604201906180e07180b0f0c0d0302030621150a0c08061f050903150c07 59
    0x3a010701c56580d51600f0050510800c01c0d00207801e824840e0b180c10042c155a4648258520010103000012800d401c41c2e054101e8040150303880303516030f601c08405503230079483e07150004c0701d940003580c212440800080c0030395031281d016001e002d0301c04038060b80d03002c407518862958240540c0034079544220140124500c0c908550b04820102c01070100c10381151202680c0d517034007501c0030f400c003c681440d010360701440c6454407031707000d802502a5001482152154080070528442c020201d06100246803001078000e00d0081601c5480b080c000785501d03400000c0f01d07640781c00103403082e0045c3c20003070110301d007210b510140c0aa00307010f0b50b000c0e0341d8070b401004140c03c01c450030030842c0602d4018014045070741d840d442050002982d11070541145260b40a906160224503402100c028920609008000c0341c1a000070302003000c0354481c541c49803180018404e20303c10f0840845402d1410145020b1405d21840050480260040482d612150184469a821141079480390a04000012100d040141c02416 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 721286771 1250 721285521 721285531
    0x20c0a0603020a020706082e03140106050109030f030c140f0c0a030203030a0804050a0b0c121003080301180e070909030807020718020306040e060a0605011409131e020a090509 77
    0x4103508000c0fa100c0e001c0d41e6491a0f02891051005010024008581407020b1a445c00d1100c102c41c00e125403600c00000c0304a9890200f541e0410b0316224001c0180414003c078011294185c2d01d80d280c1d207241d41c46440380c498460008508101d00d8020314000701e00c003e007055071a13003200300c007904240030036104ac1c52401001118a07405905000403c10140e6004426070360f010b201c070704016803980d5803803501909101040038010800590081880f1210302407030082c0030204900c0e0250403140c0c0728040041d80e5103010b444002c2c9002030400c010700c058802d000d480c1040410405010030010060205103040516507004002d46c29070301c101c02801d16030b020008640240300b03030000d04842414200c443c01e00c0643d200741c12010a0b0000301203001c5807500e611500c7c07210038072001d803501c505103e07140302d010f40094801c550008140980d035000d451f08a1003100d11802d4001d1190841d086e00d140010301400d80018400410041c0340701c4500341203890f0000340300d800c07441e43da1a140c19041408204640f200500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 721288021 1250 721286771 721286777
    0x90b040e0a050c21030f0a1205070807120203061003230c09031c090521011d16230307210507060f0219020f0a0902120a050405030706150b0a020c0a06 66
    0x1e11400450b80c0172085814490040d01d001c2d80e150346070001511072101302805054505e250004014000d0b500c1000640203948659860840d01311201d019000c0e40000e45809a202400900340344000303000b60302c08850b5014800c0114125100c500fa6514201021564444030041c00100c0030340c2031405200d01c0da018141c041c41e0000c0c41040ca840203002e01054001d050040c450a591480039004010f11104103414002c000d2080045c4104424000f400040b503005d1140b007024020003004403041e081006950042d1842e5116007291a0383d810412028404c482d018001c0c003c020606102d1600046250924220005005812454040d280c4150342c1e03c80820000342d200403040380b0380e011071011410b86a000c44581c09500728000218040310a0b42132540c40324076402d0010b040704454002d0003801c07100203410300e0203039901c1d00b61f6815602d003141d00510740d4104020401c0061200c3d840501546c1c1000503004105464800b02211603001400300005039020100030b003464030f40b10000d000a001185 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 721289271 1250 721288021 721288069
    0xa0302090301180b0c030717071d041e02070204020403060516090501030c092c0109090c09020901052502210c030c240f07210513090b040e0a050c 64
    0x38031501500580a4112416845c002000c107981d075100d522100640c0006034401001c500309100b014100c407145071295418080124080c1a0900c0e191144108200d401e00a042020144036802da000394410241268015424000840441d80a1181c1482801c5203a42000c00a071141c1d0040c100c038089600c0303a4101406c050501d184258807490000c01c903440c181180742d01004994021054041450100100f9030010000092510654202c007515501555010784880c0d25403020005a10446540c580400e0003040f0a43c1004c0b04111a2403880d20360b00c00050200404c4c1d80002c04d118041ca040410320741d41c0c0303140849110350911a00c140280c00318000d101c0300b515500414004030b2074010b00e582801040c00d18098050040d803c49001090311081c80e9624401071402045500070500d08a6188458600300c1c481d0328007801c1100d58a05004464050070b41c64481480041d20200060642113034442c80c01001c140001c000d2403e6581c4500301900c50001c401c4184840d103466031a065000041751 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 721290521 1250 721289271 721289273
    0x7150504030c083016050c0d11073b060d2003030f030108060105100212070204060b0d0c020d0f09120f0212060604050a09030203160311030a030209030118 68
    0x1141003039079803692040000d9240d40107005110550104580000080039501001c0c0480d900d60134030b06413180c41c0003103041e030398998456000c0390f890144a90b420181d5000c0d80c0340340b40480c01082c0442c0c1c1c0c4a40c50b0100e07805030b6100c0b07001c0075001190520b0720150141c00c04541c510b0742500c0103000c1044103980d900130010b2801c40c00041001105582c00f41081c0b02c80b800c2801c00019010000842040140843c1d40d1059100c542c0300d1540e000b4454005240600310010610746400340071880100d104e80e00030b01c0701280c8501401c8c402d0340100c608070b0b400f80e070310300d000500204c02c10040c10724880d01f02400542e4180040f4042e040c088a020035408202c8203c10441c80a070f0428044800d0350610302c038a042ca041240f60211f020101141d01940c4403044048480c210300c0e000503403c1c40341074151001d00ca140c581000d41c400781c8202405c0180035030000d0101c0c5602800d04040404154000c3c03408007070307200000e00040c1c1941d004100250009800060a20b500c0c2001d010f1584005e0891214081910032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 721291771 1250 721290521 721290527
    0x190e0613062c12160f02060c0304030b0a0506030a0302061602071a09101817030918040c0b120109020a140d0903021506060304080c0f010f0c081e0105010c031709030715050403 77
    0x71100922580b45000c4400a54071203c7c169500005500104c03542e46440342480d03421628200c1d41d01184030300380760010702541030115501c0011030340750b0002c00260700e4030001c020111014012010851080007800905610340350300c03d400040e1225009035461448400340034240e450010350f901841b203e10002804085e0b0410303e03804498043e1402004640546001800c602c44d1075102a032105c0004802841da00c451070030f15000e0381c450200c44855554a9842d07a1700e600480704141c0c00000414010040340a46400078030310001c1c036182419440d0b0a070007058100b6008441604185559500070000701a010011410a11000803281c4a0b41c80e191000a00340d10006000a14105010036400c943c01c2042101c0702100c00d07150028010020214030302c000038400f410041c4002021070740802c1d81244802c9070702100760360607140e8100d50ba0a04005440c0d01d01c0c4154100e003000034103184d0100340703007000f00c0650144010314007550303a541ea5401c119082c041803040c408421442d0bc414840002c6d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 721293021 1250 721291771 721291807
    0x31d0a1412061b070309030b0424060803120a09052d0102040b090f0604030807122706030e0c19090605010203040b04030f0206070b0403020105190e0613062c12 70
    0x18010351140d42d82015245c201e07150003060303100508005004080c0b10400440c3c2003a940b0302c3e030000c0c804040724000c010004007a10240d00c181c6901d03400c10007001e8201c51900c0a110317031040c40d51102150a05456031880d2400300c2c080343c01c3e01d06205509490f8650105500541120b0740624025820142070a4001145218084840d4416200481c120100ba00c0d004242d070010342c9c001200c1ea0301c543c103505094074241141d0415030b000880108101c1c0110110061104010240b07030803000726541090740c141c00034901c40600921a2040001c0100b4690b1480c00c1c0001c145c0a1440c649100b5140410a03401c0d1003d61b0051819500140003c1c48052000400d13101200c2e00044c007501c21507000d000cc90405e01ca1401c000d04004004400c2209054054000c24010f0b44060300801d20295881c1c0b1900444082d0007a41d5115000b65000c1840384170030610340d00c2018090f074000a440d00140401040d40704803030082080b0060290b1540000107800d10002401d0310091030700e680340c20341c01220241c1d050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 721294271 1250 721293021 721293061
    0x601030c020a030806100e0a03030c0611031e0402040b04090606140d02060703051309021605060109050c16051009050a0b0a11030a020703020109081c05010f0b07031d0a141206 77
    0x606041346443e00c56000441c80b601f000c0c2408001b0350716820014102e40ca8001c06440050420642174a09010002100d1007001c40c003540c0e40342c10444003c2c1c8070171000040c105a078442e0b1510301100c1c9558130341c45040a030318403600b00014001d2615020b284085c41d000c05440c070682c88010040302503160700089038201e81e45882d0040d91084104099100491950048070000d031011840c1c1c0080305260520a900c64018002c5aa090b81c0ea8960401951012211a2440c000501400d401358542130080c00340940b2800540b44d5007030b202c41d02e403400c840d5078090030b50b01c550207180e100c01030180341005190020400d9100b401740a02d00111042507100181070481d0440e400280c00d810305100b98002620b40307902003605a61001406041a000d20fa4104a012003624050001480c000e0000c43d400442d181c120313080e400c00210345c1b41545c198100080d41481414008045007082e620030606c0c1000c0c08002c2c070346c184904049003d0104581e559286c28010354000c03c240480303480a241e000b4021 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 721295521 1250 721294271 721294279
    0x12070b04080309070b0a1d0405101202041103041208010803031003030804020105070203010903050c07090b130b0a09110403031d240c030315033912030705060601030c020a030806 78
    0x280c03503c0c072010745440d0069111421041c0041413002200d6401495003011180341745050030703043c40c0c200c07c0004a03041a10451481100940104211040c0c0011000400e000610005000d02c180fa10551540c0c001c4074100d6920312550700300314119801203c500d02420515000f141140342c081810b030281c1c240f0b07000c00350074803001e400001e08580c403440448599550150090001e008280b6014140b9007041070784034842e0090200c04200002c03e4422070441400040507406035004c0d00d0304403002040d00c025495041360800c41e012800001c0b03409850198040800407950f140d166080040140700c1c012188940700d02844541c1c1d503141d80e000c1c0c60400c0004903650b40c00c07150100122601191107502c1c42446603020110401202903418414041c0d03011040e02516400441c030034144850409080402d50418101100c0740d070040e6103041d51402c1d0710300140021099940f502480d03451900700080c00c0380d940d030009041003a0317968140500500024180000c12424005690140c24044010115406 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 721296771 1250 721295521 721295527
    0x13080d08010b03060d170a1e260a06050a0e011a21092d0f0304030312180206071101110303010501020703020103090c051018060905090402040f0e011503020312070b0408 74
    0x344000c42c1c858211b01000114000c3da42c03101040090240c1412541d4100041c2e0954051501940107044021001803040e240c00f40d0400042c040052178071000e880c0700c418558a43c000f10386a2200100d41c406024213440100b0340398503000800c40d016030703819250104503009015181c4030741c082100c20300e100b0021070300e40303030a65440324130303142c0351012045016182000c80b506035001079001907032a043d0f00c1f9071a0103440452001400d0580c0d244118800100040d0780f0441e00710718622140e004148030600340b503a40704101055000141c0700e4110003020f407946402c08901203001e40e003180308008001d0380c0c6805507065624100020352516158800a814542c40d01da044c1c0400896100c40c5014140041c00058440d1209400504014240c985444008a10440402c0d694003810182c1d007121001082c081c0e140c0d8a9600740000341850158261250740c540c1d010190b54502800b03202168011242410041840d60041502e0617281c0c2080d440303081d80801183c80400c80010417598455000458a55 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 721298021 1250 721296771 721296773
    0xf07020d1b08100c0e01271508090c0306071b0b0c030f100305060403050c030712020609070f0b07020906030304090609150501030b0117091213080d08010b03060d 71
    0x80c1036000c040000308a803071000040c0801c4000d00e0203810954848104032007035200410303e500e00b00d034020030a5030081070290414100c5036100c0c0c50100303c2c151800e00c164000c10070180c1580c03504072458001000304c1000000740e00b241741d807051049074044201402019002d074414080b03522140091308103000c001c8900405290581d8035400c00031103d0703120104d6400d03460080f14685850b0010340781d00b84848680c40100d4920f000008200040c1c0b41c00801802454685a43c103503440c1d48180003585207030105105920104000190f005010400d0340c000d0413583c43d0040f161030602d0001e030800c59a03082544001e009140061007603c00b0581d054445421548901e0002403540c0130710340c00780e25001d041c101d001c203200244d0b40003001030182114000c8040d585500c01942501d035607051a600140c0c410305568421018401d00da41c204501c0c1b41a40c2652061143c40c0e856a80039100001c407100d40e9200c200410941041138849c0341c40c036841d200f4482d50501e030303061001c0e10018094a01c680704500601d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 721299271 1250 721298021 721298029
    0x509070803070605010f052d011413080c100915030608070f090f1a01030c12090f140105060310020d0b0603010306050a0501170c090405160b0714030702060f0702 71
    0x502400031241200d4950165103003800c041d007401d014000c00c0803085800041c981c1852042440c003c0c5000b00641c0c5942c81c001d13891255240200003190402200805150011003400700500184208049410b20300b801d000d0740614011089036600d0141000d4000183c804e07a0100325142521045e540c0b5030301e200ca025908070301801c1307950820451030180c1100040d0403625801c894080300e043c01d109002e200400001801198804102d40b044070103880d001c0b000d00d6109900030707800c440e0305080448016030f181e80307600129007000030112422400c440303c11007444000102c0c0807201401030001d100314502840883c0e00c9018000d480d5940780e40214200b40e120560ba007210388400c8d0041e191503201d69590611801905040d2030720594146000004108040c55500b2441c01940b01001800764000071014041d22400c001d000b40c64500070024003024580b25034101c280101003e0b40342c0b50329480030f814090a00c144205100340755030b0081010100580303d441c1954029011103c02588075207681c0085 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 721300521 1250 721299271 721299283
    0x12040c23090f0c09041a040e0616030c090e060a09020d0905011b170a060b160312060f1e030212060f010905010501020618031e0a11031e09060f0c0102181807030509 72
    0x215034814140642341350a9000000d072a4400c24504500ca111011444030540071200c181c0752181c00070303203254414000c00c1007901d001500410b01525040705a80d9808040c012600040820801140c44d005c00b501841424040c0845050305815101107240c901c2070050144001c2880480c44042807200188001e646580301500502080b0103066555692000e0303208000c024010850100b90071401d803410000c1d0600c114016500b1050041c0f40b42c3c0e0500d108001c01084840c50f0100c081c02070381e400310058480a101c0024086000c00400701800c02c0d95907440c034068140c1111519910b0700700104103681e400a022500001400071802c03088442a00c0c0c039085205e00d10f0000314901410884c81c10200a800041c424220945d0350305031480081043d0544038403918807005500e00c02c07100010b400c4c11010004001c3ca80d0010400d902d03203042d20b41d1145079070300310303000d80001c1740d602241d949070490741081c2d0040e00300d20031a80c0d1540d00040031942c00c03d00e20040c0c00070003050340e00d2000440321541040710b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 721301771 1250 721300521 721300571
    0xe0c1c0f150207030201062c0117010e07150311160326040c05100207050609060f04180204030204180b070806042003090f01050c12040c23090f0c0904 66
    0x6542d43c034450308020b40a80402d1181c02c84510b0140c85ca00c003440b80d610504201303100d103e080350f415a40380082c450b010300000c0183c102d60b07558030401081054820005e00d0001e004810760580d8660300c00401170105c0b0741c4403500410b290341c00c01810480310740c031b807078640301807039050030501d10603540750042806d20076044496040d070041003406d00c02488042c001644c111802100d00b0f104104590400701d0b101c070803900c00e8a03041042031150741032902c1c00ca000381000501d44400c0c9400d0a65954448412140e4101c000e000254002400d100754203040c040c5801980000d440231001c2c0006540d100700c001e4008140a0410002c0c070089900f55586030000c480011140e0300c5048640c0c0c1c1030300c0d00405580305031800c980904ca0614041c1e40108180105481030080200c10703814103544582e88128844002d2080b140c94601000100e480d042810340c00d403040140c0c1d020300800392081400e2024440c40a0b05891304414131004200b0100c05007006c80d410b045054078042044603180e841c1d00c0e0860b0300c601c1d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 721303021 1250 721301771 721301813
    0x1b070b010b0c0115140d06020f0a0815090c030c03040f0b0903280801030f081c0903110a150b012a03091a0a05091306090e0c1c0f 57
    0x1c40e030185001070914584400001c004020928000c028404185d108080a1511140a2143c81e2510380085d105607030103000003500e0b22403440c00c051480c2d8411256000480c03070810500c000d841c02010031111255054480c9960b82c1028865200315001c0102001102c00c4000001400c004c4000e26600006600040c0180b180c00d1186406480750040044046a2002c15210300089445542c540809001c40e4450145990858507a0f810402c850a02910f0f5900c0c02c101c0d000c020301d0031180c070810072407819800160340d0f0305502d40104903c102401034205540552016404504803083c0003070642c225120008484540030016a9000d0900c1a03080d9080c2003000342c0b882102440500203c060b11aa840551281e102d02541c0d034140441011421000d034103200040b01d403402000209030001e40200308010b038003074014a0a0589000f80c00c0600c10035102c11860505500400041c440340d1000c035085000602d00480c05203a41e0407086015007403034240000c03582800349044822001e083c041d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 721304271 1250 721303021 721303043
    0x3080a1a04090602250209070503060604030b0903040609092a0306051c1a040b0c0714060709060e010f12180c030b090d030207030815060f0d0f0509151b07 68
    0x4180301c0000e4011080c1a10803040c80c11040144060340c5204070002c41e80140700540542300c10f041200e00f40c0008003001d800010401011011902400d140d51203890110003c50341c8a0070844001d102c02103030303403000c1045410811603800a0f9010007102030201d45070128803e4130414480200c0207404a5809107400100c0301250713024011010034903901c940c1c0580903071030401c0d07280c0300b401d8031040003280c01034250f5603c0300100d2180c3d4400b2000b0300b0a24082c8010010528041691a08001050760b1907004587c0a25040140a410040c02c0040c50800d00301202c0c801e07032082c400751041e0039482540c3c44c210364a5240700180c00c0c15000708400e59401c10442d51030543c80b458503000c000c005480d0754140e0701c6501901000544240211203809134140c0c0c0d4007003107480d0403c0001c10340708a0401a40d10490612104101d08800f0018210021410001151091060a040085403805014142c080d0000903080e01118900388581c0d4111050008040c5041042143c400043c000d079a4010400c121403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 721305521 1250 721304271 721304273
    0x1b0d0f051c1d010203040303020a08070503120a020309011a1809010e01060b04060206100b1602010e04150e0f13140102210f070e1e0102190b071b03080a1a0409 70
    0xb0030350b0012405140111000740e103104070016681c034022440005c005a112152400000e91280c4c050034500380f00310222400c0c20308102c80f42911260031207410080700da0100411000160034003802a64554140408902d035030141c010500c0740040c4d000f1034000740c40c5500415100e510940c08078846505003002007000743c4c1c80300c1016500741e01034410040107100f044007254ac1820b440c07050318220340e40d42d5500d03440c1244052102003407403070222090741808900c0b42440703e81d032118080c4241554134500b00031200ca0406200b44100c10000d880f10592039645410020030450b031032040101d564020300d020348000490f20820380039100c0d2160902d8018001000440c0c960001008140035428813100c0000707968805c0001c56108005c07114081e84001d801258101e05503160300d088520050610650700188100b490400019003100b0f4112510070011040259999121014445d4409042e2050b0b64100703158a0003040e01a000e030a01c84207680e107155030182070b401106c1070308403200d015009200c10812 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 721306771 1250 721305521 721305527
    0x1905030901080f13020409030c0b1018060815060a08030c0601090606021c0f0507020d08090f15030f130f1202060a0207171b07171b0d0f051c 62
    0xea05180840c1072600850310422100009521071400d42404c4e2410102a80820002c3c00d40580d0a500344039001e040300000c01c0901000c240300700081080c0d602850310b0810040b40003054085a210510300d0034105000300307031012030710300f4440680d03403070104003a01c4480018003d40c00a500c01d003528400051900040e540100f40513048601c1904d0401900380d40301c5003a6126583d00d6580125100315280410a560044e41704140040c0203140181c186001c0c0e41c041107150024070000d4070382c1100401e1860440c0350a50341450316000580d50700928070780c000d00301d002c00d0002512076100e04008030002028828002c42e502c8101c0e400c5400038001c48050700f0151441101e08641c0c2c0c0050080d2000107840540038022641820f038071299502500b65101c051520b11741000a000800660012116003902c8040058201401040c100e02840108070b01c0158500b0294a0000400b480c0c049000c04e550ba0341d100c603c41d082900120b050420a00354503107a402c00140264549043c03240c03040000019034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 721308021 1250 721306771 721306777
    0x1a1e040303020c0f150a080702010b04020d09020406050103020a140d110319143706060f181d15040f09110901081216050a1101030b09060310020c190503 67
    0x901034400c40713900400c0a040c0807604810399400000c002c1d0810440e0a42da208101665000c105071000080302000074000074140e9001642602120b51241c0e440015803400c0e01c101c500078802420214640220706002811280071040b104482120100309980384298540080d00f201d42d034030b01d80f5942c0380740c40440b810865200141c2420050300d0540300b0040000d948040030b008603103050010b80002c0900107203081c81010110310403d420380c03c002041494106008480c040c201030780ba401d8281c1d090704c1006101011130b040c490701002c5035001c00c2040f540104c0750320403000c0c0c9001ca10070f0596130320310750407681500c01500c05411070b16008203001c1c9404158015172003e0f03c50b4900a24001c0c00100300601500c00380940340b1160000c5020000e107983c03450040800021605d110301d038004ca66100c5c5420030103402c0341652404400c202020b03c0f5a494801c444807400115840070060410340082075076840b02e2002101829070001d264038990508000c039519a1104024440071072400d4600152260 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 721309271 1250 721308021 721308043
    0x161a01030b06040501081002070c0e07110d020a03120e03070f0507060e061315142d07050c01080c040906090902010e01170c03060a2402161a1e04030302 67
    0x31440c480420b01510340f40c011300c2d0403900719000411a84001e03441140081d4021102150301003080000050f00080000300244540c10a0319501905000122118103081c40c621181d000c640100d4070315000039400c00c810541c076400580c000980da100141202c0d1640c45541d80103402008100d100750204103001401e0700c10368403103a4660352004c0d611824401240250310720701440414403070040c0024043d00d0100200c0b8070892400b1a01c802d41d6510050079540b001c0360a248a11100861890310003c0d00044841d041850340340d68540849501d5241e211000e007000c260400842c140401d856141e032005903400303020300305810000581e44240e0000200203415040707000c264001c010f64540e42c0100310401803d003941c1c2e03103111159101d42941c0107540c4000d048682c800003080010500307403040071070b038084070310980094082a05941406450080600041c0c401c2101800080c00559051124203811900121009440d042c0c81440702a070248811020110b000c030208001060503800141c03aa000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 721310521 1250 721309271 721309283
    0x3011404030f030c0e1f0906031e021305060d0b0405011208180109080f0307050105011a07030c0201031103040b060307051e010c080405030303040302030706050f0c07030c11030f101a01080c161a0103 87
    0x807a54584042e80aea07503079540c1220001c103101c6a0707031000b041070342c0080001c480404030151803640c80b000040c41a8100500c0d05020a95601c0c01c07500c3c0b41454482e00d4094881c0c114400b9110f513940d5281d82e458407a50941380250b0080d151003801c40d034080c0b1168000f40c00301000340c550b101d050615075552600b052009031200d60a0200000d0ac1d000d420344600c40300c0e48261031591814066803010b032088086800100d042640da84154a504110040614013552188032401d4403400c0000400d8504801d94210ba48101544022a04006941c000101c0c00c44028202030103a202c0714180030103a8052640035980500000040104069000c03004010140c4140800c000d00e0300c1d410071a480a20085070001400d4600b000b442c40030900900501c10036511510341c0c02d081010b1400403070f0030807054101e5400154811070300060b601d0701d6070086098000d26247c00c0c50303601c00e124000801c50400606a15042c05002886041d0540c80c01c950360b0240d070304100d00c2d030740d02d82d240036070f10300c454400748402c1d158 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 721311771 1250 721310521 721310537
    0x12020f0a030b070203180d030917030f180916020303060d0503071a0108190f080306060715061502031303081b150a0e030304111e040608010b03011404030f030c0e1f 72
    0x80c80c001034520104c41e01927503112507a90504c042c03940803400b401d00100403488240100401030308030100800340c240e05103020303508000100f000e201d02103401030318205402e00020840c1816550000a490744002c01b11038011545805041c118110311400c24043d00400c2c0100b489a002e04a1414943c101c0b45180112151410325544d14102c00e020030000901c541300c16203112002c10681c002443d004507005190034038101030b690b1560000710502d070b10204032544a0000f0810300c40310a11200d0850713024000f0f54540441c0280150043c50342d800014140e0801045145542d502c0030300e5910007840010488140c0d600011444400c014211650041c2e5801e040307601c0b03494100401030303034007c55100304071188040600b02007082c001c4160082c00d810140030303050b0360300c143e50303e0042d50003e010540c00010300016142c14103080d16030b044403103201e4429580034440001c2c1e00c88991044a2200c2c50700013401c040307605045880d00c9035142c96950141b00301000c86031030409c05821681d41c103100d4854240b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 721313021 1250 721311771 721311817
    0xb090a050717070206190b1e0a1703040e0702010b19081221090f0307060617070b04230a03080348130b0712050412020f0a030b070203 59
    0x2c102c60301140c90390010381201001c202045e8800940303000c0c000001401042104142c0301145d072055800c441860140c0c0a002142210b0401809010250a100c803410000c0100aa6907541d00e1041d485042c00e018010700001c1d00f41e51003940207015a040080c031010718150710300400e40a402135401282c505001d0010030f0015240100202c401102e0106c0560500c1d03107207059000310500004144079070600034010414440f140600050000c0e520690300022090700f01095814120b500c25044465648400c1080c00070340d9104050794100d0f0145c0d508840c00c103840300d414050f101d0f0309415554200c3c0c40008084100030140028520500064141d4038480d10444001d0103071040341614450071051270040f4420100c103403d03800c00c40c8008040c50b10b141010324400111036401d40e81c820500400b02003043c2e0200440450040004034052415905060810441031007403680600000e2041d4201e00c0031041944411403088021500442640c2661074110b40203912070340002c10014480c8602a0303050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 721314271 1250 721313021 721313057
    0x303090501030c0f030507020a12050c01110717070804030516140a030c1802120709030510020f04090e1c03020a090911040302010302130f030c0302100806090f07030b090a0507 77
    0x503001002c10f80d00c0003a4403490713440c103400030200645040c003140254507009011900040280c018082c1e0340d607030581d4039aa4000114211072410400020360b071020071040010a030107040b00d404030400f000b44265103014a1510a840e07210715440100300340144510428035140c40300c001022a090b240c602c004400d45401009910042c03800700400840c01c441c018801180418501c154140410800525282030426071070a14802100e10078005081d6540600412505001c2000e101103191420340c203007442c00004c040c1d10f02550203040803241e40d032200c03800c3c58a810400e4034590f90604060540811001000034040d520481800020441001c0700203007010180c492079407890b400c8007181d0709160a55004501075030140e88103d00807240b032000071940d405a00c0808000310b1240103000d0032a1314510500491102009210301400481030400045840d0174075125400410012146900d0740c8041055005040d21442c0540040d55601040194405940724500507503082d107800c01c25582d502401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 721315521 1250 721314271 721314281
    0x908120c0915090d0218100b120615190309020a080a03051806071205040302090a0614010f050f0d020301050a094d0d050703290402130b04030309050103 67
    0x10980103030b0156120107140070b69501500400c100100154500c601a0700003406c032210481c005211044200240020b0b000c60390030003401440740d51106424000d100301c2a40a075427004000b24080d54120700c207038045c442c030102240c480d902c5410b40c072000b001c4154002030062110800480c00b4111658000c11840381c00134030290203a40c9941d0316840c1080c0b212007926410250a0920b800880a1210a0014100c10070071042d02e000c0d980d61603141c5285004200d211003000e0309044650380340502c184500d036000c0608100141084c04d1040b4408080d01c4200e806100d04168000c100b100441d1041096034680c00440c125032049402c041182e464002e0b6008980c426034800b0b55040c01e20b03007501d001c80244140c0c83c10214070760b01c2401c14043d2290103040c003141c80300d03003c480c1c2c1000018644403813001b505c038880e00a5045e20701000001e903c55080141c1c1e02c00311076554a5414402545043c60b9103503011600c03148010b00d92200001d40c0c41100038165041404111b011808880700840c49520910070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 721316771 1250 721315521 721315537
    0x2030c06011e060e12030c0a0b071e0e0a0906090606030f0e150406020f03011205010e0c030601061d03030a2001020918040501091a01060e011103040b0c0708010908120c 74
    0x1078010310303c0c41d00c0416110042d104008039040540e44910450300e50b024405007031703505801800381805401e81d20b005c00000030010324200501c510078040d00c501d4501002e02400d003207503d05041111025400015002000c26440401080d040c036401003428140ca40107241110499202400344080c01070038442550382078a0800516406030f60000742d400e6901d00e005030018002d541c014905408200100380c02d0340300340c202c1c070010261549100104038091155000f604146005016003a402200103a02d42906105200400c5250720300160b42e03060615a001040340b004007140e640d400c049101a01900403040003000c20542d00300032190b00001802100c68110303000b0143c0c249142c102400011500c0301074801e4496640c1c2e4141c0c0d80004003040f01e610011000080302881c41e41c58035200804501c100040306040011308031030284024000400ea03000d5442544c0c9594039803076410451460031500358002181d0350b0816030140f0500150f0300040c00d0280c888054040c9070b50324001148190322031204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 721318021 1250 721316771 721316819
    0xe01090501090e06040b0a082a060c060612071e05090f01060f0c030e0414040b010b0a0c0206070f2a050a05100e03031b0c181e071e02030c0601 63
    0x7000135000d191035480358803810070080000960f0f42d12424001e1130280c802d250140100880e0003d6002c607242d100d84950012011148549025203055800da01d9202c080d00b000d02440b074030080211038000a01940c005840d0f400c020309000301c0946170380b01428410f4070805010b0034400c0c0110300c514000708074150580350300703480f220321a4007400004ca481d400b8008095041220590f000c0605950341d0040300c0b0007440c1c041000109040c50b045c8400b41070f0b0103a1001078009000c2040141581d08000fa441c0c4c0036070100c500a032540300c1e40c1010741c1000c0040c41d00800c5100c07040301e000400001064120404008049000042520342e424000c7d13000c81401410747c0082014540049035201e80b50007081c0303000c05010340b0708001680701c05d41e20300102c0703110701002a00080006041410040700c0304264591f40300c000d403064101034420b80d41d046a0080419280301c0420f0014070058084d0039100f00c003074503044456845c0302030071500a403613403c0810031502074080c0f40b00001e0390726100d6450400c2e400c0881c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 721319271 1250 721318021 721318049
    0x90c0518070f0e06071a040201110c150f0403020d03080f0112020603043306170604030503060d080c0a030809060709030201210605040905010501060f0302120f04030e0a060e0109050109 81
    0x8425201c4000603c003003580824104948030010b4905001212200c2000030b070103140341000d03c00903000e000c00400c000c4495004151410380f994443c0c0500c80e0b1181d8100c051642c61130007440000355842541c101940048a841e920000c160388004214451458002d101c1c40c0f81e40c860a1415600d02c806034080c1d4000c0060001c1004101c28000c00c691103032050000e0fa80e040c10202d003484403c05444003050740e69903645020403c0f1201244600042086000034051919181da006000c1380405401a801000c1a01d8800c00300700440c0202c82410b041c01c03044422904c00c5207070003807850408035101089401800d02003040c1c58001e9000d0010b681e0b050b12103180000c40082c0c0488513a580c06030b6040c0d0300342c5861000426445903c0b5201886000707100116030307981050006044488144070040030584108040200104c50302c40381b58000582c480c0e6100d207a140c1e420201c03610000301d11055800100307001d0000f41d06030000c541c1c000a0000783c0b518640981d544c001900d00d00350340e1090041b65820380e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 721320521 1250 721319271 721319297
    0x801090c14010e030a030909110906180d08030a061502030a020a02010e030118150b0105030c0a030f11030901050f010b07020f04051e281e050a0609090c051807 70
    0x9071038607510300c07901894005050043c80c80064036000d400344007900403c0e60302109020101c414021454610b0301411b441e4900018100410303000d10910800c4070904001e19003000700d0780d0720382861400f03040d0465000f0717449003400c890510050595100310f40d800a00d101403900c249001000b076a20000f4180c003d8400a1800d40055900e500b4038007035990705540e190715500c03170010944101050140562500c004400a07a0340d848100c604801609052000501c204103d8689000890f07040c910285000708001000b28400c4c4007030300110026a40c1c180c8007104004080605601182c49031602e60226905a66070741c5e0740078154810078070080d401644882e402e010034203041d0840d58000c41c0403a1a074481300322681607402400c506440304502903400c04a69001e225081c50b075131000c1d0085000400640490005000480358002c440300d090701c0c1c4900002e1003440b515444000104482d42d0244212600391800c2c40080015005180c0300d401e02042c000d82c03c0c1c1c443d01c07009124000c0754840c51800121 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 721321771 1250 721320521 721320539
    0x302031e0118060e070603050f0a2004031104060b0301140603151f0905150d0e100f0c17060f011215090632220c0503010f0801090c 58
    0x44840c842501e6407252184040007440b2040c510715907024440004845200131040d5040c1052a8091400c240c107280601510000078501c03603402c1200b0382c02c0040d0054400c82001042020060a8888020041000014044004100090b8040c100d40403c0360340d80b242c5000d5080c0c00b080c000e418040c100d87c42400140d050150080da0450b0382c4100d0f1082d0304140800292a00707017031855004c0070030442d410b0550b134107401c2030700a0080c12045854820f81d403d103000c0e5a030366000701c400071a142515026242c0392540144104198890307811428403004800b46036910240144806201c00107011248540d06001c00030ba40b01d0090000030303d4840062128001160702904011180250701d81e0341100700c0c00b4500030541c51f00202508080441d04500c0d15510509411031130030390641c1440b4031030b621541404d0301d8000410304e00088a03c01389011002e6030180c2e00700809042002e8452614403005040c4d50408069412600c0301c0f41c4038044aa192070340b00382030701c0c191040207015074001e540600003100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 721323021 1250 721321771 721321813
    0x4030b31020f03250906031205090f030a061d1b190909050c040515030606040e070b0c0318030a080f0901030b09070809121e090103020f0315100306030203 68
    0x10000b0700106451103280002030515940304506141da44070301100d1556105080d0900c4010a00740400b000784a246d40c94001c035000504603e9010400b001030f0200c000d0b520380903d0410101c0141c01c860441403c0d1600c0c00080031040d41a4103da000d1a00c0f009905200046c5045000c0c110f00103461039845007414070017110361012159800c400741501c08140040305100d03007500e5900400003004c1e04500c480c18041100c1011f0482011001030080860702c41c0c40000707044d600044143c600150000d0713403898080c2401101e8008812050f00040c4100302120004041c0011080d1044100317120324107401050340c0c414038211700a000c01818880000300000e07807005060519010b040104001c0d000d07200240c01520200c881d031011074850320501c454054108442000d2004c0a400d90b85000c0000600c0c00c8850304020080d07800c46000074001180364401d4050391400711640301d806440342404210303070060740900c03040280540d040000c10001d50307100c0c4c003e4400301c03600074002d05000d450124005400390 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 721324271 1250 721323021 721323023
    0xc030705090a06050306071d011b0209040201030b101d06040509040312230702010b06030c0405091305011401031109011a0a0311040b040504060503030405010e01050c0c0306010b04030b31 82
    0x543e6800d0005080e1424030565110300303208e9a03405135030080d1400c07801e0f00149100407141040303401c403d1034250f1540d03507000320881a0115040c000c0c9540d540b00480c0542410000745810510814501da1070b20340001c1c0d88075100c0d01320601c1100c4803104900780006230180744a6158010000400320740481c1c0120b40e03a14140802c8400450120b202c00c0252039428007066042180d4800e15013000032140d820b1144080142c01220240e2442c105101c44801ea405a070246500c00c3c075038400400e002d803035030301400ba415a501200038064454122644401c010003444240c0748d81c0c00d54445051203242020400d41660114070104404098407401751342d298110300307400800d050703903015190258044c0b04090320048c0705020003340e8550402080c48195210b070303448280079a000340410b0049a07000310603011014000c1c07808540300e080301c410784c61400030a01445600350003410b00100340d2035080001402981c1c084c241601880d150400180e1040c516000c0d5258180203801801d402140140300e09039007d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 721325521 1250 721324271 721324291
    0x20a031b0c06050406030f05040c051c02120303060a0801020c03031b0c120c0c0f03061f0b130302100507240f0609050a0b090c04050112020f0a02010c110c03070509 72
    0x40c404036550340300858078070b82081011400100b01080010303414090354000041d00207082c845e03403c0c540d8880941074298010350340b09040302e1103102c3c1c58044045410070615001408215460001c5010039101c2e4800d8504078043d0382c1d9039a01140c031143c14021034405e120040021465030355143d42e4003400286070001904c014a0811509040c00d00070002100c171080084202c40d46c0e0180700c154280391019843e00c1074003e000ca03400403a00782d5004141e42e9031000741420f12011348604a0720b031021060f8242c100e41d1002d41d02007403c045411780c42e005102660710980d6100251542142e0940e001c0c015140c000b4481301a544001c03016040040c82d04100307030310100300862000d8600d4180c4058544d2034104141065894080004041c8a40a400c81040003900e11200c0750070031603144115031046014503410f104484102902041c9542c0c11035400041c0581800d80320054075070024040e00d225103c420014940040302c1c2040c45012945400351301004008180c564507003000d120381c40000900740200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 721326771 1250 721325521 721325567
    0x6130308010302041e1a03210d05070c0507031401050c180f0f1806031905120304051e100f0c05040303082d0108060a05070804060e0c0406120501180201020a03 70
    0xb02a4a034006c1c4001c414641c034603001c4040032030b07003032610300850301ca1580c00305094004040f00d0450b4200c200c80c000000744101050301d98a45e40b080d5000c45030003000070914410074000205201503a4030040c0800c80260081c021038880352009806400f03006d0008468150000b140c401c54a4080502d0158403801390200002c0101b9000150009110800403803040d4150303001c1100c00c0c5410300554950f25206c90f9151080122610345542d1030400d80200003200100101107810b00800b004500310720300307071030141c062a44c2442c01010303111192205052922414418540d001210f42c1c015034040b900c89584290134549507440848181c40c01070042d5404412100401002d10100240740010050044041c0c1495141140c2c45181c041e004040000040ca0602800351a59100101c0b42c2c21607000070000c140600c0d000c00d40780c00c010749581c21980c02031030030500080d07400c0c000301054245030058000f00000d10b4121421055851401d8000740142c03c400c1e81240068003030b40e103014500c1c0840c006054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 721328021 1250 721326771 721326821
    0x106080f1902090d060e1b04020c0d201f0b0f030c040b0402160809010809010b031f020c0d09061115040f05070e0403050306120a020a03231606020613030801030204 72
    0x2254001c48100165401802c04103001c4910900c2180c6891012343d8218600700c2c4d071f049110780341c00c8000788410401c07005014201143e4210100055904400b0090b50603912001b80c4a01c0030441c1341020550240c2051600c1a40380343c00002c070034070000090060444119500b0030040200305820507c1d41c026804e21142c40a00020110690300c03d115031205607442c180b1000151080c03000425040050b070400402ca2090b4802203003281c6100c41c0c000b245901103040041140280c0100c180441c0584641d07098040360381d174021007110840b650341d22007045409680c4290b603110300103c00101c00f003040190128002072104000c1c3c2c640203009100b0744644503210610b403135940f101540d0940000b1004000c0c1710691401c03041c1a850184128018074890507183d005c03d01e190150710018014503240c03842c044c0f00400e80190313000d04a200c0b000351400462a9411602510220b01806006100d001d0010360304003901c5120202c0d240d010340342d14016a185500304405030003500c44480e43c446101040d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 721329271 1250 721328021 721328033
    0x330f04170106032607030e0d080c0106051311030c09010c0206040e040b06120a3c14061b0c07051e03060f070c030c020f180106080f1902090d 62
    0x85520050900100d2010303c1e50400c3d12140710034400c041d040a209415491804103400110380c07100764076003003910000d18440d00044424060150151003a03400285006c010b48040d440801a1082150520240400780c00fa503012551607403003681499200300045082c0034291000f07827034040d9051420f0014140d8680c0403401030f40041d4031800f0501155000d0004100001c41c41d01d41c420000d5880300700c0d880c18500041e0380c498501ca00038014490111a00e4080540300f054242c03c0010034001e003402c08140381c011481c0d43c40c045000e80e45114408a1001203c0300840c445014042220b01d40c01000189040104668004c1101000310f2081040020310364844083d00c0b90048070302c290810322001600141400e28100030111100031540c44100a21070f40c0004400581a8151805000f103e2180c4003103924204183c030132560006208000314612100b20103441d041e00c656a130341c0c601540b50008020203002c01600c100c05441c0c00e491900c100c10740c5550140c444540c00074405c0421541ca43c0302c2c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 721330521 1250 721329271 721329299
    0x1080c040f080f070819030c030e0a080f0c060403030f050d06081207060c0906080703180203070b0c0f0705060a0302030411191e050f10050705010509070302330f04 72
    0x480d0240c00a03d0400d080d10010b016000040080c003010708076000d48400c1c007450900e4061b90040c14000403005403000d15100b0030020701040c2002c0c0014180075210400c0300c1e40c4c3d60881d01380344407500c034130145814a41040710698044941c1a250720740391010400d82503500d900a80340b5810510b43d40c200c0054046003c005003111841e00401c10760307451083d0b05009040d41e8803402150309102d8000410801c85034131150003a8454032915000031080015045e9120300000d405000e0b600d486031031000b0945200010040010355030141c103c40c0019a900c2d40f00d45c94031510321515601c65001d11541007464001d400540e401407160380036007a4940d00b0000503800c0c085000c42d507280b0b07101031078051240b16522108490004008003403c00224034000015629042c0148414080d51101c10a014054003550545000307640c0f081c02404103240c2180555a030394803030310050f4032446807610410340c0c880020038541c61052a00c2d00314a6490901980310f482c40e0701800c40c201426800300000a0074855880d44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 721331771 1250 721330521 721330529
    0x1d06100303080a02072004061e0906050a030506060d0c0302180105090108010e1c020a120e04050726150607030305192d0605130c02071a0901080c040f 66
    0x50841618214100144102d400429211410f4810080d007000301d640442e82d031420002880c0d02048000440003c500505956030019020b0881e840c162070100c03420010950945090304402c1040507038403410040395100c03a21024180d50401000305046052000044070640d004509a80314181d0300e5000c0340441e81d181200c3c000702400500103222030316003015118014030f42c24000b40007104074100c58a4480f6110b6503000c2003503824a030f540741c41078000e000c1d404145801c1042c00c8010050b00ea4094401c200c0d1140540c0309600d00710010b0f600500624ac44c2c004010701c14040b84054042e0000a080b201d8040c00c1c000d08060075440e1000c003592031400400703445101c0d45d0b01007000d040c05440b10210f40c00103009803005d80d04080010410111103211002e20500c003000d030b11070255410b2074040040000c3d0708038640200500c0f110640d07540e610b401804c0452520383c2103603d45662156035508a90040160b05810f040800c00035003158411078051303802001e9040036610b0f20b40d803900c60103125040d5901c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 721333021 1250 721331771 721331791
    0x204050604380702121c050d110c1015120212010615120608060601050a260a0b190b0328020a020f120c06013b061e0906041d06 56
    0x3c0301c20850038130b101c1c00b005a04d103407001461030900001e1441c2413000b09290f00010010041102621451140c00058941c0103100d080d075542c4446131500d035214aa008061140542400c01c000d0040c0c000c90300300e03400c4034030400724000502c80729030030808090291001031040b07649a0002191200a01c0004106016561250340034044007039900020342c2d0b210340c013185040d0000380030031030f0990b0404112070160000c1d14010505a030035580150b070400244038200e4448011408020b40d03a4042da0000f42c0c100400c842c01d5140e11141c0b520880c83c0040d5000707030724246e00c00307101040380c040c0c1c1d0324aa613211181c28402c0e400342848140e41081280c001000c040d0050f40700c0c0c03103002e2140d030f820f000704444100400700f03280c40c01c00f00c95803880c1d4400040c481d115142c6c0c1c1d0f40d610780045001215039182008803c541160003042d410a00c11113402055844620410f00c01907450641706562050309540c0c6006007400e0000e903200c81c10000282b0700a91050314030b04490409148011090040c50701c1544829 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 721334271 1250 721333021 721333027
    0xf0901050d0f0b1c0c09020307020f01050403180b0306010e10020f03030a020310080a080a0513080d09140607050c1e180a0c110a0b04080417150703020405060438 71
    0x4040090a10100c0d076800d01c0e90341c0d16100c04001c02d0a807902c600c2946c16569000d03030742e40c40b2040200c1ca0440428101c00c0c1a5213843c0a22042641c000c004a407c0c2e10343c100d8030207a0a0704ea400c2c4400512054814901140417041b41113401d00300740c10ba50f107601925005894514144450301c3d070540d407045072265002603000040200840e03a40540c80050201c40c0b0091408200980d03407000c00744110124142440008941c401540101480d40c9001e414002c0135640010b040e0080036203920054002c1a4440704c4003e080032880c240340b81907940d1980c1040c02008546c121a041c04440c0240e10600428030f203000d104004541c41d11244141842004000f40c8902c1c07401d800700c441124400c41140c000c0040380340000205c8080060035070a40ca80050041c0801d0310f441ca0301e0f007002d00c40c65001212070101003075001c0076024003007000c144d029051a010000765032503100850882c8030b103003d0710b0707030021003404140f00b89040103c001c04010241c100901100c1403001c0f042142082c080140300b0854400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 721335521 1250 721334271 721334291
    0x150f1f09060e010512060906040b13060e01020909070e0f01050c0c0303031602070e06130c0207150306030605010f080a03301a041b1d060403030320030c0f0901050d0f 73
    0x5c4445c42401d1310841c02421040c2030082d1983d4035120040d00c050050301c07925000c14900c0b200d1041901449500460801980c9003280d1704c24080c0d0002c0740e6451003100c00c2000a80d00900985226001800003011200061032100055409402000c005070591040a510041645040005600900800c90103c0c1035140000d00289000c42607013100580f011082d062020387d44441c0c072510010000340d02c01040c030a0456404074584540c56025030103912680e6400002d0035096070010040e07d010303940501a40c1e0f03d80d4222801200305102c0c800a55000e407000340040380c4902e0700c9004960080490b02440350f07080b180c0c09401c0721000300d0f041440c2c0c0d072011045407414081ea0014a0500c00b030340c060110701448001170303040220101d483d009024041c07002201c101d2034801c03801581d41c00144207a456030340b6402e0081c001c1c01519001a010568050700304038225070300c015640329031480050340b803802c032070b2080728440e03500f0100600707061150074404a00c0300e080c98090128400364109001a0038109 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 721336771 1250 721335521 721335529
    0x5100509060610030c0c021003090b0106081008120a080912040807180513020108060a182f0306010f170a150617060405070c0b04060501050102150f1f09060e0105 71
    0x6940c3d9009052810030042c00e5103030481e007030448464040301c0c81303500c20b0a800000e402500c12000e004103400c241c0380002c2002c0c1c0e007007103000d401041100c0140640646402d6a1680c0d031601c0c2c80c1040d10f0000038007206464510845040780e1016581044c3c414003023802c4c0c0328403541c2c0c200d07070072442658010b00c6040c0100b0f42920700c0003d61000009040c00f803400d1642c0003810114482c00c01078108220310000032950b41f10f044490000700700c0c0301110a00c072800b9801c0e040041c40146103240c483d034007140b44006030745001a80b18401c4003180a080d4a0f580752400150399018400400c0030900030084402d2040e0004664014403030b02c005400495080e0aa12800d00f01d440385801c82c40a0045401e01c10004e01803021102c0d5100c0ba003600c0018094641e808290748529000400604000c1840200400c00016030000e40c102d500a80881d0362410000e400080c1e800c9007220881c501c5801070000a18401503100941121008403048200f04c42d10358907200240c8040303030499007401c1d00c0c8400400040c18 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 721338021 1250 721336771 721336789
    0x6040e0d02150a05190507020c10090812040302060409152114030a0207060e04200a120605060d020d090c150206010812030f0705040806070309021801061b051005090606 74
    0xc00f0000c10800e40c500a04409680c42d540c0740b904032280d54510025801c98000c01c20010400c00050000240040540c030042040c1e8240c01004058000c01503003800c9032440340d0a94050703943c002c22840c2828100168040108144031540e0409254034100280c8235820a92041900d90f000c60790802d050b0341400d01600c403c01c103a03c214056401042144c0402c0e9010400c44255482c0c1d186c071408030b400000000c1d0140c49903003003044e03030100e02c1e00c81d44290020510051540100d140c0340c03032241c0314404960a0840d5132920610f500000e007000003880d080d50f02d40c002c245225103180002030071203507030701d41038110089604420866030301c0302149018140c0401c02c4500401001c03005040312209152500c00602015150014408001000c50342c0035000300182c1c1e01816903041290200d10300b100d4000d014106e0307400c3c00d07030081c5c81c190340a03180c1040258074281a2071580e12040c040d0782003000f40062404801c103007a2103a000d0292401c00d8aa2107015160085201b400100b0303071410100201300f0900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 721339271 1250 721338021 721338031
    0x9020c1501180e01090b130b0f01050618011b2f0f010c052401090c36050310060e070207030b0103170c01051906090c080a020306040e0d0215 62
    0x1000e1400402c0101c080005020b4280490070022a500b01d0000307407030f40513100f4028014041c0f0011030400c01c0904000300182c105034080c041c4040507444c2c907458881c14410038001d42e90841810418111500100120300003981818508611003490f1205200041e1440b150120344001c801d10305200ea0008060420700c41303484d111902d8000140060000760880d0b110100c1d1418004112800002d010060220200c078480540880303500400d68441003044540901a103500f461500c84505800c510907242d80514046908405003280c890865001040c50000c074424042c0942140109072601c040c000340085070504a07001c0b642d00d050846652105c0c8004110030115404401d0810204110751000c41c1100e42260102001c60050356066200303104107400f0500c00e40c248400d2100c82aa0558011415072190380200440c80c2c5440314501510440c008060000304410081051707413034258025504818000d1000500e0585c117a03c1794140940c288400000d07800406510300f20041e1010015400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 721340521 1250 721339271 721339303
    0x160614090d0504090b0d080d0501080d0e01021506060c010c0908240a02031b040806100e151306030b0408042306071e051c031d071512020409020c 64
    0x410320760803000780a40030301c1c0300d03c526080e101d03801807400d42ca484c2d8500003038a404c03440301540d40c0070100b902d002030f18080c40340300e2292055a001c141220710070103062010610507400703030003c01c080c00d09a2240c100040c14403075018004006c4490741d81404d00c01c00c4508415510b0326103160340742c1240b9070f0514004500600d181000f805a481c00c2040710140107900c0b02e2403680041c0c498544010000b02c1080701110240d504038000350120b004100011000c2c416044000b1465100751106015403c1e01800e580e51403002095256460b203506d00300015815020f548200010301541c0c0e80c8580e146018291415a00c816001400380082c022054040f1566840c0300a42e4141440380804140c03640f051540217040700900d8640c00503441046c803004180745030031404882101328103082e0f1085841c0038030b040b0400b0a103007001c030440049501d50050880201440500042468030445410448443c0010800c01031a4080b0302200546840500050454a1070040c2c0313681008036007030324102d0b800c42255a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 721341771 1250 721340521 721340533
    0x1311040204050a211e0203210d1e0906140a0606090303031109030607020705030c0d050604020d0203160e0703141513020409110901020610060206010e0c16061409 71
    0x40340c850760941000ca4a480401085400d14940c0003124503801c12130040500149440681106288080b0710003110b000700c040e00c500c10344480c0c0900c0000c0c0c401500c240c02410a0201c00351000e1181e1001d0109000800d002003001100b004840403134908500895619580307014545811802165055110b0898201048000d040440141c1204582d1000904050316a000e050802d00c040c029615001d20280484096061809010791150503d002c2c290083c464080591494946803034140304042c0c000d0013602c460b403180d030240310a6406944080e6014800d401d450310300c3d400c0c4503480300010030302c242c202035481c10801e400509840360401552a00c2801c40c2c1440315030094602c4003007102034112040380c1081044010358029005551004441c1440c20203884441076400c0020004070400764241c8945580e51440e402d01c4051a002d81c0005900c4900140030050000ca03400e5004040d240c00c0b541414010300a100d801d9402e80d00480700d50b900d403080240f1800c1c9980b5641e40110741d20002d484 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 721343021 1250 721341771 721341779
    0x30c05040e3103020d0e0f0901150216241d01120b030a050105010923180a1e0308150f0f060d05070804150b0d11010e091311040204 58
    0x4020718080d04002420200c1c0079914078200314901c41c44003040d59a081941c0c45062410040e4a81428081000100312024900709140c9098503c003440000e00402c1121141d00f400340741c840e1314000c0350600003988550305036820800c10064441000300260041507030b24402044590002c60010502c1405000180440301c0806c41d0021120300030450170304e00720b41301c40d40000103d00603000315143c454250103510317540b06c2803000640240d410384d0003143c000d00030040403050410718042c08048019045181ca000305201c509081c001300c0b07980309044125000361003680c68a80410030a0003080382000c0c2141c503201c0426030072848807640036503070b448400a000c00c5c64005c035940c11042000b4500c980b43c880e80c04041303a038540c030a85021440070b000c108903510b84001301800c0b90506540640d8240a084a80c100c080010f00407000c00c0c0c64007400d84131105000390b0b5202210001c401085040c1320103d01c8200b61034440002c0d00e40f00e2001201c413001e8010140c2010a0340d5074070b501c1c1d031500503801040184 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 721344271 1250 721343021 721343039
    0x403050a05190c030605071206080304170f0d12020904020415020c1f0e030a05120325021f0f0507120b1206010e0405160305100507050a1707030603170a030c0504 71
    0x40c01c8a805c028042510f0352481d00440755850881d01d29101540b0f031020101c0c0d02c0710000090006e98128140090740030206512881e6944010021070300140c2c4414050003070b85100e03501c0300f00342880358800581000410341c000b5060741c0050b0800315000000350f00e583e0009a041000c0350703400780140c8010704070f40c01100b00c45494458035400c01086c8a0442c10325225510304010b44142c26401c0419549109604e45800500340d2090b5044900f005084010541803071000c5190301001445400802c0e0404440382d4940b03c682400441403215661540c04141200880c01681e105d81c4941d40d681da0100900c4588030102d8407070610050261a004a0f5001c07000c0d00094860b05588807070482d28216035940c03900911b42a02c0c0b2641b210b02500d072000000400400040e0305481951441d814006070750780b60401c848a000780142c00c40003c0d80104c102d04054000c0f61081e0704503541c0e180100c3c4007600c0c0d8071180c080f020b8075400250076440c00514905642d0b032520444498141c140303006c030300e0940350000032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 721345521 1250 721344271 721344293
    0x60c02030a1e0b040f030809030a0504090c20060f130b010515091e130507021f11220e0708040308060f0a0b12093702060403050a0519 59
    0x203150300d412a403070070a610982966038071050f9000c41100c243e803505150192400c0000881240454896008230b1a01c10020041d0b030441d2119030b4650341070a1510b86003002a000312490002401320140504213170001300344540380d0b0602f04100400080c10a015240180c102c0106007141300070b412069040061021021181107800890301e55480310300d400252041031248040c000e038424066003c6522070303803401e80e024840f0034007111a0b04c0d082d1190007000c02900c3c8116114401a0444000707000c495401800400c0100071000000070946200310001c01c0c5688481560419035112100c01c0c242503460280e404c001e441803204011003828650009800c510001d0801400d01482000140058031103190542c40d0010013840d518955555400f10180c0c1c0d404000009041407000c0d000914084001500312200e06c00f0000c6403c002040075100c3d858080d5818031041c90071481d42c4610007591312800a08041c5010b6405041014564030b0800d280c42c15560000c0c0b10944000c00e0f000c085401c03610f00d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 721346771 1250 721345521 721345523
    0x10509060a021819080102040e0a0c1d10120509030d1b2a0503031305100b032a13021b0105070804060b040e0f03030141030f011b09060c02030a 63
    0x4004d9036440d5121070f1400c01c8041d0300a910780c1d62011800203031a0004848070f9018400f1104100600b21000900b22142250103803189800101c00c8140f04a50034203800b0700b80c4a110f14507104442440207044c00058171400e07900024650720100d5034088801a91080c0e0814045001000c2101031030108098843c410604a602944000e01d10a040d80e601140c0c1c510390301644001604d54a01d080303110791103115003103082500d542c0300c0d130790185801c10154452003090b01c00090051001c0544e207929400281c40c0b840300c0407d20b4002c440b040010340c898201101030300480d41400358803101c1c0c43d208000304036220a1100d0f000d13810041030184407034016026a4000f904850046200c0c0d4148002c50003402c0c11500ca590b0602c6021703e600b00414000c03019505035426007420018006002d000c600c15056000e40507188034007045220340c0168484005240e4260b000b13019155181c030240c1e100303030856901b050f003045540041c0c0c1954013601d5001c110a40580501c1c2800e2840c00c03400e401080e51801c00600c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 721348021 1250 721346771 721346779
    0x9070f0806100b071509030f090b0c1b0a120c050114040b0a0c08162006071a090118050706021612030305061c1a06040203070c0b04080f0309010509060a0218 69
    0x880750141301e038925011743d0314200e0380010300c4100503610300148002c0490340100002001c0f070001085c65854401260200611340c0000c4c02910703124000c180701084504101135100820700800101001d50f184c0c203044080c09000030102003441d0bd400034014150800f29051880c0003000140003980082c0b00365442c103030711413504207141403061400c1c02c160f00c2441360f01c2c003409540b00851701c2040107441c00307900340030700e401c40c0e801d90010390a06120950207000300c001c0c0711114013107116142c4d040800f52990700c0b001043c008140c003c508500c04c800c411f101e001c259400d800c015420b1080035010015600c45070101c5148690315458550089508485000001c04154413000030603001d0362010144c400f8500c0000d0541205202e40c58600091100c0da90a21111443c200002d411480c2900c00d82c0e124190a0310303440282800c80d42c0342410f89100820071035000d042400b401c41000440409980318540ca00f000042901f8070300140391030841c004120030651401005000c81201d0178480032084c1d200700390703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 721349271 1250 721348021 721348027
    0x2120103120c08030f0601090e0108030703080901020d0204150921120311210915010302060f040b0318010b0a030c0612180b0f1509040210020a060509070f0806100b 72
    0x100116607042c48403401070b0070f0502c003000340b00841803030000c000d01039042625907a41060f83c440c00d02031a00024880c2000d035800500009010a00030840c10798005007041c001490b110520010900300c2c1c1147c1c1000d46c2d41d0441080c0c0c10321245d00052048041c1402500720034015444c0e8506480e00e04991100420401007040f80f00310043c0280c1080c100090900c4103241c40700070301c07044840c0311290301300191250900038000c100102c4010072201446442034082400580c00c0d0780a110a07035001d11000c0c45884001c21001414182d442c000d14080c8a02807400590880508041821744840700015445064584d40c10000038142c81c0d002401c40b4420304240d1441102c0484050050000c0014600501c2910a41c0c070200300c540ca60307851286550f02c1031021070b0f4441542450765040b10444454002c07180d40b0100e0098505070b02c10600400c45803044444078042c90341e030340050340d905607401c00550b8060502408101108140c00d406018028010072040c41e044102c05103880c654464026240340c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 721350521 1250 721349271 721349303
    0xa0e10090906330b030108030304123b01170f1509040501020a090e0c0f03040c091d06010527040218150f120d2f03030f06010302120103 60
    0x20380090b83c01c080c540c4488103120402c0c0d1052940000d00b0721154454000300e08010401c1421881075a040c0d44404000714107617600c1c0c1d0398880b000351442d0b011509004c240c51481001c0503048590200540640300b881c00d010581e00c181414040161003410f052001c0f00b4010072000341c01c03d100d154443da140e1a40d0503151150440c1d1310442d09200a40d5401c2080102000140101500242140c802c40d0f41c49070319041e40d403204030242e52000c0d00c41c1003d8007c10007580681d090040c010f180c1090107800c1d1030345540d503250354000468250b4148411027021041c4040c60709241407040c540108400c1d02c80c401034002e48031b00c441c205c45000c0f00901803903a0580102d815511a0404070240181c4070600140700d080c001c0f03076505502415007209214500d82e044502090a250158122400b90003000f0603000d03e26803010344100303195440c030035420b0a100e021844442d01424000003a140120040d56903401d04801030100510002d11090605004210b1600e2101d00700164a04581d00540020080444 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 721351771 1250 721350521 721350533
    0x6020c0a0e040609140d26010506031305030d0606110c0a14061c090c15020c01200c06040b0c070f080d05030c0c0703060507110714010e0a0e04030203090a0e100909 72
    0x60b01e10321455a102c0c52400f0000c03d900000c2e000d51004041c52010107030a14100d1f44411000240292a0464000d0000c940c111069284a00b000c0348503a082d24144151044003204940c0c040d401103002400004100c03000b10018080d101d070020040e9a014819410400e0480c014a40d2015481c003034180080c15298500c2018450b442c1130a01e041e083c030914010741000f0080e0f101034000d07140300d4500c140391100c401e070002440b1455040181c4410103501c50706007a044140000c04012201c50180300030240c03295446200a1014150450b0a10746a03200f40159902d403480d0798018811680d103403501131005840014100c01c2031006c61411035901d80d21100c1c0d136182801000c0b0240e006118002001c01004199000103104d00c03150755884020841d04000e03960b645403180706032140750700c01c0700c8003105c41c8d4410348514580900251840e9600c1c1d9561040b01e0020b0320072107080d001a0030114024102d41b0708003035a031008001c001520029420140d400380c020300100d03c00c0014107561042c4000c10010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 721353021 1250 721351771 721351793
    0x421f080303010b070f0b250207060e01030e15040606090b0d05071502030f030a0204090b040b10030e0a0c0e060405070c0506010b030414010207031d06070f1b0b0d0606020c0a0e040609 80
    0x35100c0d128400e9418034500b81542040040e04503a48030300041f04030318141c0c1c40010510111180780e40d41c0604900f40c4001500140500b094074040c6001d01400d012000c20a5030b90750303016510900300001d11501e0507030040200c44178160f00340d10902c040072030384003c181d0009103001520b08546130000d4558035030909a18502c100c45100407015408020030254401c1079000d0401c0b41d0500c5400e120454210040008907100000c0041c2c0c065560856801d402d4801e5100c062044145e03c100d40b001d111645800c030006d40c03135910103142e00d00410100403142c280341c05000d4211515040140d89404a0340d6100d031290030502500400304004800581405440c0c580d400c00208a04003c46d0748400d1414018050a1000d00d1400410b48100c601d24007414100110341900340c02c42074460a410309d0356660f2500b201380c0140301042419880000c1040d0503080010040000610b04c000f410320314220001e0305040c8103c603100d105800143c41000640704e04402c140e03216038005000142050245440e0100300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 721354271 1250 721353021 721353023
    0x1c031e0306081905060105010c1e081e030912090105031906091a03060f19090204020c0106060c050c030604110d052b0e0301050405421f080303010b070f 67
    0xc8580140e500005000c0c400741003c40c0e0103003050351160f03030b265030066a0220021000809107840c03a80f04e40003040e400b500201403a031040a000749400c000c021544e1045e128080030072401ca00000c28844000700401036142c5410300d400096040001040000c0c085000040c10081d9840d003009800441c2e100c5a40140050001d1040801c071070071001c02c074840d9046511030038600074402c01020a40c1c01101c629100c4c03069901c5e00410270016242104080034040801d000c03600550280000e40c1c14000a02940018207555035500c0c0207280c807030074113500d400c02d030050306806604041d0501000c642d00e51040e50380751a00340d945400f101044e181691800b0182c580400c4d003406884e0b5288a484200d02c550030450081d5501c9503145003040c0205402c0b41e40aa034000c0c419402603004017038000b411114120b040450700403400f112882c1904864541585c2201102038074400d0042045944c0c00d0030010291000e210300c2c107503403142444080d560b80c3c0700601510400050214011b01042a16801c0d0b0b4549 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 721355521 1250 721354271 721354273
    0xd03110f06070906030c0c0215071e1115030601080708040f0c060315090e3301030302030a120506101112130302040606140327030c0c1c031e030608 65
    0x24508400010301ca0100e0780502c0700046e08001c0c11007400342c480c03800b440686800138030710f8114140180401c681540000707030032202c4503035000f0102c17280c0e070100075030440890186e10011640840001008201000515143c4c081c660500078031825981c400c10166100e080f9081070310107500c071410049840d400580004158078850342010841c00c1d8540c0024580d6200e5001c1c1c032043d0758075420f45800350b880000300443c40e9481044050003059440d003d103080b000301104100c06d20042c0080c04900840c0c02d800035000740c0d000003000349650354404004103408005403003c10180c100301c0005049000860740c540304020048503002d6240c003050000345004400600e020360b40e550880c204110f14540b612040e03101324078015000640c24020040f0020404c1002819880e5590b2949901d407038001440c1c103000c014400000250304000e04000504010320020010038914680c08200501031541c040c80c285180389540c0c0034000290400760b81403e00448c550361204042030b001d01100280b5075544035902d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 721356771 1250 721355521 721355533
    0x171b041509020d060501080601020a0b15010905150309070501030e15060111031b160f0e09030906030112110312040e040206120f0405070b090a0303050913050c04051804020d03110f 79
    0x550442e43c0d010384100d170b03c00c0c0ca840c195a694040103907282c1c6050b01c030151404c100840080d201d02c0c1c48112941c0804014101024010f4590010038408082007800110f410000414132a00020800c00600104400d107001e201e1104007898058981c1140081203c5510021010800c00e80c061070b11031809180002c1201e88a00c01841d07044004051b20485007035074010030304050780900824a4500940300da12a070110124540309240c42c1d5160000c0040c0d01a00052140d507030b203a545c001c000c0d4002c001c0d031100700c02411100e06200c2903000401c05d141d84a03911072880031003681f000781700f55000c40e60300300741d038820641d210b00104090340305c1d204c8074031050b400369010003121141d9224080d016a00400850f20341980310040011140b0500c56a107030721a0200c00d00300001303445440240a0000064500704d041c0a0071180c82e41601e00030342d4543c4001030089820702c090305003518803800d003e484480085503800c0036008900569020350014082181032050115024410011071901580700302c21501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 721358021 1250 721356771 721356787
    0x17071e0f050402031017030a260711030405060d0209030c0d020f04090f020a061e020d09050f13050108030901030f20030414060c03060a0e09120a2304171b04150902 72
    0x520795000c142c0810201c0d0b07078801b0802d0440c040c09c915558075070000c0510112519000c00988840481d81e00384040c91204000c08620740e29040d001d061609041034001d40c5480545080500307012a50004a000d42103003891040507a40ea40c2203070246002c2030b100002d00c80410b003043c00c40103003603001c06904000722030300c0002c070030360320400840c43e00c2d10199140182c040c1003a01244c4603c1002140701c0040c1c44e001050250b0724101c7c402d00500600101041101c005080c1070708140c075001d0340440382e9038101044c1306115503014004d0300c0c41d080b40240104020500602212038117160000b090310000e41c080005001c01c81c240d190040c1c0000c8a408490700c524001c818001c490f07000b124054000c0c40a510700042201240700d03101d01a0b894a405010f0012300042d400382c0c6a0081f003100000c002c410520301940c030f81da10441d5415100c2074030302c41e951281801c0320103443c1c1c00d000c02c0140441e8041032030720000c4180840081c4410030222001303e01c181d00c0c00e40c0c00c1d001060541001c02b04906c00900e0117 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 721359271 1250 721358021 721358023
    0xe0402031f0e031305181302010e040212040b07180e0123060c0703030306090c080a0b040204150503100602030c1c2c1806060f03060a17071e0f050402031017 69
    0x2c4440480c1c00c2c1d07200900406c00d13004685010b030b4582c44c9121100c50802c00641c0035820380c03c21110b0242006080100300789020300c128005031420780305502c5200c203000129038442d42d05180710000c078428121044ca49003080c0070000c41441810180e00c2c8ea100c030f03911581c407074181c0207030f400e14001c1c12540c0740c0041003c3d154503044248401c80100f841e2010000703001c800340c0074084418038244c40721103440e959107024901405010512680c842c0e4200404100c0c0c4003054501100344040d951760342d07201c1c9808840750600042541054003958001d02600e004104000350300a4405480b003400603400c01d00d8030080d5141c102c4080e0460f000c01c00c45e454070f049030902c402e9410302c601e002c9481c0941e5406a1901e148007078020340d030040d00184104004011810b8990041d40c01c144c0260082c1c0f401c0d030b911a04100c1d0b4015203014558103030072080701001840f0b0213110f144920444080300028691405145041c21207151048030b0040750044000743c007400000240000030700304200c08840c0028012803007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 721360521 1250 721359271 721359307
    0x5041a04090e15010609030809010818011a01030506060c072c160f0c050c040b030f06070201020c07351c26130605040c031a010501090e0402031f0e03 66
    0x80080f4031140000190340c5100c0c0811004481e0040350b0a803410080c2001112038410041444504c1441003400c01096182407040c3c0451035085c81c9180011200c8400050580e403020f40740f284200c0042c086003c80700c0703001c15a002101d80307a442445040085003d060441c440c440c114840d03100400007000107a80d904005078076000141c0d1744185144048900c01d41d010104040b01070a20b9122a03034020721400c0035841040c280d60014100da12000c404d04100e807501d0300842d2721400603500490304d01d000303c00800c600d20144c41a0741c034403405074219042c605903080031922411000e1034540003082000070148000c2c0c4040c08907200b480b46060b00104081d01d00500307844d100309a403014140b00c2204d04104103903140200080e80a0b010b800d4034a44492000c0c01c00070b407064404043d28400000040d06141c155641c241c5c0444c0203d803650b1500e00054165196903011000d880401004c01c0016a8080382c2c0d120021850b4003214491000f074100f410040c20407448139020751000080d4061101d41031124 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 721361771 1250 721360521 721360543
    0x60724050f0c0a120e070f0914090601030807020f010c06090b01151803060e1501030303060f0e01081c0e0612040c05030a1a0403210b0406090c05041a04090e 69
    0x1d000c0032601e0b421000245031003540d051000054202c451301d52412001e07002041c01c26401011120800e440700041c01300110241c0c8180034031130759603840241c1d60348a070800301d6200c5912400b0b410355601d1a03c40e1982449810fa000340f05148000f42864681c5c001da2140c124585c00c108100708462082c9403040380d0780d4080c014410038035045c9400518842c400c841300b0115580c020880c1d4099440c6035641409840d00700242c0c40c1034000c0e00303a004401c1000c401c90314000c500940e004a13189150005404140182d03800ca0500542101d006020702c0c0c0d40004c00618190740181c481400e110040000c0b00d0f918501048240d0090000403800c40314512881d03000d02890007064030011441c1d0b40c00415030340740c0c85018000c0c608200704141701914409018004d1303000d030003402c0c00416541ca402d4a01c0803240704240c1401900c1e51213080c000035050511540d030240c0b40703008080008800c0c60074003410900451080da14100c810180403081011204140c500a0090702d100f48911803070700c0e24a075110109000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 721363021 1250 721361771 721361791
    0xe090411011b0b0615211003320a120509030f07060c0618030206071d040507030221040213090f0503070c0e07180611030c0d020d030c080402090606072405 68
    0x65a43c2005d540112041001e100c2442c0900103102864090043c40083c010708408401c0e030400401306541c0351240f001502c00c014000344895099454902d040c0e070b4810f14904c6603100004a100148502903241221806402c2890320303114420000303440c140414101a48500075400300082d841d400ca00034003105e82c03280500340140b2460400c4000701112140001e401640b00e01c0100385124000c4c400840d90844d4001280701000e0084040ba0540d81c00740d4800000950000d804c0c20820341380104210300c0c0c0d03640325400c0b8643c01c00d0740005d0000036901080d1a1140e80d5440c9040c200000341050620380b50784401625190022414074800161091140400d040d02c00c000089030b0354450300400ca100091800b0880160b410300808990000550316183d5a0348400c025880003c0410410081a030b0700c140e000f02840106040000c0c10344140440d5a01406511024480141da0b1390702400e52042d4280c0d20f0980300e500c2400d04080a20700701000e104010000000c1220224850304181d21a8150350 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 721364271 1250 721363021 721363039
    0x60f0509090c073c0506011505070c0303050d06080f060403050d14010b03010302040c050c0a03030c030621030207091a190317131a0313050304180218010e090411011b0b06 75
    0x4d4500055112400b004040d03820020060140400c0165450f003039102920f009410852940d8410703017210000e800a401040011034090044242409082c02811510700034100c4007600c04003840d92668003070b1000b41440004a202c08000c61035500103410303401c0c029260789042d40d45443c00d140a40c802c0c002039000701d08080c01c00b003255008400322100700d1500d500030306021314070b03032070481c01860902282000c168a41c4800130f8640300010080c0000d00500980001a901900d0041d152000039444000003500f8908810f881c8000c26140e40380300030082d10140c64110901194616244180e0001040020462980c0160300701c0c1002410032841194001d0b40c41c3d94558501f1517080f0000440c03110640c50070000a03641c842101d0710702920714421421642010340f2682014512080c150301400700365404600e00054403c440026109880b0038202052142482c1000c0303501040000d1000e8808000907200f00c51607441580008083d04680c01010340c0c07484540b600f1a12503000743e601a100300911 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 721365521 1250 721364271 721364363
    0x61909020409150302032a0904061b020106060c08030912040b1801090b3a0e0105010e070c120e0d06020405100314070f0e0405010e060a060f0509090c07 67
    0x4003c0101601e40040040806030310080102c0c00103425803d103681c500d410102c0301101900da01c428070340100d00c5050003041e40720601d554101c41c4107000016500b160b0400f0020426190480c0300482d01c42e41001040740c1c1c0b50f41d200502c074584003081c950340c00c10b9000018000f49550301103000d0101e03e0321100d1280b410001200044400e20014083c91800d41e404025215940601900764603c0901090f0665481781411914100b8000800365004407a42c403001d0003006c51b0020b103d21030140c50380c1210f800e414140305800400c0050302d004010309050948500c00480c9000c7c0481c03ca000400600c0d0715120700c6640381100194116105a0b4080c4184071200203829000b400b45035051384201c0e404849903620010201c2e004414807000f1014042288a9101c10b9102d6026083c00f8116140644c9503e04041c0188446c55029600070f000300080c405009104540c86012034400c004211b4105c080b40d00c403005401031901c20f41d07400070420964061640d10043d00d0109450010412004115800c000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 721366771 1250 721365521 721365551
    0xc010207090219260106120b0301020708030a1d0703031707111b061c02070c06050703081b120720011a2b08030910061409061909020409 60
    0xc0c04402e9403814203031120180745a22035080000403844441130b040044415039128036400b01e0a030070510000d000b5005551208142c0c0c050940400401e400841c5400d020341c854440328080030b0580150903440d00b040342c00c058590003800f0401c80c90b14041d03c0000c1d58038540508161142c850943c03072003909000041d90b150090b81040c01c945500006010780800c20362441c641c903060041c6c61580000103000100c941e480040342d92050505d41c080043c5d03540c0b580e040c00c40d1409000d500103002c00c0360401c584000650f108040c0f90304041c0b05c4201003000d90030480702e1710150050110040304103209070100583c050b8081c6103a0311194201041c00e030007003620f40d5034900786c61105100b850441c045010354403050501d140d0006100f4600d01c100b514031030142058400b10700204400f99074015000c414003226140600c02007c140d40d4030f0f44108811440c121202c14140f10902a9034400c50403000051040e84810117003203401d4018070a6442c001c1d4988192200941050180114483c94003c0c0080c130503007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 721368021 1250 721366771 721366777
    0x30516020c240a050408102711181e0c0703110709092a031e050f0f0d0801080304081e01020f0a09140406050a12050f0703050c0102070902 61
    0x20154003601c510541e03001400300c2c07100c01d042c1c603055040204004403040012003000e000f08a034580d13659035407949400c182c1c525040a1003603049010b858000142c03d4013840b65040340554400c0150340008031f0050a000c0c1c00140070307603280b680003101e002c8401400785142c0ba8861040058224000d00d020503000300c1008010125540c420700c000c100402c3e4042402451040a00c1d0326031003c4401d513546421080d819110402c10840c0d280d4003030400700380c07103402c0707440542941c2442101d948011407464982c200b1312001c000c410071030500707905042800d00c04180306440702607041c0c00403600060214402103070741d480045960400281c242c8000701d007050009c01124200d812400c002c20400d46d00322102164100d0001f260903182d0760800841c402620102c0c042e0509202e01c2e26003080c0303186003501c8011081c2e54405c115224900d40b11040c02581d903600216030030f03641c1400380d100300354a45141c50b51400085040b841e0081c480c0c1640001006000120304a03081000c2c3d080da90216075850f0181e044e40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 721369271 1250 721368021 721368061
    0xa030902180114040e1f0509120304050a060207060f0e030409180b0f0601020304031a1005030d08010303050a03021e030402100f0c12140c07090c0203040b040e10081c0305 75
    0x440c0d03521080003d85800d400150b4104100c4042e02c280820520a001d68942d00030706454141c3e80317440421110000c1440020900c4181038401c600d11720702a0f5456484000c10400200000d60100349070050283c0c90b4010320141c45c0f51441002800d80850540381c1e01c0c1c00c1449100003103030410004841860035072840a000d10b500100c84841c0b602e802d03041e0844001c000b13040070704501c810704c070000c00300d07490040305007140a00c0d018901030750814912988203041d0f6600000d00941c8007400803091a0351049001d030441e034040c0380c401d48650510100301c01031710842c40081d4000050003110440b4140380300c002c0d402584202c03010ba104500c803501c240d82e514071245c842d501203544a51000c002c18407010612804407410300e410304210460400441d05504503940c0508030f64003e19091080c40814410005d501d1305a0008600b82454400002e209220b43c0c02044000c24800c000710321420005030f1180c0141ca44241546e8070b010040801820030a90b4000d00000030707082c200402d02c1c88148810102c150 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 721370521 1250 721369271 721369289
    0x408060403120f1a06070206070512040e01060e010503070e030106120c09181e02061c0516080c09011d04020403120e0f0906040203060f1c0c15050313050c04020a0309021801 76
    0x541103c004c00c5206e4000000c20f0b60400c10402c90000040c109001c5c500440c0b12075100c6d0360f181c5081c04150005880142c0128040c40151400d92040345c0c0c001c400e5a510007000d1804842141c040b2002c24050710741039000031145909901c208040042c012040d60984100280800c6444a248440c1032140400d10018007082010003040002c1c603006980d0240700e034001b40c405440c01d000b1031a400d01b205442e284d000303407055881c414041e07801d01a1850750070072000c3e45084003c84c20190080000c82c881e00034214103224404600d05203c0346004080004c01a0084c003c41d29070b580da040c06c502918900450345e00007802240d05100314a82a0401e0900860280c840a42540d4490034040250300c06000c5a41c800030036150141c003996200c40242c0d0300031001c0c141100e03680f86031819a115880c0c0d0340118400d0048845180326a81c2c1c85410b07203500100800c0c42d4540c442c81c03802d060342000c075283d9459401500000742d03080401d80682000754454400e4403495500844204c600240300390a005180300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 721371771 1250 721370521 721370561
    0xf01060f0b0304030201090f0809041b050306040902010c05030307080105010906090b04050d0816080d1a150307090803030c0a1106040c06050c280605010e04030804020d080408060403120f 82
    0xd90307100c81c0156034014803900001034007a0741c80e114941e00e00c100d41011111010700280700c081d40e0401c1d0107a120082c1c9070403080f54000d00e0b050409440d600000301840d02a42d510061a070545e841861510303045038201003966540d040192000304004803d01079140400d031172880014209110f550100101c0369242001420f05051000708901107200220650320035070184445103000d840c0c90001c040b541d214030301560341c580042c521039003642c4001082c0e41d18020b54501140c410f0300c4420700b1509000d4408111179490f5034840b0300707481c0c4003610381118445100c040104205486c1e1840241a150320315141c1103c1c4020900d0740641c1c42c1801c85009209850650b070402c1481e010b08040c02d40d0602c18004d454020324445541861200a080c41c1040c1c0001c66094406009840c41118050076403294410300501d0940c4014003840009880207014902c20006c3d081400b44a40507078026119620590741b80f802c0c40e04005001032404500c0b07040181c40c003c40040301090a200e80d00c5c4810030a988500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 721373021 1250 721371771 721371779
    0xa0215120f0703110d0902090a180f0206120406050405060604020403240b1002030d150b120c190f0206070813150e0303070c0b0f0105090a230108030c0f01060f 70
    0x440d030700a080032040c0350320303a41420764909070708000d044940d01ea400c0003d0700b00141d004100f28400c1c05042c0b15961480d000c01040318801c1384845001c1d1a80040351801d2014261010400a100c0d03003000d88561181e8a0030700042010541000303000c2c5000c0d00c215243c0d600d0b4030702000124825444010b103a0101058455400d0704507500c0da04001d01075100000300780c00b0000204007014039841d00c010040c1c03c0017483e008042c000c0d12a405600305805d00c500026414000b43e40c8040c40b5041c40d0700f68100c10000054140c129000465000030340810b21542c00c0030320b0351400740c4001900d049042c09400754030000f030b181a104191452081311400403100031401c0f40d0300c0e929061002c44144241413a1662842c200d0035000300019030040909036160b6243c0719450514521902014100b40c51104400700108180e0f07a4440055801040b030794000038201d40c1c01018550310a01f0348149031602e8074010000100c0c584040058120780c00480c2c107a80c004c400d000243e030f013201d1807809035890342503921200340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 721374271 1250 721373021 721373041
    0x21204030221010f020904050c040e06010c0804180b12010c1d060f0c060907090905100209040902031e0d09051008091612060b060304020d02150f03090a021512 70
    0x20054000465468182c0361003800c1a425a00d51010300368006800140444160031f2a10910350f000d10500020740c1468109524000742000c080c0166041000c6005540240410700c01110000d246102840500c0011000c950020b88081c035402032040c6444812007000d0141030086100240d80d50780e840031400711207108040162044146070742c00010500ac1c4958061140004244000301d2000418103071424103211803500c171550b0481030340c660a21b640b000000340001070482c3d00c140c0140000d41c4030300c100c001180c0208041000a50b041c0b040100c0300607560030920050448070b500205540c07030710640e90415160110144516070300800c2000c81410b4440c40b0318040b030b402070740a206a80058140b40d03aa17810303201e65500192510384000b000d002c10006544280540b2480958010307003907190035000180441d0811101030302488030f98120340101d141030b100701d4040c000485d886e581c4900344021402d59940d00c030b00c4224083c81c01d010303840145007140c0080d10360030141c6011000151392800d00346 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 721375521 1250 721374271 721374289
    0x1050a0e040c0b03092a030d02070b092b030e01110c010819180b0109061508070309050f0114040203060109110a030c0e1807080105040b010207090207020607080f190212040302 77
    0x5d010768068841d0200c82079045001c17030480341100184d2400c03041c003100c04041c10b0030300b2000d0040955105903010003546000b5003c0d1020900112202c092070194201100032100000790202041070700300030700208154100b05054003004003070b41c602c0f0303000d02d0f0070748055070360040c24858501003844070000400c801c55108076031080c000045404110103030f02d002949120f0001d014120f508003c440014040031590b4440e080003026094050720148010850261120350090644800c040d1100000e00501204120305042e540c4a10003c124000ea000f01010483d9015182240302c4d014109c00040c29440c1c600802c9505041804000d00e00b04020b0015002000c0d030700c850034248030081c41020344654409010801c00e08a1034140ba450340740078180104182030507000355100d00c0c80c04141000c9a60b0001b0140f040d100715001c01aa1041140000380290107801c500038142500081c0c3c1c0e4200c0d4074103002402d42d1240b4140b043c01240d000450a80e1159690884002d841e40d00348030400c0545440082 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 721376771 1250 721375521 721375531
    0x111102304050f0c0604150f110d0c0c0503120909090a0b0f040b1006050307050d020d0e2808070210050c06150f0114070605060a0b1201050a0e040c0b03 67
    0x3480030001065415445100304950030758203030b0007241d009010320000b4005907849910440f000c5240509000d060540d0f0006070000c07008011030340c00c14800f40e50048801c0c143c45010310046a58408a0000c001c01956422408450044485400151500300040c0c0114412440000a828100048140965000b00a101c0c482d01c0c401c0300342c0c040124204000440c000e01d142e030494403051415003020b5507102c2c8080c220f88284090b140f010010307140d1000c19680c201203580382c81130f51000308200106c007030300030106081e1281c2c1c6040c0c0c040c00410000a0742401c1d0031090302c00c0c00106d5804403903a0f29543c144960290a41d00b0402c0301800500d014490101e004000e070410a05120115522034a0010112150710001050085051007494419400150b18009107000c801000005900700554065500c005261588034000b09000d0368801c0d0a60b8050a204101079407a00c4544242d00209842031081c0740c0120301e95903001c9550307010740107a140300b079421003500643c0301c1c502188001c203684001c0c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 721378021 1250 721376771 721376801
    0x1009020f0922050901050f090a020a0611071a0a271202040603150605090115021509010905030c010903030507030c1709010b060403081903180f05031306030218011110 73
    0x25000c509010b20b84107113400b40c1407000001903035240078001c016000001628503001d0307502000c42e00740140e036410314002c140c4807140b41044184410002e403a250895a4004a0581151110101405019001030080340107690f45145c0e42c00d560000c00d40416109080c8a00b0070b0310004014441d00e0325210426071428406000050f0a5a4075103550013403000c0091654026919401300300100c1c54007072001809000105001d40c21880740450180da02d1b0040c0040c02c82448150740003e10903d0298004880c0e40c2e002820b50b40d841d4211190680208900882180071071303c0e00c00801c12a501c680f094607004c5800f5204c0303e00b0194491111440c001000344510b0a540d210110701c0202d4561901520080d842000040d03107403803103101884245d80c1910140c0c000c051a0244c50341f0966071101d01410840e4200003004a04182400d00d03c0c1144652268640040c1c0321410004d100c941c150f004040e550350005c0c0c2d2106040d05080111031320300d2841c00c0344480d17a2120101030f20038082d44e07100700003060f0302c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 721379271 1250 721378021 721378069
    0x903050a080c07172a0d0209040609050d08070f090323070504020406030b010e0f010507150f1515020a020108070f091505090a0603050f1b0d0906051009020f09 70
    0x1c1c0054000c44411401440c04c0d00410021007401a04560041c1c8076145803884500606585000c59a111b200e404007900c07940381a0302081c18888183d0100c4801c41e00407061740c8100740e6001001e01069804d58003500054542c1b8000d5040c980710728102010707242d02c4040e241641d00000242c02c0a840203012001903809130090014443ea40d52009100520464502288568803c00050105007400820038041c0d5140701d2001422380c0e0120403034148542c042d03000f8200c00c1c0c0285500740141910580148640e19000381844404140c14500c41152841d508900f01010101d800326161121907070000d000c02c2d00c41d0080303401c06000e43c1c100f4209100c1845c00340c1c101956048890440b0a2020000010420009080343c0c1420000e80b0b030746c0600320740e080901c0306040c00403102d0362174000101104030301c0c00d160082861124064080303c03120a100340044c440d0386c0b010309001e00141825900041d1281010100040409540c000d40300c034105000300d154180000002403184410325220100241d292032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 721380521 1250 721379271 721379279
    0xf0609030a03020f0d09050a03141c0801030605060619030518030f0301090605060a0c030509060d050f0a1a0d110d080a0f23180402190c0b070903050a080c07 69
    0x1c00c03000303001a01950040c00101c0c4c2e000c480760b041c100e01960b01020010100010b02543c0c03288a145811603038018200001490f050154038203000d00c90a2044001401c88480c41040394800d8485060340c5c042c180400840d2501c10400c085846038010001c00e06000100055005003c0d81c00581d0251569840d62140c40003542c205086a00c0004001030190b404070050007102c07814071540024100641e1103520740741d540900074068400440b8001c0410400041200007900e4040548007042d8102805005034204503140305901102180c20b0290145440e00d46840113000300c00c15085c1040c094a000d59501d155140c0d000444100703001103070043e02c0d4031918000102654000c224454183c1d8a182d040f681c4440c00400c0a031001050100b05520a00d10080c560401801c039903842140c2c08540300702c92064004030380640180310b01c2030420100003611401c0f19401107070b1580303c9072180405010303654540c02d041e9140e10aa00025100d0780c05003641c0000280e540d001404010341c50000c40f80704540d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 721381771 1250 721380521 721380523
    0x9020604050a1215050103030503190609050a021902030a05120405010b030a0c0611150c0a0c021003020927040b070c290f1510230a09080f0c0f060903 66
    0x4035032101c0f2150001d641a0f01c1400034000f42101c211a0301c54060000f54519240103080380800b42000410488100741110a034145500c02c000074400000d06000328500200c50078025004417140854400c0d5401d07403070604c07d102108441c22000d007501d866007052209040c50b90b0000008008588542d620035800e100caa0301080442d00041c1318900c1a40a107080c0300c001080d80b0703200100400c40b42c5c00b04040c0f03602c4070300c41620150f02507046900315880b5025580c089030540010807002c0c2d0400d610601e9002c086902da00142954601034440501e011004645915945c034140b0205e07070a00601404540068002021603030085110319100c1c03401d4803140c607000760680c03003108900d01d0110409546000010107252450384480710360780034040c42c03030315404191450120843c3d803449a80004080c040300790040d07400e2000e26400e03082c1d080c00e9034114110b940b440d034802c0c0e090304045001e03400002003070f100c0029819041c0401801800c011042c405c00d00981802150f020340c2d2059040c007030302d075450720 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 721383021 1250 721381771 721381789
    0x80c0a12090b041b051005091f11011401080c121608010c0914030a12090b04090e120a0512060a09050f0615072a240f03050402010c03030902060405 65
    0x10160b0321826003070400f403429072004541c04100c019581c0d0760310b008204566402480111360074140c282140da8806030800944401c15451885103501140d1185d80c01081e402400950340b003002c04020022400810400060000240305074080e0b1341c02010703c0d030f050f403e1030240e908030140c0003000c030340b4403130076035202d1107401d4185400c40e281a030355440302d00d40000e03403108032000100045030316442800800c0c1d02090700c950804202400c1001c409515207400d40c8501803a2000340040a030030b42d140c0b41ca80c030841d400360141c50106005485826010654001503908484c01d0b00000d40300e11780341c80030454130031840d040014107166001c07421120028250120740280743c402c5140364841081c17440c000d81004421800032800c180740b948144500c200290044207520750610b5051203900b44900e0506076843c2e50801a08003108004c145803d114011903303c513069907100543c1c40780031102202a03c2201140c1085601a0000380701c030310101c000c24000e030700080c000d50020b0222407809842ea00445c80400d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 721384271 1250 721383021 721383023
    0x8010905101d0d1211090609040b0f0d05030309060f06130e011508010c030f0b0f24070b04030807030203150409141605091303020c1315150f02010b01080c0a1209 71
    0x242d00100300c001070070124445c0a803c17404c1046401c2c20b01e01c4c210b000c00d240303025030310407280515514160f0411568a0f03909140d0800002030400b09492000c0c6000f46d1070b5042500c0741141403041c00301046800041000e058800c030f80180c10074485034201c40b625005003242003c000c0140d540e407011664144121010f0703a0291039418000b060780e00c0c0441c801001c82e20605400d1004510b44849030469030f403601c0e0142d0408608a9403502d00e0007021000e042c1c00b1640285446100b0b0f00040c6041c00c020644030f2480c40b8034020303145d81190742d40e6440c0603010303071100b20b07142014095403017511210383c0707002d078800e9030241e020b00304846062880e106118588000c020401013400e100307040401091038006030260317001c45444500a151505c0d90b8005e9603512000308070300d00c0362035140c0e13860400052aa1000103641048075a0030400740c0c1d203000b10a803581d400c40441001400a600c8901190700500034607000c9081a503485205640f1a000c001040d0080030b4411b040112481c1c1c52840900c55005070610170b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 721385521 1250 721384271 721384277
    0xf270403110f0105012909090109060302011403060604030f1a01080106090e0703120305191103070807170c030709090e030901090509010608010308030402220e0708010905101d0d 78
    0x103024010041494607040c0400b03900b80f80c0c100f01c014490200340c0e094503450100d040c646100c2c0c00041c1d0b03280c42c100e402210805601b002445000048076101e80d000314080701c0c000e807144210181b030345602402501c01140e00c00d401c80001c00080000030580840e00501c50b01401d0105101c002603030a01c0348980c020b03440020180c0d103481c1e051042804902c10341e40d00200c0c0f5001000c0407440c6550752051071000520f0f45060584e40c20001e8990054000110429081070700c04011540e01d411891a05420595000000a07085800200b0b41d0b405880d4000200f903802c04007a226580300800141d06900003000c3c1c40070401e1320500011120214081c0c6c070b0302450071030701454454842d007000400c400540c0e408079200b0000d140c01005100e17045040c2c0c60640380c220280365541e60700d81c00030500c02c2d080d07581d40400fa04070340c0110080344521b1794440d28010059209803418660794141c006d013603070b042410140894000b0350f800768025801e17a001d09040050164483c0c04400b00300b801030304040c100062038000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 721386771 1250 721385521 721385537
    0x2903011413051e090a35040338040f150903031b0804030f0e0d140309041a060f0c070905010314070608190903090312050c0f0601050f270403 62
    0x502e2080b80c09940801120010900f400698550020200560307505869080d40c4806c802d11004c0d280450100001118104136525680d914080c041e6680c855103d004102244440d40303441e0007644c0502054007281000c5109075107640c2c481040164040c2e00444490b41c0c50725074900c241c02e0380d003d980c03440f07402610002005958450b030829040c5d01d80003c1c80800880f0320800000a8010480ca507030304106160038a12400403e0100c0e095441050f0042e0200a010002d0700b80c0d20800802015070707450640d400d01606610601c03450381c0248035542e159010030240900c2c0f0ba410101c501034001c2c0b0405e88220b42426035a07003255411502c0a0300150341804e0040721003064030400704250001000d4a261045040c46c1106c2d0503000d0902407d042001651200b4528051601c00e038000c202940d0003a01038a51841c2c0450054003582c4001d0080c40c1c90301801803080b803403850105200741203450180c84010304c80300006c1004a0b01c040501f0740c0e1080342450700300d2201110340c0540307684070f28032135250120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 721388021 1250 721386771 721386811
    0x370c12110904081e04090f02030a1a013911032505010503040204150602031309021204060504050f030403050303180f0a0227040804290301141305 64
    0x11080024158140c014101c01c4103110000381c03003804a51080d0350040c03402e0392500381c615420b2075520882d407003c0f504504111030000300c02980d1340158004ca0351a507080000c1c1c404501c48141c41c100c0b088115001c03801e48441020140800340e000f00c01c1c1c400000100c0400941516580030b03402801e401a11000314408004099003420007201d042102c2d05584240c1040c1c00081c180c2962650f4010f0904000d0044007060854032960441d10038155802049013145840e000c00940ea03800c020201004001c0d00200040c00310b00307030303c200c445540c098159110503039525207810000c3c0401810880e582d02c0340e480ca0b41d050740e005101a1010703601c00c40195607203050404038400881d021440c2c42d8540d4120320b10048030210001030300d40d5aa0742c141c8c0e250307000c08132010a48030b8600803d01220440c0039050700f00020085614028410784028808820200080014600c100340040480c043c0b20710081006221206102c0286021180002c242d8000740c200c814078107060301c00c291600c88101ca0700d004090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 721389271 1250 721388021 721388033
    0x150f0a180c1e030207080c06070e0102190b2d09030706150602100c0207090c0c0b0106051222020d0b040b0105040203060657370c12 58
    0x3050800546040c42003038046a070b00c4504800303260308000625900080e400204040007080c1e07a8219082d800740d1320340346040000a007044008400d070b64010700400d0358481c01982c51900f48440140c0008401d02c080c2e4a1408420100900701c030310b0000344022180d00b00010f81072407941032103244110b014580300c60980c5403040582c0d21f00b43d5030801c81000c501c0f061115503400141c1e4a60328a0030f050104181540e41c4017641441a141c221008440c1462076095105400c02c808507040340c03158801d1807482c0c0e40c444088900703028629070520818030007800b03d000c2950b00b0034814180c06240100141d2407003031781d0008241040d0360104851264502d400c00c414807607500034150050a094030251b1440c0780840004d00240708201e003075000794002e0380b40c0c2e840841450703030808000d04e040c41001001c00d5500c500c90304076101c0c03018040d24108106442181581020071041844074414004200031514214013118413007150f081c0080340c003c059904004150b00c103141400034405aa04000d00c012241000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 721390521 1250 721389271 721389281
    0x717040807030c060221220e090a02090c0901090302060f0408151602010b13020c100501030305030906011a0409050a180804051003091e0f05250e0906150f0a18 70
    0x142d412450382d26952450346c1e1100c200c814034070030700f207982c0c0b4030310107491031a1107410759a0800b0341085041400c0001078540021800d4925000700e40c1c00f90b0b06d41d12020400c0ca107202e5040c00e0740c00141d01810030801800c0c05000742202020360720b042070802c1d8031a0382207454540b0204280400b0700c041c5040c81400303a04040900705a01251009000900006000c588184e080c4003501d000c642c1c3c0001c0c18038084005004004400300c0d4030005000550303403424010a590010364010045000300d00000440c00014054141d0306217841c2e182c141800d1520704c0c0d00300100802842914a20b4442d105008003035648880e0700721042c13288048030b444c1d90030442480862034031518002e0600d80b80151000200321102032034400400d100000845002d0240b5214180e001b80c1030b40142148500340703010002803a841c0561640300d49030505d00c0c503050341c2c44a640c150300341c040c0c48085944d004403000c2080f05c8030502f0491085003019060020105c201c4d0080b5400c400c0c643d00100c3c4d440d01d111018000c1102d80c4c010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 721391771 1250 721390521 721390543
    0xa03060510030e070b090301090503030f041e03210221010e07021906150503030d02040509060d0f0308060f1c1709011409150409050414030f0717040807030c0602 71
    0xb040107440e042081040e44ca203640c0c0154004410003040f45c6c1d011f0795094004001030366010003903c0e1a401c01c5100440005c6081d00c00301d400b2001003a203402c10344160f00d00b078a03180380c01d40d6484905141014031004a02e0107131039500300180d020000650360340050407128090502c0d1942c9000550701d0001d50520400c0c024100904640100e218507280d40c6480700700304095034000c20005030f0743c000491612900302c0ca6030b01490305400041002d00620106a02802c115002078038422250740d60301040089a09581000a0040c00d108080c0302c0400c0c0b250b02070941c8440b001d00103440b08002e42e000501d100c1c009044651202e001c180c8841e04002152400d00c942d07212948086042c402054000780c214900c0c03c12460b07030f103200451084a139581d1001c140c110503021441240da1070391140c0403903002d080200c030162012000d0301a25905202d001003116590102e0035061030070f04e5000e5036982c860714003e104812840c3d0040c00046040001400320070000e5100e0503044002510b40b441c081d0030300d452070b54 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 721393021 1250 721391771 721391777
    0x2150a05150f060c06090706020c0f010f1b02040509030711150906030c0409061202120706091505040e071106130305031501050c0a05060108160302060711030f030a03060510 76
    0x61000c0003050030040040d0200072100c041d03209002c40040f65813401005004011803069406004000d0781c0030480a0950f42d465090302c8000c50320806001031041601c03031a0780040c00c4030ba1003102e19441084030095801c0e04040d501d03128451600090280d400c19111b91200b5000050318000f005525440c4050300c0b0000c0c3c40100c4003103501d1003070301201d0040401e00c0d4007801c2c0c0080042d52680008040b036000c0c02c4003000800145071107d0042c001a0748103d0101d0080901707080015115800250f078004441e4207554030002c80b400d01500e5032240f40921845c4013132010a00010400800aa00f8070b449940d00b0b1342c4082d1000e990001603450480c0c040c20310020b100c01900341d2408260321004507a4441407400791401201c0c03400340100c50a00c07880756980384902940074100d041290108500303040312501e8003290340c03010030000101240e240d6480001d6020008000460014611020080c59a000107042d154610400c00c2d41c0c500f1903204030101701c00281d8540c402e2155160210500110b410320f85 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 721394271 1250 721393021 721393031
    0xc0a0503030718080a12110114180114072111190c0803040b062209030806040c0c02040e01021b010906050705070305180f03010c020102091c0b0103031d060a02150a 72
    0x121000741c8582c0800809000040070303411500e681b44c0141100f8044da400d00000300080b03400b0704111100044c042c1c0b503903070030b040048202642800c01402001c4c41c51822414214181e00e4401094449074001004042d0f00024026001d00d11f206610481e14a05981d03002e4030f40e10100100c012210b000703031003000c000340208070079614082034200e010399901550101d071440441c2c680c9000220743c80e084400c105035000381b145000341040e4040c0c001a020310b10945a114194a903d01080b040c2c61b9074a44160002d004440348102515042d00f03c2d0300b00c0784408000515041000d924041043c0d15107606107256910380401e8002c1101c0362091035444138080ca001400c11407a6a8020841e00c102203059000c00300000304400c1590321540b652451480080080021504201c0064042d4000340441441914680302d00402d41414910700b40806611988110050b8210f0740c00741c4101401440318181b00c0240350344864076480b194001c0c0340e00407040e0010100c0d00205820a81e031241c0003401d40310980e00b41 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 721395521 1250 721394271 721394279
    0xe0f060618010b03010902031e070e01030501090c1b1b230f15090a0503060711060112211b0303050121110f01180e0403020f0604030e01050f0c0a0503030718 69
    0x3c002d40c1c0c155031a0200140c1c2c3e03511581d1180700000c00a11501001e000caa0f8203102e90550030207810043c200003a00d043c08582e1380c0f8040c040840b50703200643c0022030403242107a081800080b041c81e03601445000e010710080c8202c1400c039040442a005002544401245042500070358824559007207170803144a0f02c200e1081d00403608050105a41c404078800218401542c0d81c1c1e0200010050f01d0b024044034564507001c00010010200030340001c01038058140045000002d80b8200c0981542000d0300e0a44980651511a0000c558501013401c00002c0c00100140d201c0102c10000d00e0703402950003041d130b5410940210901c43c00b0541c098189004030b105040042c50800340302d42101400c8034061124071940380143c4640c1e80096400c082480c0c40000428001c0c6044c2c8501c0c01980650700f04c40b03900403061f50050351200250341c05001b2400603034400420398480c400402c0c80319018403c80b418060310038495842c0c20280e0398200c0e410f4001008010060781d000d03081c3c82e000c0c810b4059141c0f29500e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 721396771 1250 721395521 721395539
    0x1e010e030a0e0f0d030302031803250f0b0f0a0f0b011e050f070c030308090d1706120303040b0f100f140a0302030616030b06031e09010e0f06061801 65
    0xd0016820910404042a400c0740e9604022222241006880d0013024501d07031138001c2c029481124009201c10410840741f00c1414000155450682c201c1010b403060310242825400541e6403100842d190300d20146001c0010301600c2c84203002c2c142641d203000c0103061240510054884915004034200c0c58071740c161031960f0740203040b1115a111454144000c218a2008031040c2c0f01d5282d87c144050700004a00c2d0402c42010107190803a40607680d161903580b14001815202d40b668000c240c0040c0420020070203141c06100842e8005000070040c281d03500400ca009400c40c1c20031202500c0103601c10040181c0503c00911003980852184800c20b991400d0012003e4448003038001e8031081383c90781443d2601e0ba00c1e021481c40103150000c0880b03c852400c6c00c1c403d040103642105503000030342040f1440c0c00d2404c0c5013090f240900d4811100401c603440050f1308184942c001050322039550340752040b901207600107022960300501d00e1409050f180c5003960500c40343c0a010b081004014840398010800010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 721398021 1250 721396771 721396777
    0x31e321b041802060319020d0903120606050406080f0c0d05040614060105130608060301060f030c15050414040e1f06031a091f0b310e06070309060e0105091e010e03 72
    0x21025410309545c08040900200a00504102d200700e0781c27a0001020515800c00c56a0441d4509440c0602200c0d4444404a415018034800c61021130f645002144451090b100c406601c9140c0a121a01f008001407405094500a031015a101903031000443c0c8900d08403580ba03580a5001c0c28602d20b07040043c1c185c986003d101d4400c01040010107408981c40380d4003074200c0b50007420644022900c3c15200c0c1022040102c280c881ca05c03a280070001f50800950081c1c069804a0701550750764418015141c2c01e12014064089495485028080409c6c10303040000c5001c4c841a0283d900005030a400c2d8130b8000110181a01130480409015081002d01d91000038044841c2c13281409101510948800420103010200c0441d81e11904c2d911940c412110320717090341c01c1260f0b400c000c241905215510004111082e0381c071650450307001000040c1c40f19029070004242144143d87c0000c100c02040042c03400c440c02074441c081590442548401001d009150203100740b0a03d600030085480580c100c02d41c1c80c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 721399271 1250 721398021 721398031
    0xa3c060c09141003060510020f07080f0c060306131a0406080309030706030c020a050706021b040209011202090105090a0312030b190e190e07031e321b0418020603 71
    0x40407690f208145a8401d400901c010000a442c141240d0030b440006504c5982d12603044005120706c0d480002d203d14002031900e011f0f80500d0160502050300c000340030341da500003802542c004005c07112544110505109a214440b162804001018590300400040c0c0b100c2d44d0160070a13074418031900003103a601041c03c10449415040024010580b0030081c1c0c100a55520050810700851000041842d00410160050920020044d516000c00700070807040307008003400700b40002c20071030051803e800350b41d0090071010014140942021400380001d135054001d0b4004480c0080b0b80320381200500c0d0903008081100c141100c030b00305580554640c00200c0f40d298425101036010507404100360303005040c40c51004184140003800301c8250304811a5803200c0b036110444030000010042c40840810040411405501035224403803103200301d016940c40090340100804d00c2a1084114601c054200303e0048091007005480404080c1039081001300c0e44010030711562480300c03d5411006075140c0e82140d6020b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 721400521 1250 721399271 721399279
    0x50c1e09090111030a050f160f1206082b0309020d0f17280221030c04050a0821040b03060108040620091306080a3c060c0914 55
    0x140d59011074907409010075403103009903d035000007030052101c196008644602c10f44481200c840d2035516942c0b80a40c1207649400014404444040c00e035486202042c258480c0c05c0309c04514640c407090200e06145980e40300c200700343c0f004c60040c11002c259200c4003607185820304040111800c40d070041150207804c040001c1070092500b80320300410444030072522001100d02c03243c0344c943c1060000041248440d240c1e03043c883c040d200d0b540b40340754400140b03003500032100d1030148480350f90030b0300c2d8442a0f08041c02d050403180b42808049002d460b4400300c40000c2c0705000041c51140d10071105412407411403040341c0c0e2020307030804c01844400c1c040d078202e0360405c03020b20f131844c1180d507103003005001041c00c5040200c40f800850303400050703401018050981410f04603240c05c404d61803d41c5070011100288aa00c445d034001c00c144901103032240c05101400e091031040d0030050301c070480072044000d032000c040325100c400300711855007802801e1240e070490146a0910303d420900b0004288040300d4618080d5201e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 721401771 1250 721400521 721400539
    0x50d0e21073e0301111803070b0706060e0a0207031b1a0405030418050f0f092b0e1212030903040e0f0f1617070e0d03020703050c1e 58
    0xc01c07034401940c1c580d80602d41039030101c4520100b040e040840391440c900b104000d40c58a900141d180c1807103034242c6808070000191618002540307110703082c070913015156454010540000b40300c10300b800050810501c10540010000d060580c4152941d00261400b498a031051001c0d00000380c2011441c6444c841120414544034503a1a104405150458800d400d54425100b03200c10458000003a000b521410922000d914000f41c901804a4070f0840c0d01845000380507000c200c080f20711720075058229446009880c44e4950703645003101e100c40c1c403004031035080303a1b40405903500705d502091035042e00104541c00d82d540009501042e660f0320211f40d6800c92148004007141d803500042045170010310b40c1011001c814a40ba01c10584031410454580081c1c2c01d59500154040041062400d900c402c6901c80081d030080d5003038440c1813090010300380801d109000c1a08801540c4480f07818140741e20a50003004910b0451500b142080e21030000b8a0091807628020205103ca080b07040c48010808c5d140f50315 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 721402877 1106 721401771 721401773
    0xc0c05060a0b1c030c050312040507050a03230f07180b0603160513050d0b0402040c02031303060b0303040f0b132403020c070510050d0e2107 62
    0x60b0042c0c01141010050b5000e21010044034005c0c03a0105018032240c1d40d2516591040f040303480900b540c0302c204410054100142000f400382501c0d01800c0794a15a540341000a0407100307254006070320f411042e0505404c00050303081c1da00406c126200300d6036071459418006183c002ca45007443c100100042c41341071560449000e10f1585010030840c02c11014102d911390404440101c02a402e220002500d075107894202e603000d130042114006904051041000300e60842841e00c2c1035410602481c0300580c0d030f80f244541143c2d0041e5010505130940d400107403d6111701d400510712101c41c61000b00c1c1102000d4042c2c6810344007180c2900d8115280c6540c011648000c0ca4072550b84115046040005803198026000710840e00085440c1d058031600091700100c40c1183c0d403000180c0224410b0307001d2109005910007503241101526040d0445040c0007440c95690a155803607002c0015140 = true := by decide +kernel

theorem cover : BRFrame.Cov 721223021 721402877 := by
  have h0 := BRFrame.cov_init 721223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 721223021 ≤ n) (h2 : n < 721402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
