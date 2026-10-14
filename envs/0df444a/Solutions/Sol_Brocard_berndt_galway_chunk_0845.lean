-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0845
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:07:49.022789+00:00
-- url     : https://prove2.me/submissions/395d714a-a05b-496b-a29e-0ec15a0902fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 151798561 ≤ n < 151978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 151799811 1250 151798561 151798567
    0xa06141315020f01111e07030e03010c08150312041e030503040801020307020d05041a030a0b03060f070f080103082203050703080d0e19060b06072405370e0102 70
    0x11076003c0740d076542280d524002800300080348500307858213200d00340000303042c4c01c9080150700c0c1e04490791014014150003810461045c0f9182c2000c030f403e6900d21814070000039907881c10040030a28020f60346d02e0302c180940007815442005908200103100b54011480d4045050401b0b0b20f49807002144070010b0340e072003410750342c845994442c4107010b9003080d18280054080c004120950700e2140060341e04580d41a4045248070100b01207810265001038100309455454000d40d54030741c0c604002c00c41c065551143c54103014078010a000b004004030017084410084888010001329400d0300982d2508400c2c4c680846440010402c402d141e00031650009049004104000050110380006480c41c0540c1c035009001c42900c0403052a06c1c0c801030707040b2041e44510080303140041801c0b84e12a01e030700311001c0d20346443d141440d2100d15454001a6031185000014105007030300001c1c1e8040d0a0300685844507400404511000511010380201c1c401036040000d104040041c44041d004621050f242c1402155 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 151801061 1250 151799811 151799849
    0x2010807031d030708120609160e06090d0f03080117070302040510030b090c0102060a14150604180501080f0a2102010f0e010207051c050711060c01020a021006050a061413 75
    0x17245030081940c4090b03016140380066040c0c14291201c80c4110743e080ca142c50b040d4004d072400c1d076901c02803075041a04108140601c021545850121413082e500a24030a102c1d5192850000d0072800160865207403d01c0c031b41490300c00c2d01c4e030002d480030a482d4116000309144c0d4440454807003145569001900b640b0a02062080120303020840c801c44400a030f090310b006a507420f5509044d28030100c003085201d10b8500009441d11400340ea5808074a100410080c0b515540b0075482817001101a1040c0c25599110010030200b101084001d1000e4465070141408038420303102c20588615000c941a07641174600d0668581d14801c3d40005101040000304218442d07480c038905000303410602040368588a00401080046c10001c6841c0e404200c40e0b4580f480c0804036590070155250020341141c201030148440c041501c001e00103028031200c146e00078014030482c818030030b00341c0381c0ea070744200d002d00311900303013480072035440002e0102008200620380d9954010380d1703a91403202110f5000f20800584002150 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 151802311 1250 151801061 151801073
    0x103361a040b150a170f2a0d02030a0f11040204090c180803030a0c020f060a090b0c09010206010509070e0a0e06030d03061214070801050a1409060402010807031d0307 73
    0x28015402000c8a0b04295245003021028120750f01549501015a41040000002c0001c0d90700804a44034240c4a100d4036403001c56261965454505109084031084021036442d10600b2241c045802c540c4400148540c0c0c0200f40c407181c00fa40098128001e2128160074003003905c0d00e07940071201c041e00031552540c0c0c03091a10014480400d1180004000440058680151a100000703656000014600d50b495242d003800003400f0907030508055004a044401c001c0806008541c8a00417031407001c0b0740744103140b500c4055180002d10000701d582040c00030300000d980c00140d03941034480c252103584007500d968405681c81c1a203543c0090303114800e03480101c5d19000c802c1d40107016041c01d07012619205200c0d1016025612a4050742125010160103880132446211252040090034020b41c0d1a25880c0c0990350309455084038103136811601e80c080c00011000c41558141e00c90205006050b1506180e40000e1000300b0241c034100c1016107800c1d468100310300403030004e1005c2115408495441e071047c0303440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 151803561 1250 151802311 151802363
    0x102040e01050105030402030c190b04030c08240103020904020409061d060705090d020603060d05071502100608060f0a0b1002150a050609130501060b071a0105010336 73
    0x346240828a100000b4154041c0003580e024960040151006140c0c007014480c41d1900d200d0382c0c00b000c0403d004005000d004241c01000558021242c4040c500d0609218030300e08580c040c007100340400d006138991840b00b03248082e80e040d41d604440100054596000240244c200820042d28040c500001d200c0c040500315a004402c050b044d081d6a441d0f981c40c0019580d80c020091005d030082810400c0384014500803008603030154004102900300140c0d034940390f1030440c098210741c201c406009039040e419038041100f4940038070307000d000303101103030603c013400c1e80b240343c003505030307040000f9480100da401c03034182d00f02d82c5c3c507903030083c1080400e4109040020744e5560001115080c0e15800c40100342c01500780d000d4207201d0b0802404407a03898489038a0101c60500c2e10070f0a4075555a12500865094141c0d0010000640241407400c100c0340b540e85480020803040c0d010905051400301121013101e106442402c5e021950b5040f1012200c4807810141e400e1140f0704000c00d005c010034606204041c0780b85603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 151804811 1250 151803561 151803569
    0x110a08040605060a080706030906140106091802070804060309030207080f0a060506041109060a2a0201120e1b0d0206030a1401060c02060d0c0c053f0d0209010c0b0108010204 76
    0x103101c03a8540304113111101140b80141034858001d40c074140011070180d000304000600c1548001140310714400c03110703001a0207800032000144180070800c0900e00d40c1c400e14990110700c07101185000e0031995001c100303200e6131085200741a1584d01c860b0a040c0240420001400704605a5046014504201d03031034200e00038040300d48625020200c1c86074181403155550346280b43c1f54480c42c20000c0000c101d0244c01208803d4104080b04000304440309400c420041e00d0f80001807c62202102c5100241c0740c040c604400c10410b034a0106414070583c00025030303030340c01460000802c000042034400f0400c000300b4480007a41281000052003118803491f8408500c8641c0d0025036504e070303601c0d4202181c074110030300300103940301809010203115014668000c01c1707407030a0b600701203102d850300e1355601e070504980b1070f5658143d030110940244841c1040b440e510204854580311250406441201c1085000d2840c0500c5900c2c0d0100346044140d00400c1e02003107480c1c11020344416581c0d85c10282c2e010303501c9801 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 151806061 1250 151804811 151804823
    0xb0106030e010e030412081b012009100f020f010525110601140f0306070f090f0b04150306050307030606050f010311070b06030c061b01050603030a09140103110a0804 73
    0x1000141d4440600c154808400f00c2c0380558501841c0440b0000950407a40b0103a4159408010080f00014649001c201c180042d80011a0b1000074012703859203c0f207554111492054104142022584c0745d81c00300c1c1d4202c4403818000641010b2007400ca291403605819100070f91310341018040a021500b0911070722910307460f4500f4000e119200216594132640054181e03680c072480052003814600301c100110007201510040c090604200084d181610540300b0303801160510b00c858198540c0815244082d00040710021940c0d841e14030710389840e100742c1c401c0c05e205a50910141441c244039070001c0e0000c0400400b2200384940f2410001c0080c40c075485801d120342034000c1e030020154068002c072040c500305d5625450514405841303444200e81c0040480341e16000b41a00212a6a203550103003503a980e0340c01000b2942e5a4122130982101c5018010b20b100707500620003170146a81c00180c40e000d403100800801054104a030059025040351504c403102c030b810110b80c0e00e62080d8000c070a0781c480d5002c0c407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 151807311 1250 151806061 151806071
    0x20a0305060a0609080304060e13050408091302030106090e06040204150908060a1a061605010614040608030c1207170409020a120c0f03020a0207031b0f091b030c0e030a0b010603 78
    0xc0b83c151581c0c0028810703902c07180c000740420401d90f401110f150048580180426181004003000e600c2261012a4200d600c0c1c5804031310b01e007150800d46010750a00384074007000c600e154108080945060020310410f4030001d00180000c14540344c64065400800842143c6180e02c0d1700200090706480c4113019080c440c0c49010005114803001c0d0099411038040020010003008180052220365440340c10010350b084100c882840004500344602801041d01408000d04803c115080006407445903205da50750303030f01c00d010b82d8140c48008548a0104010543e01a54580003854403103c540b00801d8080440c5401160010394030785590005c01320450780b551610114246051a103048802d607103207000c001199002c280c0b100c03c1c0280d00410303c84205004582c00f161303480d40c03a4400c0401d60a045004c050307001c0010001d4101044003900509840c003000c1c08060107040c508401d03911015149001c00d9102c0228680340c500a52582d040d0401c09010341e0704e56a0340d030421001e01d16080c4a80f1000070f10304 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 151808561 1250 151807311 151807319
    0x702100203041212020114010e0915060306070309021804030503040c05041b120605040f0e06090303070e09060f040504030801062003031b1927080a030819020a0305060a 74
    0x1c0120790646018058055045060340c540144102a401c0032406641d070700d030350016120304c500c040c460080032a00340d03210752440c1140c042420030608404070140d507040d030000d0010356640804c0c03d0750312079031500e00061090f140c4d00005880d0301001c580654000b2a4000340010f240d4040020b61140f40120905503206070350300c0610044034201d00c2c200c000c0103804041d0000c014421800d12106220314180030980070b0304e0b180050200c0e0600c214180006584a040048000060000c550302100b0840954118544010050002112178914a11070307070420000580320750310380318040003810307016108200a1a0910700034003c0e900a0013100d01181c02c0d44200c000c408250407145482040c100d01a40c110340b1259054604001d1026030709500910030321000000c0b8407030040168118203e07680f0b05d080806044800220011004951722548411200c00e10680b1320000b607400e00140c0c140b4145400b540c41d070001e04c0100c90794040c1808220700000300010b070f0f140d141d040f1b41c0c014030301101c0b592401640c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 151809811 1250 151808561 151808563
    0x20a030b01030b0c0306220b04141008070503060a020c010207062315210106030b0c070b0708100303050c070302040e01090b01080613030807020307021305070e01030b0a050d06020705060103030507021002 89
    0x104846c02584540e10100b07864401c0c0c0c0c400a15803010709140c0012400d406820009000e8400c650318003580150344034108111142c0302c800d200e008045c0d1101801195080c10040b80d00da100041505d92450380004500500c02001d50440742c08a4218030100f10303074004091303050300c1c0280681007150400038880128011000019084405030307070003843c6020408444e9083c0c090300746450300390055035588020003c085002c0150540c413030400d95000650b00c840515010703200143c082c003c0c41c20094601e0410640c4500500c5040035640c06041054070f416040100e1441d01c981908025046400c140300c3d085c9030241500311461085c4150040d607560780e200c0d2225665440300301c4002da914800c01c103884000c6402594169040070540c810b581c60403101d900800d084803010100112029038541c100040654407580007200050241303001e02900048c0d0300014000d0206005c0c6078481e5500000b04002c1000e42d03030440321144e03031100607a0381d01c1d03950f41000392441c3c10040c8240d00408172118407102c1c0300d00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 151811061 1250 151809811 151809817
    0xc05180f0109180917090907110304050909010e0703150b0415090510090207080301060f020a03141b07090507180b0f0702060c0307060c0f020102070c1a07020a030b01030b0c 76
    0x40e03442c07055140c81d040000e46142d0303015800e60340960ba600ca0007008603841d0240c0b40100f5040f441d20607a544482d50600180070780042030b0f803040040b075150ba2141c00e00d01104540858004641445560b16004400c500400051240810920a850340001000745828080f002889940e90401460440c4403c0c803003034a6100705105203452500d00d050041880a1b8405508103400303080ca0080300d40c40742404400c81c0d11407042030b0380040340440100145540703d41c030b030301ea480032710302c09006810700135500940060752900300c5510740d00001c9000c001144008400151b4244681c00b05c5041c2560380c5205001085d003612444001541440d1807500500b04401ca041200c40b01c5840900e800c401035200e04860b0010902241d000c1010081d1304001341003000600102d9014800010b038001482201400c50041d0401d804196401403000c0b6022884494048044440c030000d200c40c0d1f07a443c2c1c0304210152040c458020740c00100440d001c400c0c4000000c0050590b803103107011403020f464111010701c030343c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 151812311 1250 151811061 151811089
    0x3020c1c1d030a02121c08040501060603020a17060312070c0306050c0403020a03080a050721030b0301150905180106061205010f0b03040303020a12060602010c030b09090a0b09100c0518 81
    0x20f40490345850042c1400741014098120480940d10105d0096100344007203411001208006411a0180b20070302c5028401c0b02c00a04450800b180790580710a8081d020300034007000d121080081600160fa00e450610150303810183c0b80185079600d903124a070807a090170f01030000ba1100c034a401c0000c3d030001381403000c072000e80fa001801c1e4401d09246a440e01c0c100c1e4011110002001018880381002504203100c400504082071030400303160703800d1a070003011503503640c003942d00c640c1c1006140d65064403100031240c00e88032900800700d0386981d40000410384044140c03140706c01e5881d080380000c0d0307142c0c064440c0704081425041070005999a06c81d03488140003034058003000340d40400100d000680254001c10400b6402d060404142d003025070074104648150703005001507511010460003465061003000701070301085460409600f0f2030b00c046c43d5107070302d1712100510761507083c40420300386c00082100e8582822041c200380701070f400400b0300501f030780c00080e054140c0589010b0002c88510302025411419 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 151813561 1250 151812311 151812313
    0x4090911040c170c040f1410020604030e0f03030906030c04050a170601090e0a02120d09050105070b3d1a1903050a0204030503040816050603010f0303080703020c1c1d03 74
    0x104541d065030308802c86026180c42c081100421000030411002c8144500a150107c1603c201c10080428404500081141c0f4400c64225404110000741c224250352040207003520030b884041a0721000c40e00d98030600e844180e010300084104100411140018029103006036050f10802d560f504542d60204040d61443c041c54015200601c648030f2103070b2125072880030501c1140c107110402e8010441001c2c00710290641c0c0d4220700034040e1501d40102e44840103080070b1030124031701800307031b1034452003044c01a007041c003848085803540104201c081d00704048640252092952041011090702141d4210312a4800102c000c00700207207220704500c142d90281d40360000b41c0384034143d1410110001c00c1d000300344e1103241c0c2d030070f01012010070020409071002e420b56030010304851080701900c0c002c00b06a640080d124490400040c00490030f691030301021298941445d00d19510b440d01c0a071b019005810f01455584a190240118003440754100d41040340d041d114070700700d0b102101e40030301040618030300075401d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 151814811 1250 151813561 151813577
    0xc08070c02091510090e15010e04020d11040b0306011e2f03040303050d05060d0510020f04090f0b01110c0a05010c0c270c020607080109090c050604090911040c 70
    0x150070704480c110b90040002800201c0c1d010b00f0380004e04802d8020318950001070602c0b13001d011440450b860b858010002c0d0251640310b001103000240382401c56a001c0303005a4001c40e10784030840b115041a2518016000c4042e00c845d07d9040f000200d42003118501d0028038075140c1030001110f4407002e64030301034555071280c41c1010101261540c220800ca40c160ac006031070144241d020b407007070002e003014502c2543c6680d0340300095483c407029180c004d05140d02c0340e0040c1031800009840019110190342c2503d40c05a03c4180324010140720340100d5200c030340c2c00d03401c0003034100459038968802ca511203c240c840203c41000708001c25941c903086810290088e09610080c0035560003242e4131215544100b128001c040d4452a13940070446060b2081075440400c80030f040459002400b8074680300351607200070625032500c2d01c40108800d40c107200d1141400c5d03880d4078050910855920702000f604d0b000d00001d0391b81c3e070703942000b10003403400030030548001407800c0040c10580707828003d200744c8910301c1e65071441d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 151816061 1250 151814811 151814813
    0xa02060c013903150b09030708060901090212060606040314070b12060103050a06031205090621011a03150609011205010305061906050f011803050a0803060a0e1b0906070f0f060c08070c 81
    0x3c1701d0ba100490140d070511a04400150094040100e180300e85c0c180000454150210b1040c0080b4400f04000c0d1324031500004104004c6445041c103031012039410a543c440341c01e203d4603080b0300b4003103242c101c0c0b0408400040d41501681341d40b05014001e50080c0c1c0c042003c0d42c2c0d14507245007280d200e030100408800c680c00550b5403080c81840a0280320100505843c54650f6040c89105c4000c0341045101c031682d424801040505c811240c2d00503003070340e1140c80520b58a0054040300000800000c0c840c400d43c4040f54080c10369100340f5102c40340012102c1c04000558403411f045e641e40008540e4106192010410b0b08000e011a0140340120f54014250700c0b44a5045401501c840e1010403540e000f00141c80f10000100b0070801206035418058084c06a9900340030b820310003070790002d4000c59a0a1243c40c1401040615007010780b50143d6a4182e9030380b1250b9103000900c140c071507201e000c0d040316004000714080c004502c48801e01c01c0d2185004100704c400240065540d00030464450303010581540840c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 151817311 1250 151816061 151816079
    0x91e09050c04050a12120f090909081902070801150506071106090901090603061415010f0504080708010609150506070b0a0b13020a0305060306090a02060c01390315 72
    0xa07800411541e001428151a03c010030381d00303280c50780200541369580034014140039452424040c10045460b040403182c280d20703400740402d8000d101d0031105554520122050020050a4401e4810000c85202000c0038070036000f99211941d0003103003101d502e801d000c48800114001c0b80c008031580540400e00f000c00c0f039200c0e0114691900302d0982c0200e000c001c283e99030391b100c08a0501030440c0c110006262800c50030088215140c6146903040d000c208003d20102c02503641410711008004d01e0510481010340408490f540110703840000320784680a40800d0b034041c1900080b098504941e4104020506036255660600c001c3c424590440380130085031010443c065802c6504c05008800400c2d1a0320780360200d003645010964ad10386840c4d012440c0c0c44190340c5401441d8105004030010f040764109221007580300c4680050092042e500002c06ca11000004c2d00031704c02080619050751225403550ba4881d841d603803021003142c0012000d01000b00568000e10034100c811480d05d03140361645040c28006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 151818561 1250 151817311 151817321
    0x61202090a030501090308041a0105060313021801080d08060301021801050a02070e0708010e06040b0622050a0e062103030c09010c020301050118060f1d07230307091e09 74
    0x1190400100c1c0c0300840030030800d000307100c0c0c0103109984007000e0789050708154440002000080c0070040c0c1501c0104900d582e21810361360012500b03001161004410f10000c0c14449000103c0e00140400303000002d95984081000c0c8045140f03602d4040d844e61781e00701014202c0c410740c0358040c0d81d2030185e54100019482600600140101c900440d00040d45581c0503407c075102c00c440102c00a0b0920005003e2041c01c0c01d0101d82241c03064070148110040e150018044d8041c90300c41d58500811580f888048419845e517500040201a00503d1001d07200d0145032250a012500c03c2c1c018401c0300c1ca81d00741040301c103034182071040d10200a5411900d91454510540d03010314000e80c10000c0c0d07a510200942d03030a102c3e09000384112041440200031900e105d2003135654942c856168240021410058142281801544807114021142c140d0b5103568080e15025503a102012060a444402d064090000c000844c002c651503110482000c0d078030b15a0842c1407504150003100c40440c540c6c20005a0b5907034000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 151819811 1250 151818561 151818577
    0x307020d030f1413092301150306030c080d0e101b06110a1d0f01050715061203020d08010e070e13020c03070305041a0a0921080703030b0f01020601061202 68
    0x20004641c3e501c0071644a400c83c2080051500e0f0015003000f45011a04c04c01e03003220084c003181205115005800f00703031810140326194410200d030110141841c172950203140510340c4402003210103500d9880183e034502e401d00d058400710b501c070075886ea61454a0900102c001c0702c07d40d02d481d0300c0c1c41c040d81c41c00383c90784120404842d09501c400e545040190700d0005000d803030b041541e0301403511180c1240c0314410940180c13901e001e040990a1010b0036684078040b0380c08181c10004402d210015030000382e00500c42a0310664071800801950010158085589000c2d07039085c0d920304816076200c0241482c0c04500b82e48420106800284241c00c1d4107001c0455068809400030040c10500d95802c6541194032007141100043c2c1c00090511148504100c0c2918100010340c016080088018001c1c1000d42d00b40603040d1281e0082c44010144205422408405c6512038a020f40301c0c0c01e42e20307014001d48035800407284101200d8407800450b501c0001c03041d04071030316981c1c1e03480b00181031000c072402940000c0d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 151821061 1250 151819811 151819817
    0x50604031b0b01030615050a1818050a030c03180b09040f06030516050a08010e1213090f060905060103050f0c0702041506020304030308070507050307022704050f0f0307020d030f 78
    0x303454002c5600619078500860240d41e01040f204540c01e58141e81c0b08a0750012441500301c11001e00c6080368072025400024000d040c0051282056900c0001900da509801000d03445040807404c205030b072180d83c0301003081c440c0e21503108881c0c5010804020068600079448081c5040c00160010300c3d1030b4101100d1a6002078000640030b031039490b86400c11040000444411164902c01c02c840d050041003400203102040c000c110440940200c641c5950480c00d00c0d48850308003080802d9001e001040b00e8004240c4040304000240310314680c40043c085511484206078038040000f4182d50090041e284180c10030300c5401284d95803441501e455402811043c1e030850b950340a072070048140c04901d1006000960004c580f91491403400400c416001000301c810050300380900c400040c2d000082c2c030800d0743d0486681e0b1558411038020004040d65a40d54164955a40240814031901060b400c00c0d040c048002c0c0c0c5d04001d03401040540d40e03c90050000d410101d510006004079201c1c07485a003510050f49 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 151822311 1250 151821061 151821107
    0x3021308070b18060d06140f03071a070309090f090201030e010c0906050f040b0c01240e01030602030703020d02072a0509060d0c120602180108160807020304051008190905060403 78
    0xc8172074115441508080080c0400108040051910304000000400304030000d2440a0911780f5501c3c00010004a000740c1083c0420503c0c201030180c920007029100c2100c007000100d580481d0340c805000307406003d82c0480d142400103d071203101070154407030700c520f2510341d41ea42030f02c2d112049a060f40030000751f5002c03003c103102c00308014108400a02001d44a0b4002240b90081c881e402c0040e051010b140c5249508408070422a42485400407411690040c4005849940304202540641b241c110030f241c465100096103020021603a01400da46d24207080740d104115021301000810703143c24080c1592140e00040040d49510b00300448801480c4540740324803129903210034007440008000002c80d1b40f5a000f2070075540030001d11541410f0241c003403078003100d0b90030180c0b2000020462010340c0d4081111100c00030314003e00030001c850060201600070788240030034400052000384182d030a0424081500301141900d02c503401207902e8182c000d0064140c40d242c56030203a0301e002c0c200513005203004e516 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 151823561 1250 151822311 151822327
    0x1b0c02010e1314060a03051b0607170d140106021009020414071d01032007020a08072907080f03041b03060605040e0a03080601030c0203120703021308070b1806 70
    0x503140a4048031444140812100f00d10440078003800030062209003d51480d4000b013001c80d10000c0c0580000c14000a0303a0b00c8c40d00c1d40804100684103004007d0f000c5210000c0b81724001e00410010b100c43e6507800303030800c1480a00013466221030402c2c0b040c1d20060b0b000c010300e0711031001103038040c00440388020000500c0d800303040c550030070380030301206c40401081c130030500780312b054000c1b8440310140e00e001d10b000c00c000c00100900e1f003248443c110410100740b1000c1610300841d2560007005000d080810102c4007101c1e40c07034082060b2026a401200350540080d810850340c07288040903031b02c05584c01100a410641000c44021041e000204240c0740344103034074100c0003180b0a5005083c059801500d0202e8614144018001940c5022074000c1d210350110800c4008070381d21038241e640046091901203162041103008a213140540103520151700352480503c04882e815038014141c1801c090525182c140da51440c85807664010b200d02d108080c410481a00c507100750140211340a170b4018409800d01401c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 151824811 1250 151823561 151823569
    0x1e0102030d05100f060305040201021e0a021e0316080a02190b04090b100804022103071b0603111905031003060e06010905010506040b0706020c0307080c0105070e041b0c02010e 77
    0x305468100c001d40b88030100380130354012604a900900200e040520040c14650b00003540c550300c0309004400c90286021680b90796100303010301001c8a0f0014075003100d450300003501da6000310b4400000e6100e840f9040000c840c08241161200032110020003401c0c1e032884903003d0020444184c20195030050340e000d40400c0c8100710f0000380c00034100103100018855403000911806801d154400c0e170a001c190300400c0300586d5940030416004003c403100b4180345094240441c40e50040e10b2005001890b0380e07070280300c2e2840c40d070342000848205035403d0145c0942842c100c002440341c804070340d1810300da041c031500603240035030029904501002d10031048a641c94441d41c044406040560340c00e07410003001004140d4007070203040c3c05400c00b02c903d189401d1410514078850300c550032000785a5900031414484550042c0f007664030598000c0320207070b6110072043c00d29000303041c2251070101245143d06900100e0406100c2d0b5210303d10403003829072500030402010344050411240803410881c141c4038043c0e003038503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 151826061 1250 151824811 151824821
    0x1e0905060c0c0a0311180c0711120106060c050706030203070807050307230304030201110408070504231e012705270304141005090913020409030c0204050a0603021e0102030d 76
    0x102841e121725003102c03150100000844c80c00d64004030041c5010900100c07510404c01c603841a540b00340344001860107040070551051407058942003c2d480e0810002c3c1503500110901200b51003031060741c580d90380b1850207a049020030b0320341c2400110940b0000e142607001e08029904911b00307091000721403100354410900043c3d0700c2e01d07074084000007105000030150240107030345135030502500d03c9042500304090203a5446d00c920032240f140b1b442d01c1c8181c1c182e0020140035004c80d80c10704800c495514042c00b108048a1484981c1d94440c4803060000844402081d03a9080e061080303c4500b00c1d0802e403d00d040003406000e4100d400c40794140400c440b2000c5024a82d4840010503409152584d26200381c2000011041403003c0c02947d500c9006210140d00408640040354100c2d503200194480c0b10703581c0454400140c0007500a494202c0c0070342850742021000c41058130032a41403006544581807841642c04c1c5100003500604402ea0b0070500409401e01d146400300d041c41168200322a0301c0c0c011301135507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 151827311 1250 151826061 151826063
    0x7030206210c0c10060b160c0801020a032003190506041d070515040f03080f04080304080106051c020f0609010e0405040c080c03030301032105090607060c1e0905060c0c0a03 76
    0x9000003400c000f40103010700c48103c00c141d41c0703001082a18600104004a0301c03419014040b500780c44c0e1485810041c1c0c1580d91b001400031240210740f80c441c44c0c4c00190007880400e00d00d02d0059019803059441d142c5900880307100d042484074081c00007074040010320140c00050318607644281c807649107800c15014181c0c8405440004001010560304c2e0405104032010410310354281c4580400c000d02400c40d40ca44448200d17a4468055541c0300c46841c010403490080c2d800019590100003800038a004054210300103a4100b19032a11122141c040039084980d03d2243c0207421064842041c0b445142c9807010700740040040c18031010213011200054111001110f08031400000000180f00006080203031280f96241a0011841d550642c2c03280424014007182041001030006072441180d84608241c0340e50f130401070310080c1c1750085480e158003d03212401528000808a841c04520a80d07050440140c0700d107551980142c1904010034040396030310000030341c0440e01c506031303d80700f03140c4030032514400071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 151828561 1250 151827311 151827331
    0xc06060506070b01050427080c0a12020102130905150f0301180f05070509040b1308130902091005040f0e13020306040506190501210201031409010c1107080703020621 73
    0x590305007400c20040347c491000d1122801050701d900c0d4034010b4402e420100c1039801654460310f601c00103481030701d01440c0c00070007404071940905980c1c00c0d41e0150041c080c0050841c10311102030b515111480b040f07030411692070fa2400301840e551103280c2019a4501c544013006030010a0644141c1c40500000c0e46a040c11101c40d441c1090b10f009010091008502400c81100d0a084508080d01e440d5100c540240152000c403412503107030030401443d84111591149810038501a40d99100706c000000d40208803d5030140a48d0703401e1a4940303110780101c60a607250304000f0704169050000d5081c005500509504080c0a620418000342e40c04100e104c0c17040d4031603001050070380341114007822148144c1e0300e146416410000107010b00b68241c0380905807031515110070b0481041c18001200901811008016019600c2c820b20100050641085066621684480f000b07003045410071035594040e841541404d4010010510042c034100c002021100c0c0e80a501a65480c55010f001102020584003c800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 151829811 1250 151828561 151828583
    0x6050a0815090105090a020d090804140d02090703150906150216031703250207051518041503060c020a140a03020c12160b04030c0f060507030c0606050607 68
    0x5140e4854105a0700c10708284096a04440c00008524112010b00506100310803032400105204980c1d0b060305d40c0c0846586081c0080c0c0050304002c189540b10b80111965021400041c02c020b0501c3c0080008251740545200350b10340d64100114000d00080c00350168142c1c1c920300018150b03d6a0060b00060448034010300d090410401c03001e440c1c844400d0b08840403001c105410404113001004402501070b101030340c5a036036664078280031a040b8814900b004074081400400040035800525201507070026070320550204d580040c4000240100c0010a00c0b021050016116034140380e0800c0f000d01c00d09044e08084da60312555000e040d141940c1282005034071030361000c4144100410304c00c807038120100c042e007000d00041c5c6009403600346d410162030091aa41e10b000600c00c404210391301c0001135504100e4038103a05d41058401da1b81c824441502c8107981404049005000403000d601114803d84a0b90320b459001c2c1d40c1500c4842d410642030b80c001e41d440720006210384550004101442c17007180c607040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 151831061 1250 151829811 151829827
    0x318031201060917030711040603080c0607020c03030702090103060b010c0f0303150506070b0402010c03050c0102040311040c080609011703040e13150513061505031c0e0102162d0605 80
    0x5484035a80031130706004110410200c1e05a01008440b401a04600481108405507020802070503d40e0710003480460002034107030751100040389860082d095a8203035900d0303440348400c0507541e010b00c2d41e010b540080424010400a0990340c448617144106040420000e6516142e80400c240f8070b00d800c1e00400d489110f503480b90190400403034051704048074468280300709515030761035000000304004e0501c01c000c0184418503024400ba00e0a003001d9000130740d5155160b00d0465030180c06c00c2c1c00d0602450a0111600205000750788c2e69214402c081c181c60440c1c0e180640d204560001c2802c4418140000c20010a02840c14010a8440c410400080b6264400c41c5000c0720141c040d001c1c4145680e15040500c0559010010b0503c10a43c04c0600821204d06201c1062411000369001c2070b451f100302e07000320940c106980d0702001507400544900720540048401607860b41c40700d028422034011600c00030300107208070038414441881c5110200101030b1b80610f1000980c00f080d004600815030110b8a02e0f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 151832311 1250 151831061 151831067
    0x81204080d08040f030806150a0c050c061602100e0301050a05011701050403050405060901180806061201060501020a1707020306040507150e0303091c05060c04051e01020d05031803120106 82
    0x1d801d941140c6095840c900c0c0c50340300c00300c040003d01e100074100010200801c000b13690f10401c4031071080f134900c03d1036501c03e41003201401d10104242d01b1030743d6026604040340301e85440000d460108c00000c0d00b042014006600304558002c94011540500845c00c6005525480c2480b69a20071610a58000b586505200c90a080ca4030122001c2803268140300801c030010b5880307000d070750071100203644407a140c145031401601d0240c0315815012600408020000d14610001211401070038240d460180e24801410f150703003070b02c600f8000c4602682c000450440003581300b88004001d03540c1c80503040d00f048075030703400241080c00544d002d82d00c0303501900c0148518640480d0204000307110342007100081c1c403030002007512802404210381c800c1003c000241c946d039203640c2000d015240d2013000d40f1010b2900100ea4001600302d030117100c0c01800f500485004040f0744402802044005030020040701585400495960303000a007100c445000341105080208000c001501c40d003814454015050f45c1854001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 151833561 1250 151832311 151832323
    0x2506030615090e061c08120702030a0e09060409060207050c01080a062102040e10020c0705010503011202091819061a0d0311150406020c0d02011104170708120408 71
    0x14100401060181c000346907049541d00c400c59107801c0e03403100595100e800041c00c0e1060f0000b03c00d45c100301c1510800c100100309004102e0b01713101c2190180e043e112003030100da503809184080e2012403030803680b400407440c161200d207034401070050010454200756902c440698000314000c43d0300341d01111441d02d031583c00c0b5043c039034800000ca00030800d0324070304030441c4070001540300d15940e40300c3c0c2101041d0640d01c80703800c4548174039540c000315180790391a80307507141c02540031540d0b41c1414060014049000c2d0b2290040f241203414881100c42001001d03020050592405001d51426518481114014540603c0340810440ca00d0402070303001805414285e003512000c0c201c0c010110b009101d40e0300c503941d80d01c4000070880e80524101403940c5009844624240d1505c08409403206110b040108002481c2c0051015a0504059071002c1250340c0081e0f0a803103800b5200c03141c054003070cc424070103c0032100c08428054040310444500c6980c40080505044030702c02c0d07185114000050902490b0010492 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 151834811 1250 151833561 151833569
    0x80307032009060306040b0303190f090e0a0b030c100c1106030702070e1306110309011d030f070510060308040e180d0806120d0807020106060507020a150225060306 72
    0x810072551a80100015040c032402d00c5142c8142004000708803584c443e640081c1c5050340142c200c81c1e68107108210107072500c5420382038500040c000e64183ca41188a0072013070088400c0179881c05032a894040480f00039224446140790184503501c0303042c202d95180e0400e8403e0146588900c0340c0c14515003818003007503450f051002d0044c60104103003d601075001801300708903000008161003d407144a020402c108241a016224506210700c42c0c10007041c03003000350700031442d420003001804c070b44141c801d0141c0405e0321420440d82007806120000b014a200034840184203605590301c0340400e5001d20103c4100d81c200703807078003680880c083c0f0050004880858012010001c841c04402846040583c1c65815500110810203581d022610a41710b102d014035082c81908241d4640002c8800000c003040c004942200043d802c0c0703140020114015421101c050307030081e004070b6480f403c1120194420a902d41010214403031098011542130008121802e040000720345c65111500d8814014180ca080e1b0304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 151836061 1250 151834811 151834841
    0x1f090902041a031e01060305180d1409010908010614030c010c080702010c02060405100807030c11121308030a020109020102120a1b060e0a0506010305190201053408030703 75
    0xc00e00400c518401c41042e400e124000780baa49555000c0108003809807a0b00140100311450000300d02c1940581003540300345035034002c15080810f10b00e8841c0d07440180e0766882010a041c0e40754400117440e250001c1101c40c0307042c1400f442c0184d076017008500b100c41030361110201c0c091109605255190a0100e11054103092030075809020b05515202840d111340f0034000c2c10300c40f0441c8140215168002500c00034040280350240142c0380300c42c05000352000700c4030303580001e1402c0d03001da505901482c0030f005504040380c02001c001c03c0da801000b040c0d40c07050000d40d05aa032034800006400743c1c208010f000c0b0724403550011030016010310001e4174005551440000c00c000330b02011072010747c440124210b940898207400d2741407607103062120007000350f804011250700842c00c99605100000404c035040703a104904680c95407103c10900484000c800000034009034041041801e95803d607065222040d104480c860119058440080f118040c504021500c510006c070411485a80521071011200c1d0702c44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 151837311 1250 151836061 151836067
    0x20f060603060c03070e0a050904060213080d05071403041a0a020d170a09020409020310020405131b0c030905030d030516090311010c110a0b0c0607112107021f090902 73
    0x154a808080c00000c04200c00c011031b084c0e00c03401c0c654501e9410401003030051300f14003141c1040d0802034003950040c00c050190400c03062002800078000107a08198100c40d41e0b60710309141c46991404075185000f21030703107030070b200c24400400c4100030642010311212101e8241c41e038454014034041d040001480c84101440701c500c4180e0700002d28406425840020300d0303030006a4090a200160060102c108003a415114440d010660300710380303600078010303600d0860b03109103440d01b50710940060720184601400c1c0843c042103c86002c3c0d0180c1d41084000c4c0c80f03820004211911030740842d140c890741d07149c01e03400245c441080c061480301410714079118001900d005c10b03019086031210017841ca800310b9212704000049400400340840c1c1490754483e508010000f0108503503d05601d00b168002e00c00a810034020a00414162030142515464400c0902c001d8400c6a006160000001e000a40546c0c1002c900f080303507d0061f5914180070300c800c41c00d030148030013444c840034004104080b150001101c0c1d034410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 151838561 1250 151837311 151837321
    0x1106060108070804030c05120301050f0f03030f211e01081506060a1709030408010e0307030905091503010e070603060602030906030a0e010213031202060a0212070309020102010e070303020f06060306 87
    0x2025003103500c00420f08128043d62103914089070f58040e4560068014051a44840c61b060325410040d4101c0c0c20803900c01c0e0f1800b0501e410050b5080a000ca40c0b54075034000c00c110711920040a001d410140b40c4c039001d1050200c48180109030413201140d90300303000d120f080e030701da90b08680700c4500c280582104130080244010190304900f0721240a420030744203490200d0504802441440d0307100c2031607100b2000001e10b00b044003407555280c1150041c80c91039400c08448105606000094908039909617071440c40b2107140c0424070280c06005400740960412100d00d40180c1e460134091407852004010007045070500d000002001c507109a000f2404540040020741080d640c0c5105803600000030500003d074980072110701d18024401d1500307141d0003c02d42d54000050005100d81d8200341e0b00c031f0703809550059803184990400c9108005090b003140b4401000308a50b14420b41c4203080492040c000042d482c1680b034001846e285042d80b00701c0050307000c1e41c0c1201f601401404070070741180c410b500402440c140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 151839811 1250 151838561 151838567
    0xe010f1e03030e1302090d15050a150b09010302070803040b040506010e0c070305030a1805071802090a060804051203100f0b03060109060f020a0807080c0f0d080604091506060503060111060601 84
    0x61083d565114610003202a40085080c0d4100c60013071000401c00030040b041464101501a80c514080913201c0c5801c0026080040d035004048003240109a081c0999082c644043d406070451815541015400c0c058100066505001140100d01820000615181924145280c20742c160410b030f828004035414080d1150304035090750380c540c2d0300d403e15a449981d1006032000400180c0789461101560400329400c1c4003012411206640220002c41007280c2caa204002c241d2040c1c0c040036802100c2800f00300074407480760f00c000750002e103d00d040e07460b0076034205c400c8a5503420656854030711a00c0d03400e0070410200c0c003400d507000910031121507500354070703011001910101c03003031161100388400d081d032003003005200740001d902c0203601903900380e1218402e04000d0711540012411a94510900c1c161954203280010850b60a0781999600c9040e03a85600600000d45039801d0111088180020003620b6007495010380b0b005400c0b1503540c83e407a841c25000041000703818480380350341904000305020240e68 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 151841061 1250 151839811 151839827
    0x1030b10050c0a051902010f02010e1c0e0a0603020901090f0f05091b07060b0108151003020c010f06090203040203301812010e070f0f1403070e010f1e0303 68
    0x300741001034403011409070540c10800718520007000c07030040700e4041d15051603d411721001e960013a41c6040c5c07081c910700d90a03400c9804004402d9115400a220100201c40c2d9000180c5c0001043c9082c0c0345129481c404180f68903025041100402d4003c100e0066650b481201c010003000800c040c03d002c00d00d8050100c1c03100c081c5024850043c0013002c0029a818042c1941c100461041030502c0d9803004142881401044281409030010b0012008076868800301407a04074009401841c500001c40c2481082c0c0003507109103c1207059540f502c10700340000d50984180d0f0010305406801507500d241500c10941007140514051010b0050405982d4220300040c00c482010364001d44120303078446020300c090300700710005218644d00c18020360500a10400641054030240d010101725201c0d03945407007030506000514090426a81201c2808214035030321101c030590324003400380030750321080c4d16052400d803401404d030010701005031035200404c50f101104181e1025503040f560903074081821540e00800b80e035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 151842311 1250 151841061 151841089
    0x1b1d0a050c0f0723100504051903021903090b0703021020190c06020f0702040f0c12150b2b090c150908061509090715050c0f010606030204080c01030b 66
    0x403115100204c0b004003e90040c00060b48503c04558002a0380c0301c0e51809031600311012141800b07101c1b03605801180b400d0884400d680e140c2c020302444403042699100350f0201000603000c0207218038001928150240040c0003c901039800f0349880821041e003541540c090000000e401c04102d4900025503003000169500710b0800701425800740b11101044802109040d4054881c0d0b05c00511108000440e000400c1918030968052117010000e008120444080810790404070300914018621440107502450000900d5180130b0b20707a94880d1104003ca4001b004654007408a07540d070110f41c00303052610742d40002d45e02101444491169600c0700e00c5043da900c140291201a841003103070041c0591ba0000c041c16041048540602d1305003610550316540b0301c8105d00480e81d20012400f440e201161907803da59075a8280c0140c001c0381038048030140d114450b0403105018103001c851060b0400e01514008200c5c0313640260302c1d45d0625404600740149103035414181407509421000c0c4d5142d1000e1031070300c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 151843561 1250 151842311 151842323
    0x81006090e0907052d0a0b030a0906060b03040b091209010c03030216050d020d0e010c0506040f03050c011404020a0504050702070b0f09040905010c03051806041b1d0a050c0f07 77
    0x40d4036550081d5142c60f04a800440d48907075070004072115504142d4922001c1840b8400070310759814071505004540f101409204070f005010030000300440076503044500418490280054516a10b0141c1c100903081035a04131303151484141404001001000032401b1541305048403031501c0343c40717400079111444440f0010185034012500c150602d00c002c607400203442d00907040c0d46891042000081d12521101003920103c0c600c02070400595100e8141001003507888001800992500c1e1500112000391200440c10003034200104c460903078080c0501c28200080714580c001606051040042c01c03500ea401c054011854941001805030340051500c0c01c650003a07080c80d545038901050240b0b42d124050500341c0080c10300c07402d02d04101e0f05500084441c0001d940c00c00554030769194801d074922440844c101694410300128020521005844040a2002070f8414490340d44500894041c4202125881340064840c00c200003c8114000c43c2e9221546100c0942b400e450943c0c003c00d103010f10000038000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 151844811 1250 151843561 151843589
    0x3170301080a03030f0b120a03090602071a220906050102010606050313020906010207081b040b0d0302030d0f0b0a031a060604080d0c02040906060806150301020307140315041b08100609 81
    0x109120503070012000315000f9103442c0004803802c418623501d100c90a0110000b130060240023848510200b41302d4107403042034011006d001940601c000309a0841c100e035038449859820078103408000310048000620f08a800460194903141c006403c455280c1d00c1481401400c2041020004107000600c0541b541165040919110940100d04c3d2a001da0000083e510a41d1165102c9100540448035400c070110790a1100080ea1018003002d15942400100941d000b03010340b104a84194122440074409182c00250787d0071003c0025070300340b00075031082d2051058010315124180355600001e03030000c0156805d500e02450422110f9403860070940d0b20301081950044681150b4540e0044100180c200e04184202a01c3c0e0602c103483d80019601150b004002150600c0b00d41018000d0300d03c140c50688480514401d8840514081d500040c150f060030108040d25480682d1184164609100f003118620400c0601c428041c0c000c680c00740c8038071070b0b0702075092080203025400b26056058900214103409 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 151846061 1250 151844811 151844831
    0x1270911060c120f13050d030c080d090c030606031a0903030606180303030f010f080a030519030e1203061201020304020a1401050415051306030b0a14030705090a0603170301080a0303 80
    0x100b07050f424411075a800200040140c0582106809403900e6092600f80c08a0103503580c041104c0c6640c1e1002c0200441c0045020102060081002e0700d2040501c00020400898079039841101d01c06c6900112036986da00d100c14000d004d86031a04095141c0428a1525182030811950381c3e40e0000030005486103a00084280c43c009600c818002048400340031203440781000083c44c80411002d0191036503440c00c030303400000c15180c0003c010403600d4060700e071940b602d84145050050030390030201010034107032103070755040d000c8130208824144607645101003074032804c0140800825a4083d880d103102d5a0045c401d00003d13a44560108045070481c17000c241000f0701c00030040c1c0e203600a550004264140d20302028800c503400030700030712a40e0001c20503500e0300c0b625000180d046485986070550400710a0034140200e801e12030030b8107a4a44c00030111100c0bc2d0303031080040d5504030100c41120841ea1100300c03c0040010540e058407440404194144c11581071103038a03a6101440d0401404164982403134007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 151847311 1250 151846061 151846063
    0x916150c0204090503042d0909020d0f0302070806070f080105040902041506090501030f0e1b0604080f030c0c010f0215220609050d1404090e0c030601270911060c 71
    0x2800e64040e000340800c01003800c205440741c01070b10401c1158404e035081d004018084114a20540b9640c0c120f522001c3d04100c00303800240040f180880c2c204c2090720000001c280c406000042c0c041c841ea004001960614460a04240303003c1c0c4010b05020041260030041034000b400c044c1581d405480c00500490180000303400341144003510110041140700129196038803105040540c1c00a0701c090002c000305240c50011a0070346807201c21030341c201c80444410103841202d2205078400c01017400d401c20b91100135031400e00780603621700c41c45648005112007a04000344000c8055035401d080400314040c40d8080a52552485160a25442c504500007580d15a0303907400340d44014000c048509241c202e0b481c01750001c0040f00780036039261080282071685503200b030800700e0660268220150800d454100d524010300450700c0c0100381409502074030440d58400304140c0c0d00070299884210400d61b00c0899050385203003121800c5842500300140c007008940c504140e11022403080c1c45060703071854108401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 151848561 1250 151847311 151847327
    0xf03210403020612040c0605041406030702010f0f0605030f070b12090a0b01030303050403030e010c0f1115040309050909010507230909012c010e0c1e040b03040308091615 75
    0x254480f0003c940382c002600c0c0190b103244290700c16584096215290b09059501c1d010704c0c0f0820110040ca07a0b185d440509012001c0c44c0c0041d41c1d8000070440101d01003110741070f20400c0e40c11021503642d40314204194941001a0440b8400d4500900380080c100101c0b210248142003030400ca217180f20000c240c4a000030083c04d43d1003034000401d41001d585a107402000303820f09803001d0700000c2c10b10500c80c000b2541031190034161501500c800c00c0107041201c0603100031551038403116007401000340c1c004041401c101c0c0e052007a403080d0344240e00c003070821040050010014008410b580e01d041e0410401da60440c4a0943e40c01d201c461469101001040d113450522420b0034468104908500006030201c02c140c056005541940422811124841d542d00c0b0b503000900c0b40051982006d80416014805036005044030000402520091401d1034020b02c250352195225510f18a40002040700737042d80400030541240844000d80036500804030008005629806044405400c0601c40f6030007030b000d4620 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 151849811 1250 151848561 151848563
    0xa0e0402060f0a02011d0c0f10030e0a05010e01110406021203060a090f050403031a0105120414070e0f0109060821041e03020a06210902010201020909190b0f03210403 73
    0x2e59031a4090a4000d000e44800c401c54825181300040c021203560011030881102c1d2000b51904240b211070030104802c0314400040c103010305665284003442e00c1800c0c001120501d0240c0b002061090310b8140c03e50071a80110f0354221002c0040c8414000140d001c01c40c52180030503030704030a880c0d4941c5000500780e000a0707800070000a00c1c0803c000d80c51a070703503045544918003e4900b00020300d28940c42014100c00e4103495800124108124005082440d00e02c40d0058040c0c01c1192501660b0240540f42c040c0c150012100100804100041d011048240705d014001040003070040c2031600114a507074038a002c0320b00c10303c241c101a40d545885495000d9600801402c01c0866003450030350304c40d0003041d0041c04113138020300031000041100341c05075041c6803005100680d5a001c90b44200c0540c0c00811035110100e04554003009002181d80c0c0c0d032032201e4055505000030564108494101c0c0d0100c03a0b422615a0103110003100698040d40d0200310028110075070f410400c01e00a0803c400580d510a6402c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 151851061 1250 151849811 151849837
    0x705090103110d0e060a05101205030409020c03040e0105040c0c140f011b0314070c0201051e1201080606012f0f0a0501021b0a0c09090302010b040f0b0a140a0e040206 73
    0x902000d0f01d00d00341c008480303066488081d2641500c480ca1114159007046a01c20340c001d00e04d1100f0000c0d1707081110a05a2140074801341c034281903c40c01500282d0380004201d4010354804241885400314042a00d401000f085400700003c034000300c00a85856000d5001501d160301d40c40034de0f0710720030043c4803103103803003030040020002210410340c448581c03a1910f00600000f0b1034401c0d03500401e010ba1840c0b9000b40b15948681b4404c60b200e82c01103901c0c0d80a0b614031200c400c810441440001209000b5084514001080300c08944c1498401440c00c40001c11242c1006814407450540480404020741c102840c0e4041c42d1341c00f070086001d80d1034514a43c9610310a8030a809410301806010740c00741241200708440c4010101000d8007503a911a0392181c05002d141c0300740c41c2001603030791503409030040510134000807031307100020f60004d4200c952070a00c0d160315a483e14414062454181c8401019043e0b621082207036540b00c80c041452070b41140182c240c000b042c9000f08041d55202020f83d819011960 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 151852311 1250 151851061 151851067
    0x90a2c010902040602010c0e0306060d080403121d0910052b0614010501090b1218061302010201270605060402190f0206060904030c030e01030e010c05090a050117070509010311 77
    0xda0714600940c0284a80d000551900c021385c41124071400c1d55804044006009001ea03460784c80802c0b0a03038582e10400c880c4040100000000142d1586401083c14015200d01c0104004122907014051801e08010311505074001005421043d2030b59000541c1d500340c4005c603025440d15004d03aa0700281441080494404080080801010b900240001820381415003496640e910056800c1c40d00341c040c08001c00002d00a015603d280c0d4002541d02205104140000c048410041800c000003943e1850001c08114011420365809024021207242a03a0b41010b16001d1204901200c41200400030031003034032000810516581c9030107480440c1c035540250b0300d0113224004003a210380a00080d04015004d25000034a4a2409801151046030035440f01d503a10096594102c94122120710300d5814076a4500c40c0503035031a02403007861420512034640a580d281a10108482d440e03142c1e03c150b04000580c08010541c01b9409101c6811800c44d0034680d40b0b40710074500580c050400030946448040c804 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 151853561 1250 151852311 151852319
    0x130203030d1802130608030a0e010c0b070509090f0c0a050c070504112107050913200a030b09040804290f0720030c10020c03060408040608010803090a2c01 68
    0x102c425211203a10032200440b8450400c01c52070151071540c41103007066002801000012030041c101c1c0083c205d0140f4003c0c1000c1420f603038000c549281039680d800041c00101e4258450305040307136942d412450440443c0451b203480b8000032107600c1041200410041c011440c03119100003042840c0152800400c01c2c407414040030405000380c3c02c5400e055103001e500202c0400c180403030481090151225644107413811614805000ba1020507001e9014990364501d17880d8000d1554180c2c40113040401ca0030b45036203085610009007a00d40c17144525114181038401c0c400081c2d107c900311070450f1700465403c100315200c80d20303030350100d00c4030310f45490340a40000d603195024100074018090b6600c6680c084100184060903010000345070812581c0503403119480b007140d850480e00202c11180305104039502101d20f440440d0400000b074500711042240402c060000582000440e405086581c00450130720b004040040c000c055036100320003802c0e860b11901040c890f22500c0b000d0201e000103800d02003650396 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 151854811 1250 151853561 151853591
    0x9110c1b150d06080601171902030a0f02060702100e030708060112060e120f04150c0309210215030702120a020604151107050703150212150d1203090203060a0c08130203030d 76
    0x111407c0e030390240c02000200c02c400c1880300c0c10441c3c80358001c0c00500c000c05181e82d4403450360b000040140d030f00203803c0c0010b100580d6030019040403c1c2030395440c045022100d8051628000751500b100a003500510014400e08540da00e41c83c496680150000c10542c3c0c24220003800d1100d0540c4070020804000342c4003504030780c2c41009104680d003030580c000364115a03c0d81100c40c8203480d40700070009554200200000000c20a1691010040c284051000340c800e90000340c01186e01c65048074400030110406c021a60140164899a551020b40c80e1070120410300003911036000a20040411596501010362600701c1d1b8406400840207020a5554100f1418030301d0b42c0d0100d911049030005c0ca4120700000001e05402540d46120414160b035000751a2501c00a160a510407551034000641403030001c041205e030042d01e20903020035180003c03440c805005060a1410090045200b01d0400000e41d01c020341c8070704541e0f8401c003600d0b82c44601c0744407440000d0a5105910f0708010990422101e20708030341c1d0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 151856061 1250 151854811 151854839
    0x2a10140f070b1303080106090806070c060209190806070207050310051003020d0b090c030106050a030605130602030103080a09051f0c0201020f0706030b040b10050702011809110c1b150d06080601 85
    0x4000c0e05e9581c0d0f0703681d8aa1045941903464017556895400280124031040d00504000441e1071043d80d01604003110031703010802152a510328030400c44890b1500300a0304006200c1550003a4192020f050b80c00e0038000803a0340c3d03182c002981090b840d91030001030045429070000b24040c59006007403003950000c0d403e080c0818001541c52200c42d005000d0b2545051a0520916003124001b4046451040c0740d9101c01000b084001d0107000302560301208200040e14070b200440c040e41c883c0030010785800c0358040003051000d0981105024542030461144050303189200c00c1e001031914545807503212240d2004038201032002c0045905403144c42e00104086425800001401c03e00f55010826405c182042080725003070546100003095040201e040517510420306594071200d065100c59106640307110010840e8040003000b0260800490710000e4844140064041120301030121500c0440c900d0000303600d2210640d004110410000316020003603196088040240341c4582a60441d40e564040e0000a607 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 151857311 1250 151856061 151856063
    0x21905091306210804050a0f0812070c05060705011803020106050117312423061c0f05061b030f0c070303020c2a10140f070b13 56
    0x3056030400d0082075606120b0001152000d498420f0f80c0d890464001041190510082d15008401c000c042440d0300c8110400006059400f0720181e81450104d0170703805d19540502061080c181041a68049a50400c4007010344e142200c150381e490381c0a1904900508420345075285203c0b00207106000d164042d4891011a002038940050f4501c0348401d0701100f1408540e60004040c0b00c800d910710040c4500d041710b00c0240851500301c7d8001c49610780003c25004460b92a01e0310f8105940844200541d005100114401c40315a480c428140d0700c0c1040b403414020001d44c050000d82001c1850003c00100d0078140a4100c650020303614060704045440c1c160840306502c109c691b440a80e8410b0a210048030704c160303820b404034503598503072000181c20340c1e101c4a8117408064003405144605c00040c080103a0000d44034101c2200041000740000c4400102101c0e14407507410407290500d1103820031519101150f011659950390321aa0b98949080d0042d4200a40ba8200d403404004610341c3c02c19a1030401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 151858561 1250 151857311 151857319
    0x10c0806040605060a1d03010608060a1505010804260f0c10060b030c07110f1503190c02070504020313060c0903030809030702011706030709050a092306010e090102190509 75
    0x41a120fa05008103845000001c80c009250001070020700c040e500c03100c4450010050010806565a007502498600b00307440e5600d0103540c54012000b0641d1440a0b10000c100a0070804c1c0203250030f03100c1028216540241d00e076642d0798071403541c4240010b05c00715208130010546003502d4130015242c1075555003c054054507890f203403810218100005074203985c443e1a400002c0391400e1991350304ea03296496080c03102500800d20205454281c1c0c0c0340d03117002645c026100ca02d0b03a12840d14404c650f9200603d015003401440c60208201c80d019400714512043c2d400a0b100565a501e58103c0c0903040205008050400c9147c62001100113601c10b8220b001c882c000d51381c482e05922201380c020f03204d20071140024040f440800c1c140401d401617240880c1d00000040c2900c02d82c5a6403a403500a4410480b040c6015551700d5600100f013100c05030301d041358604030000505602060014459440106006090000e025800000c1e4408002d404890b0012488107091103d0010804090060703040b440c105445 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 151859811 1250 151858561 151858571
    0x203011806050913080c0111030a0f0b181506040503010c0507050607080108030405120102090d03020715030e0705190b0a0c06051608010308030903041e090e0303091c050c010c080604 80
    0x10918103610241c0c0143c41c00b20b00d40042c084c0c03a503144060380e0300c04205202c40307540303480c0c001c4102c00e034a001844c41140032070000300d50302114441c14000c98035921700561141a000d41c8280070300142d91401a4010341401c030000f0400c0301c1800044150050780d001907819820644a1600c081d80000600035042c03060045410f40e46850301c4c02c6c1d0760200c09001d420502e61088c00b08104901c0c1c0403812031280a201c00c001403a100c1c42e0fa020940348528540207801588c080c00c01046603070080308480d9000001440c04104a40c41050900d07118859486564030500403081400c0b03942c030005128000030300550b098140c0d18142c0610141803038101c0d072000d5800e146404001800b24a001141c0b0340e9017842a41c2c0c0344120781c210380c1c880c1a13170b400c0a0080a190b1005210215034080071620342881d03081c05100d140d084500d1b01c0469015100c404828450b5a00705100f4480303003902c0015030303090b1380308040304a010201c1b00500c101c03098003c1c041e4002d041e40c240182d03812055005000c1a00840c0c060300e00b849 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 151861061 1250 151859811 151859819
    0x304080d02072d090203040f02010207060e01020601031101020309100207151704021908070806010e071107031113050112060605031b0402030606040b07050303100501021501050d150203011806 84
    0x42c59030414410108240c00070f081c101a0b80e09860b4a011015608440841c1141c1c0c846403000c00f284c1088a045603599544030b442c9045d0342e01040041c00600761072800780710400580c1c0000b03407124018032008120080c4406c801402e0782c002d10075200040e5018103901920f01002c08001d640300454410307515081c8408030802d11162085145004240510f040c2d0b0004e61229400d00496203080384484128220361440401d9208060101c01c0080079548000c0c4070729410260507004421014003642c040c04041c1d0940182e1300d4000c560f22088980086110701154a01c0020507101c2c0900c4404c645800c0c5044008207016000480480a9a0188008000d6103803208103050f07480c0000d070041c508800008900d28520724240e0011540300e14041c20240c00e02d40d5522013204181c0090100b02e80580010040202421080390154020b0000344014081d004160200d10034030b0b80d06004041c0900d1840e090030041c090340f00400e84002d0103001c0d01715a2981c1d9240042c0e03100c002840c0f0711007110f041001c002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 151862311 1250 151861061 151861063
    0x80a060803120c0310050406120b010b07020307060f030219170906070207050607020d060603050703151404020d020d051b040f290a0305100f111204060b040b120304080d02 75
    0x50b0b184001211020110b0300c450200078403d0704020550fa400300c00303001000c01eaa843c0d074050400180707141088000042ca01d4501405880b5050f0022807450409006402c05039800044400486500f0f0600d84541403064a044000c1d00c0b503c0c00e6aa0b032701181c4c082680c5003070f41c0041c88041c003158085c20b111460b21000c00c0c1680b141400e40d001c00040c1c5c41040e00344400d00d00138000b84a000e100800c056146040781d45d890051324055030080e10743da0000c040400602441e00210885618042c07010000802c541803188004400039201900480756101035108545492600d03500340f40c0c1010480360700e001900182d41c1c810950b0302c00f0074000da007004744250000500780146640c80d540d000d0403405601e01c081194000382c0750404a554800120180040070520a01040500d20324644001c1110120340c81003a0550700300b00c0c403408480d081080250101d001001c000341d0016031211011846c0c5841d080007074085c0c60080380490340a21403005020890800000034012a001138003514801c103506a02a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 151863561 1250 151862311 151862317
    0x90b0d020307051210090804080f03070803040305070206090619120c0801030f17031008010b01110a030e062110050409170c120703050a020601080c011b02030109080a080a060803 78
    0xc1d09544122400d029901e040c06001d58041290300032203200001d9004803d00340c030301001055403460710016007031102441c14044601c2400500b0300840c680074035a139480f2140d120041000e800c0001c04500ea600b15501c880840742008401407406031111501d01840c826041680c40035008107001c03036101414130009010307070002500389459012140e07103140c5400500040d03031442180d004a06c00b902c400546c00c01000355014080310b05000c0c4815083c04946403c4850b044203042c140107445640000030900011851411903152401c40280c510090120f10180509403600074814450852610800100c1900320702c515140303107003000d896076070740c040c0021101206400741c82a01001001050350f012000241140031046048698002d01c80c541c811140c0c200080880004400041400006030304200603809040704c0005803841811610000e0711013002058200056420030240900350b507402e43c840d0300c40e1780d00030980e2590307000d159070001e01c04401100c0c0c002c8821701e41744e0302040c0c2e00000000d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 151864811 1250 151863561 151863563
    0x1401050a060e04090c031b091109040c0201060812090a0906210f0501151805010b0904150308030106050310090608030906090409050a050303100905040203120f0d090507090b0d 77
    0x6141032560a2940848080c00d508100c1c82d0041d444800343c100196286504000075802210118070013042c0d0745000c102c2d940c0c00d030b00140c0b072a42482c1200c1d075505150422180c058800b1a800074032880c2c5504140e01420069100c1c1d4000c1c02000b60000803100200020700114000f02c03200410030f40c494024104a4050380500042e418030b83c10211340c4001105d107038003145400707260b98180c062008c0c1e4940e8251410104090884441030000300319081c1905685610308960f0b03182032090b50f050001c0082e960084184482c441c40d1206499194511307145410f01c05103410054540c0d80703603103030800a4015070041d41d401d00c0740425458001403502c124403485060701d000d28059861300d2100400c204550b08641c1e040c80d40141d0324140100003800820aa404a0340b080c1b0182da100d20340710046e1100c43c2003d41c4044103490805c000c10006a0300800d540e8610507055481c00d44030880081c0c3c0c00818000d44805540132440e1601c070400748000051000111412904140501825581480204a10100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 151866061 1250 151864811 151864819
    0xc03101b05070c080a0c030209070c0512031b0f03090706080907120c0b07050f0c030d02070e070203190c15110306040506040b130501030b091501090209130f0f140105 73
    0x8144085907110701c00401e211030240d21602d5050352100311113800e010351700710122840311a02e0020811428412040c40e8000f5541c10000006007641d1509525400c0a0b005204900000000100303804200180142c0710b921081003640ca840e0180710100c40d0368401c1e1030819040c8076031f1100081c107a2107071094520400900e8081c0450f54070f8010240c481e008140021680513003109008994100000b02138407010740603000a07c3d120b1660704d65a400c3c948107441207400303600596031700c0c103501d07400140950440c3e0710305103900700c1556101d800f20b00b035008404461058010460788040030350390200200c13132200d003d440d2081d08465541421000c8a1038008044009001800010058640360b40401d500110182010501403100000502c0c82e408204c0400e40256a40c00180705002d031417907400d60b0107880180101015181c8440c80300703034070780140305480741d50f6000144400740ea21003429800c2010140841070188000703884640014020441c0061600d070703d000b01c217002101041c020b4034100d4102030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 151867311 1250 151866061 151866101
    0x6151205030d02070c050904050618030c030f030405010905061008150f070c0303110f07060501050a03050c061615242106110f130929031005090c0310 66
    0x404101c0c00f03034024080569040040050000c3c10340c8440b000789100e1031066000d820305241ca00b0300800741c10b990b030008420b240d1080c801c01601010010403540030307200302d800d425200d5030f551520340d015280300100106240548014071400350303440081001915000c1c4140c5100301d00c544030118052804030340c40314003542c100020940302c0340160880009107000703240c0401c002d06801c003500303c16480b0040b650003021001945509025140c03160718050b1004035211a0754929503120540d0b6030f8032801d10a840780800141c1d40444c075070180c400c1c00b00c15038404120110a14094074950003072001c1040c4070707143d11380c40c0064400c59810343c90b8032060354079003000054950009071020b07845001000040700e07865a5044100c40000768040540308a5000001d555a941c3d06c80c0d121503048026644001082810701140c10344a4116010f206030102000c08220840748245000078a440708100083c0b0300070b0700c3e00045c080641804180d40c4180e6405808403030111800c904100c0844468039841050300c078243d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 151868561 1250 151867311 151867327
    0xd1b0503100b210106121107050604060b19080d200a12050d0906020a0e030a03270e13111002030403120908030c100f060b07030f110a0615120503 64
    0x501c003620581c424680c0c002d5154490700d0491010401c282c2000c0081840400c0c0306c4000b031841c1c000c2c0103020b08501c11003410814240d035499036915002c0c03c0141170a889401e2140140c4510b89500c40c3c1505040316945400e0341c1d81c0b41c0c1601d42003011416800203280d1307001c074007414804504641180424030b0003000b4140040d1a02e508c030f13060600c0d800c002c203d020440000d9609442c080c9d5030149000303020042c0c1d9107080c140040c3c81e45140003134a50098108030030560100b600611480e14414581c2d803801d0f03c04100300325403441e003121900580c103a111800c0070b108003200725a800c4400c00340310740700340000ca00c80e140400c87c00304000d50a42005078010401440050034090904807070004c0c0e0b0805445940c0c454500324110b4115940c01c81c1254000000307030300c10001500031b40c0c215a4031064200201410001c80c05490321031690064184644c407489026082c0c030a444c0c11101030056015240920540d03d0480017074516a0300300b0307803103040990001ca020000091024800c1d42d1010080d4070345030708 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 151869811 1250 151868561 151868579
    0x190e0a1a0d030e0d0812070305010501080109180f141002090f010c0c030c031a0109050103020a03030503060f0a0b180f010c0b040f080a121a0f13110d1b050310 70
    0x80c60070220108080c0e0b440b00c80094030341c2c602149099200e0a62240c64204c0c0c025041701200000b0196801c15040800411440e608100c81c10305442d0455404185500ca2101a4550726907000e4000e1111041d504114240100300402d588100320000a89003000405401501a03006103050540e01c0401d41160258030f42c00790281030f00c601d1058000c035000300e031340e6103c0c1540032409900503104544092890300302d0981c00d0808501504515004005075411b54001c1910b030f82240c0002401e1080000108000c0da44801d503079010540001c1209100d07548500112995800c1804040101400d80c441140c0307501d042c85000d0100007041e5500c4040c03500740d44070024202806032081e207203c2901c140c4040820550300092106881503100c00c1356010000d402c0070101d9009000d4031040c00032070403503036410303940d04d41d5002996102194981c0250355851080c1004021865126644050005200326202000c0d040b50103500c1c2e541480d82864001401c050b0740f2448216401c121850b03448801307100100d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 151871061 1250 151869811 151869829
    0x18011509150e4f021b0607030501030c0b031f0b04080f030721090305030a0206010501090608240307080703120320030103061d060711100903020303011401030b190e0a1a 74
    0x4240c0d980c06400c42c500303c5841089074060740000522026502140312041c800300140c9820901c9071400b000150314645501a0380d0040d802015804074000001c20f98022a01080e030f03800220140750b40c80750390781c1c40f071140d88a81e015204400700780c02130044560700c00b0000b00599441c0c41d000012107858a40b0b070314500425490391170b489011f01000400110100e8010405044240410303001002e0a5042c07200160042e40150f100100300005842004200c41c181a106100305003c8400c2d910950444c9001074180246a000030300184030301000002802540940c1c06203140203910100300e0100079081c0fa007041e080c0070a900103206000c2004000151103507103c1540c0038403541d400b169010442060500302941592003100190400c9002492101e060050580307100099208001584695a0294681c001481103c3d10681241040b00da0b0341d0084c0c20100c0d601030000c0180e040303854500c41d0740c01400310034050800320060041c0001c02c905414400c0c0307075031101e0382c68002107040e8804040010b041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 151872311 1250 151871061 151871179
    0x1602041805030f040f0f0b180a05130f0f0c14070c0906031103010b0102030a09270516120c09050d030306030501050a09050c18011509150e 61
    0xc003100d0620408144144060040d2000300c0048942d00c40c03030500414504c8036150040074801b07540000030040c2c0740030641143e0314a40070568105581c141c06000442ca240640c0c0030303540110580030588402c500c2c43c2c1c0701e4541030b009000200442c0c400d0001c45030485400f00340c420f0201c1c0400350400740714405c10000c3d01c8198410301c07181c104243c030707803d542c0c9c00d541c03803071340221408110450391203010702c0e003802178034505030b0207200440c20308000d554000d04860141c07050b03c012110200099050103005034100550b545c0702c1000740312038203201144680051101001d1400104100007c154a40d00c500441070403800c2c80d903841202c281080c0402c0454100080c045050607501c40713002000620a02405200d810007050010b04c0d042c2500304903080071000d088042c4074881661246d20002d2005050506458402180805d5000c01d02c000751291540f6070018104032040350307a1400b041d90300ca51100c801030000c1d0744035126001410710a88190481400d0551410000700488990901c08203825183c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 151873561 1250 151872311 151872341
    0xa0c05010608100b12150604020f0408061501140901080103030e030c10021b040b0a0303050702031f0911120d1409040f0506010315061b031e0c0506010803160204 71
    0x46589088692812100746030352110f65465504c440c00c01d1401c45a0030306822a540050841c000d0701d10101540c540e07000f414144602d60201d5000c03900c400c4030b0280d40241002c46d003111000c0c2442024503007595041820540094a040c20881c801840c41042e101c48000c117855051040e405e543c0c05031200c1c8006c010031a010b01c50040f0490069484510304000e59180390040e001c0550a844141d007801d4079602800e000310f092000c00952900c40003481c600300c079010301e00030f525203206100090800445020460351000301c160401031a07080c0b90712004069118840d04401e40300c884c0e003404150040415a15081d03008000700020b058052101c0c40c11540202c078440f441e00040034000f804a0b00110701c3d40d416141d5400410003296090321510350084200091108854982800148000c252201e109801c0c40380c41155001c041c01810b00d0914034400050701444099080801041005021401d0315580703d0f10000050030380004c01165464498692182c080030016000c1c000a80020035a00b008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 151874811 1250 151873561 151873571
    0x30806010c061b120c020a030903020f04110403060209101d090403210b040b06040506031b09040207080d050604020301120201141315090504050f010603230711011803050a0c0501 78
    0x3040c9000803d220711007000d07455104001c1d4080d60703804112200c080d0341000f0340d40a03042080c00300350030404100c122030b0f04403550400000400c000c940078001e071440820900d100461702008000765038014240317824040e00c00c0c0c0b403daa8254411a0341d000784515480284c00025081081420840d00481d03010b402800c7c00c650442000303c00c203900021510210041a546802015852a060082000d1000200c48450070181403000207081032102804082071001100249410545140203450130100002e204548400f420300b4414082e5000c410815122850b0130009000740c9054400ea80c16a41c2c0700e4433100d20050b1a900640350683c1240300c0d04800b040620404003030440054a044c081c7c00c80102e503002204110001501c4401c09030000d03489035040c07108211503054424142d230304440581c50041840000a502c4081342401201c0c489102c2400c98104881541c010f40342c030b141e510310540200030403500746400700003600c3d41c614000c0010b8010028914101d2181080044945c050000003035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 151876061 1250 151874811 151874831
    0x3020922080c0d02150c1b010b0a0605030402090604060807090b0d0b0412020607020312070507022403100b0c0606040c050c011416020f0c01030e0a1a09010605010507030806010c06 79
    0x24150012400d40000e98081a04070f21119810b00c07401500303240e840711403000c42c2005151603486014407100300c0f0361442d03181c1c04011107520035000f540c00160b019103940c2030f5648512000308594002c480590140040310082582420980f140104407808030300039203101800c00c050303900605503500a041c0d0024944440402290300e40b150180980d1003803e019610200800c0042c3c20000020502d030203540040c0940b80203013000c140826405001c52034840d0362103000788002000340c1200c1401c844c0c11422051000c00840c4e91000950040031030002454210b0394484d0700700e0541c418018800100c1d00010082151390a081e04007035501d03010f9040050410310741488081c2110b44038428a00102e481c81c06008400c42180805d444e0790380380d440580360b000d81c208151680d0f5110440d0450400d903503000c19500c40c007418495187c1840d880740c004111090000034030f00600b00c09644280b155460600c001078998000c1c81111840c81e03054903191000c1d6105401074542a51400c0213550003511884000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 151877311 1250 151876061 151876073
    0x20a030915021f020d0b03030a0507021c06050405010b0307170709020702060702130b150c0d0c0215130302180712020f040f0b0d0b0f030307061d0d050c0f0703020922 73
    0x448070300204a0058031048030880c1d1700150f5030511300036030284d041080f058602c1503011040b900c3c06038068030340e01100201c1c00d0f0a00c6130f0141c80c02000e030650b8a804280410000b06400c034005900e0110b040300c030340a8848103149040690302c0b012162a07403000741d00300511410344e0017510032103000404e042e00b0b00302c464004c13070034281001d210903600d160307564036190319803416aa220b1404100b102501e828881c00c4c0710015550512910300f0f0707081c400440d08400455880c400449076000035010031079158a203442400001c80e03990b01040381304a064403107001b440200d03045800e105051958070b082c60381d101204040002e41c0092066800d2083c100400700d100c25500c29010010507440098942d111401e5644408940130105054407030340500102d500e155600105850901e50803180c005040b80f000d5074010440e4158136041c114a000b05554007051603000000781c60031402c40c20640b040380502801c09074a42901d4040254001410408558000c04920b20380c600c2001d10040303000101140d460308 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 151878561 1250 151877311 151877353
    0x14030d06061101050106031a040506040e01060f0512010504050601121401050408030406050f010b22080708031e0906040b221811090d02010f09120819020a03091502 72
    0x2800108003030aa03100c2e003001c024800d15004005900e0308000e41d00d40e52202002302c40d8211000c6220b19152400700724141d07585e5005106201c03080008012840ea0703078204c0c4050309603e114451044550306840e0310700c40018018a8131640d80300028103041ea081200f091080e004400c0162408408000805000c2d0380911480c0d00941c0101011616442d1601e090015200010120780c84044141c004120001058040d14882c080d0a981c0f4503000c042210305100c0016103034441502485919030000d10b0400100081c02500001002d108111440c0081c1c0341e042d21541a0b450b41055041104000c00c141041c05805285000404410161560280c0d152110815001849500060703201d02002d075070b29210301c2c900b005010841505000c1518001404c9054025020f418016030904290009111b854543c1c040c00ea1050450304007a803909042e091034210100312441c2d0101c44030b0604a0900000b001c001c2182c0c0741d547c2e090a641840d114640806c05040c0d04010b5104002445485c01034000503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 151879811 1250 151878561 151878569
    0x601030303050f0112021f0c081b0f070303140d110d060609060c03020304090b030309030a0b19050112020112111c110f0304081c020304080304020117060d14030d06 72
    0x404075a03810200404071410070180c1c030020035912603180410060f1030300b066011140f800620603c0038261f8051081d200508840b00003403030194000349440d040850703908a00d40c118400d008070703425000300041080d80d81d40c00c0d02029004c0342032110040c0302e6190b100b00070912440030981c081401e08056081810345d03005109035511b81174a03100f00380b0442e80d000002e90000c00c5a4506103a0030130315078901944031b10503805501a61900c035000c802842d141001150b040403000340840b6054072075418017540c000720982c2d07014600902c01401c0d23520043c03240603150503140c0364445001100c02960054034540001301c8680705150b180c020840340381e94240c01602e80800003440311800304201c4500c030400c541a95502041c0da00042c081c0c034000c0b82184c800d0346d6010fa401201c5541d86c1d4802085040c2056503c807075641c481c2d000100300010401001c0240d4082c0e4800c0e00e4070a40c11810b07072821381000b0021100d064102800c02400c0e008a14031008070701c0383c1100c400035245820441c1e82403a007518241d0308 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 151881061 1250 151879811 151879817
    0x30f040f02030a150c1101051b0d1104060207030303050c030601080a0b040b0301110417010204290408061503151b0a0314070c1406060f0d110a1806050108090705190806010303 77
    0x1015a140300d410100041b14403102100800c22890b28094442d02c0c4500388002d80540e12010481da400e20240c0d40c444c0400c1800000e69984440c1d40d14002981c40c03429000c22400a07081c1004141c034100e41c031080d28080c0c8030503140c88210740d0300d007528800109080c0e904264807035180c00f44100103407402c0c0b0030381c149442c54420107596142060f070044500200080f032021241c0c03041204002103181105440d1f0324000e04403c400503d83d00400c128094000c43d04408010700411007440101c0f003440d034161004007015070540d03108021200341381400040c03c80740e0484031480404c0c070018214508000302074042c1c0c030b07040009003451000802d0060703400464506000c501503400c50014008110003d0201c5c034540c600508051600d01d012841040320103409902074116601a9010801000c80700322450601500262445a039001c00c00b0005030154106a0104d180460204080d407003a246c45100380407110003400311a25040c1440002e00100d189040c24072046c040115240600b400880d008502a903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 151882311 1250 151881061 151881071
    0x618070f021b0a0605030c040f081605040e0a0303200d0b0a1205030a0c140609011e060509010b13080a0c0501180302031507030b031e010501050105030f040f02030a15 73
    0x16034042c0c50700c084562201d8440245204118880d524058044107403031480c5440d544075201c1000074500340c01640c22442c2c803c6038040380882c84103000140180380d40150b00c880c591140d80d40b01400110340320640f241c101e80c0c0042041101083c0607400c00394104a01c0ca0107805900d0f01c00012000c07540182040001d11038450a17101d0300c6103001d041142c040d111100d4186500c207510340e1400e590b48140400ca90501c240c01a5410a216600b041c8100050300b06040d9041440c00426040c001c10400c813610a80d000c001059007606032242c0301c1c140c2501c902410003201d80c0d08000c5185040c0c0c110060807003407060030b1030011895602c00d003c2144510b110f2521941c515043c0800500014202003132402990000074003000507075000074600c0c0100f0701000071040c150701c1d500d86c214040c0c030745510319942600c200746d030b00f03e04040c8a260080321031850070000c2155036240c0004480d184030a4a10384002d25480b0003050206010191101140e0b100030101d51004625580c0c001d12103000c40170700d00340c5540c1d44c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 151883561 1250 151882311 151882337
    0x90d14160c051806031011090909060708010807061d03010b0a0f03060b15160609021002030706053603040e0c0a0e0301090c1e0b07050f10090c0509061807 68
    0x10308250b41050b03c01600300649060400f084d07454070a5901407283c6034032400500c00e581c079220b0842d103001c00064100042c6103406100c0c20f82c3c91905031901e00024444200000c2c1980340481c0020030fa40c01a6075030a075207040d06115004c0c000392844a1a81950790707016210103a50703591038400052000303104d0340d0310032460340c100a4221145000b0700d600424501c0003165810079000100e602410184410f894003014a0410310020541c840000390040e03aa4245040c503039030000050007805120383c07000c0c0616a40c440402007407440c148010080141c0070414000802604240821042030f214100d03802c10355280e00c11400880281e450b442510400a900c0301c156074031401119200100350001c0c0400242c0303580d9101d81507000e02c030b107030210082c0c1501450f4a41400006000510042c0d83e52030b15034610303042141e102c40401075041910300c00e030f91420701e601e1107d0040d080c00580104104540034909000e12210030340c01401d05a0100c15210050813400020300310a000310542d0752001503480003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 151884811 1250 151883561 151883569
    0x1f091508240403030504060b041a0406060c0206040b0708190512130b0402090606040308120604051e1603020412030309050c040608120a050c060103030305160503090d14160c05 77
    0xd9040c189a81100355075901e40404070006905070000c0e81498001981d58450410100402411417001e0b4000e00b8080c0481c0c05181030380038610141d204407402c000c11a5100c0050781c00c0803c0300c0000750400403e10040011003450000b070499540102801c40c503314087c4205501402c11112170408240c000c03c40c0000000701c0c81c80da9600c0000309401c140c1600c0c66071a414482400180002d00c0f80b03c9410004000da00c404098078021a03120b84280e803100000355242d1000501207a102d8003c61030b01c000034080310480352124022541648400d031441d1200e0404520300d04808813072006042e000c102c0080c60a50300d401104c1c0c10360003590001121301c0b080c58203d040020b007807859841641022000d008040d40440c0c4000070492903c070036551100c0c0c003070099a150044601d0b120150090350000800e05800d40c200e42d1040e60764080044481d118020142d50900007030700c0e003520b81e41c440c4040e40754150003020510000f00310880d860b4100350740c0c00e0345006e0008580d00d00b10382c10b0400e17200801190030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 151886061 1250 151884811 151884823
    0x30c060117060a0c03061503020324060703031a090a02031f05030309090402040f0504050715031406010815090114030709140c03070e0901060306031401050405061f091508 75
    0x310714492182030040d180c42059903001e001d0124140c45548051500202c0d000c2e42c4001c1c000d007250203091400300c62240018000b9081107421130400c81d03400120340e1801c5d40c1120103d0b100b13000200300720b0602c0440d4504800801640111080201016000351100e940341001d56100d40b19400001d07a4030b251406041003150144030000004d9030340510107020948c0c1c00701c00c1e41d402440554034070220355994000100901441d9500d6208585030900340010b0000c0800c0103030a490342d01d11642042c54030381404808442d0741e078549524190042002c60f106600c02d101036a009042c40c03041c10900d404000004192950a030300864030020b072141220031508043c04820014051041c0030060074480c0d54020030b0032103000b01a20010369000000403c49030080c46103410780600542030418660311000081d0081c07145010545a040c18540180b116240502806208552020260405454100d01d09404500c0c0d0205407a16590014011074002d41a01c00c00c2d00d2801c0844412189074508000541041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 151887311 1250 151886061 151886069
    0x61805090d0c050709200a051b060105010519020c031507030605091003110d050d081005060711090c0702120d0e010518010509180a090201120204080a06020708090a08030c0601 77
    0x700b002c1d201e0010400c0420b80b001103030421030000c680c0500a68114100e00c00180c41c4508080e00816940503085c2e01501034003110766001c03080926011110403866484400344076050008204000c100c1040001c0700f46040703104d040d401207c505c12000d90000f42800b05150003006120181c7d4204812640e240c01414001c2400703603111400f505200c401402e464103580400b5180f000c1815840407580c0390600d0306103a01da0040141c5580903031004c40105210002d50fa828000f5035102d1000c5054640903080302d044c80c0e403190010140b50365500901c081c10034020040300d6200b4042c0650009178407020f103082c000c01940d45c0076100c0d249075590003a000c095003151107410440107002da8401c1944034402d088413020242041d50b1214072140000c0d0403410a4080207121482603001d01a40480c5a04a100c1040c403d1702e03a50401c03101c4c00d170000300b2405188945030969101c1c40242010440382c1d0b0080404a0140c2c04062900b46458042580d106040d07014001c00e0740b00061240842905200a6004d8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 151888561 1250 151887311 151887317
    0x6020720010c15050907030206040308030405010506090c0a0f030b120a06050703090f030c02060f1c0b060a0215060406080a050f0f16031e0b0a090611160b0a061805090d 74
    0x94801c1e4407521589604003000c000400d079180c0c08116880810030246d402145d000304000d44c0e0382d0b26454090416041540c00715102d60805c4040b0f030051920415503803058400c01c440c0303424200c01c2d0200b200d0b880584a2940309241c1d4483c2c8035040c0340c0701ca161508120601800804000e40309141900031600300809960070149095070200028203a0002e801c04107400d442d10a0000d40b003800000d20790b204905400c049280002082c0380700030090404c1c07010035600800c04100b43d44a80052109034424054524016048010b5802c00d290200d115207400c034001410000e411390301c1e040c041d4608035200070b080e581035028940ca05100d910400c1202401c21030782c001343c40b016123142d50b6802d4031065404010115400030751051400c2c0034440e5911480c03a080800c0c06454142544140c0c01040c06040030b403912828010148510044030089801038219041d6000c20b0f078205440c0c0d041c54a0340540348465460302c4d08000212480610319184500074078010008941c140104a6883d20111680b0320046c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 151889811 1250 151888561 151888577
    0x901050408070803100509070c030f022d16030501090210091401030e03070209040b1518070c17030c0a09122a0503060103050f0f0f0c04090206070602072001 69
    0x25110106a4030780036800801981c517038841c5180c0c80209503860b007003030750010340420400c04100d07400b5010586060003038591950304013040c030049885032140d00c51312440600f140d410010750180010780183e5800800f0540343c00070b151220100900c1d42175031040e80c11303039115208082989000c55008050190701d05040040700d2601c52011895041d42c0034550525960711074250290354280704840c2d01580c0206500e04501e4149445404200251880500c0c049103480b15080c504040d644a8001c1113081000c0b51640d40d144030481d9242081c004c200d031901005843c0060000c010000355006410b03d40910761100e035011001071050032070754451900407881c482c050000c030b20034035903000030700640d410006072100b010f4000d981d1010241d8023080e058841c0c10700003c28000085030301c1482605007015207102001501e2140d07910420b410190301c017a000302d042c1580e03502c0c0980c0418507040c030213000d940c02c05105445003400ca81044000381c81000303140c00c001c8568040e00b40d0801890009007000300d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 151891061 1250 151889811 151889813
    0xc0c06210a090b1e150306040f08042301020c01090b070f0c080307080405030606030d14071b0603020c0c0402041802090616080a0201060f14060a1707020d0809010504 73
    0x4440004545111031a400d140801e00a070300d1070700102000c68000702e16100a0900758038003a40740e0041229210001d4080010508081610b10319082100c4024000d000b140c50f2902d82c0202c1a08048084aa90404001c00030350300c840300b680c400420100013034101f1064019030000e401e08c010101914100240c00a061103041c0c0d83d82c0640d940b245d00704ca81c00048101038034100702d2400b40d0b82c0118090707210204640081214400007070096030401c1d01610050740354030061641d2068014040000704150514000803c480000a0040c00c1e002d601d0050b41b9041c280c170000000c06054006400181e000100303c0c1c4155030400940920101c1075400b1480d1906d42455411005580d0f19203c101e0703a00020070f1503042d40d0700c00643e00c40c8001003c140c0d12060742441c0c02c0f181c81e80b16000207030140d428001c0c0015001c10000c1c1000c1152030082c03c0c013145040304420414141c0c03001a44106000c03105203034919610a03040001c2c840d01480e001814a0b141810011304110002029400c0c940e0401c02004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 151892311 1250 151891061 151891087
    0x8400803040b0409022b02040503071d0f04060b1c0b13030f0e040e120909100f05300708010e070f120515071d03030309060601050307020c060309030c0c06 68
    0x190440301151001a200e00134444400f44800e840742c2d00d00d40b00e4141c4070005501c0300c071b1035000307104481c1d08500b21294140d65500d603101e11000d01d0019510810b444000030341104031501c4450f4401d07c540300c005100c1041c18000b81810030300c00340c0154078224800b40801081150780f02c4e00e4000c007a24001182c019500d035801841301030000140c80812404410004650300c442d00449001400e941c151228000311500d0383c601d44d00042000b030322170135641c030105111848040051040d83c0c005d4045804150034038041c0012064004403900c001100400c100c04821b180109642c0d0124058003c0c000c141d1810501c0e43c00d642d50300c0f00d100c1003500706140402203100c3c400c040c0780480e94050325004610841d400c00c07904000f1340d0400303800301c5551402000805540002c0182c0000c03101c0007076003055601e000c2030564a00084961003200d5000750040f600d03d44c0103034040e580c0182c06104650900c5940b40108030305800540c5e40240e50ba10101d05081d03060414411402a640c00b41c800c1410301c800020a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 151893561 1250 151892311 151892317
    0x80c16020f01050d0e0c010e101409060403060903021c050a0e0906040603080a02010504020a0e0720010204050a08010b03250608041b06051207050405060708400803040b 74
    0x203100e002091018882030340184161002d01c2461002000081184017905845010031410345000901c00e00c030101081c9044890901010210766601d00c0d52031a08820f80703010f90010004651140c01032000200180c418052103e503948242e000e007041403079000403034140c0a030081d01c2c602489000d010072840c03158400c1d402d042140e82101c03071651903111140031900030b104541024249500c00036007a0039443c2c0542050340140d10940d500425240c0d540010f00481c4000c0e9000d00028520030440042c040c00c02428180d04180032000503c0c20355601c000510071225984162140e0f5101d01c01000369290a02816141079180a41c2c10440110b00d402e41103441c42a0141005001905010070140000c0810007003820313410000e540c0200741c0710b09000d0000e070031030022075070aa440240040c121511039010382d41202d00c003610381402e00e080c56071000c0e000c1e045031054880080c998a00320004900c44031801c40c1040e8031282103120a0032051040700030581c503401c034001e942e004110801c1460103e60407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 151894811 1250 151893561 151893563
    0x605030d030207060905030a020a0507050a0e0a05060a05190914040b04080c030c1902030d0201110d090503090303041409010f03020f12010e070608011d040807030c031b0b0106080c16 80
    0x50f50744519250800051480b60300280c194071000c508464016000150342d62403c2c0180d0889481e141c1d103d0421070200010301400700003024460204106807581d400594101400a0000000c10b880c0d20204136160310b40313051400d0300220510100316101c1140f08400003c500c222804d5082d281584402075481005440181700a200103409404041d00b0300c1a5a08440d214055410106101107015092600882d050784240188201180214014400c4200c00828032400c03600308240790b004100204144402514940004c201c4600e2641d0140000c1001e40504048100c0240042d03050100083c03058001003003055a2040900144c0c3d0340c0b403070a00c102e0000300c035111550b034403120585001d05610680402c6610854002041a9030852400c0e8103071007181c0039494200341d44400440c880384c0107480c040d0041c0020803220001c41d1081000400c01c13802030820305241c0c160008959405001c0f95001d0304d908085000501c17480f6031003420316401561640d802802d01d09a180000e40004802030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 151896061 1250 151894811 151894817
    0x3e0306010c0201140c0303070f02010c09140103090c0e0a0b090709180612110405091902091806011203090b030708060f030705030d0305010306060812030115030f02070609060f0605030d 81
    0xd00e421613102e05040c4000d42c21000000340c03158404181283e407a0015211300c404500f41e58403000d001c81c414860342024440964400c0c02e0249412040c805030301011101a041548a488501c04120901c10910042020401c1c80701c0d207190801d01141103542004126104100340e1051080d001d0340903076440300790755206c3c0540c2d40d420300309402c040050849030b026800e01d540030410107062045e05241500341c030b102aa0709000301d6913540b0100d900c419002c51840c84c003002103e0140c0c05410210400ca900800344400c0b14805c5034220880761500000340d110103e000005000c45040590000741c240041088424590460034200e4014000d101e000304514004c05045000c7c1495580401a40740100300143c2a9007400c0030a03203000300501400d0100b502c0f51810100d002841140000c1c00070600c0d08001d21903400c40c1d090200071100d02880c0b5030000209901c601e0011203503039240c4010800a817148a00140c2c0c14018074150701503c002c4843c0b0704844c0d10723029041006440100750240010540c0c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 151897311 1250 151896061 151896077
    0xf0207051506100f1206091107020108060303162003010504050708100209060904020c10020a0509030106080a03020a0312110301060305010303110619110f04121e1a0c07063e030601 79
    0x207185c000034004c07540325202450522009a01c02d180760001040d01ca8000c2c0d843c0c9180d680c541d418166280b0942d541035851500303030307107044001c40c152021061014481c210400e0035100c0e00310000303007500d5054900303945a800114040284440800082010003000b1005508004d400d0b000545240910554140115000030b26200c07041d01c01d10800e4040c1840307440c21500c4130b158840080c41c0d42c114840442c0290700c5c2c5a40410b0070400041c002c940c05900d90700411020841356011030b40780801282078001030780c0300c810112002c10900e010310b0207000c4559001400e903141d401c000f0612101c08440303242980280044c010400e88011880c08030095000300451aa0306030015000d00380304070b0149040e84900818040380d0050f0f90f00b01c00e0541030140c6844503401142e0304204d2106074005000400648850030140000440b4080c4607600030340c09520b190804140e43c4421065600680c24901c041c4018103103210605207140310745042e20405a88006040d02069201c1d105120107011641801130302 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 151898561 1250 151897311 151897337
    0x60f0e09040f210210111602011110050403180501180e101806060e181b0c100605010807050703021522030207050406060804050d03050a0f0207051506100f 68
    0x280c0e074101820701c0c000400741c10b03001e044a03009450301d17040c4c0580f00e1864208141401c840a4542c2075404281200407180d86c8082c144c5e00550b0764195410b205e0440740200c850161644a20f031241500c01d6000e62100302c0420310103501075016001d40c1d00000d06002c0c401c0ca0f21403503040511998820b80b004565000f07120b4035a40b1200c039000000d82d220141400d2201800301402002c0d400160840300b6036266a5032021558082240c20280ca1882d0040c0741d0000c40000d10b503041c4407602070420b605c03011546181c480382c46445c506160402d850550341a03150b9004002559018011650090030341c41c1c2541007011a54009403901d080050001c1c2004803600881c904d07c0421520008040780a005040302e00d05c40d01e006074031400343d07100700c61055113044e8000490702c0c001d4040171701ca20341c00b80103002590036a6905a0050a01502c0c0d0703450f0a0365030703401080c81406480180709503401a0000c110b00c7c0325008614001c0c910051100e0700548c221299891000d405c8112010303202c1c81800c20406139180 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 151899811 1250 151898561 151898573
    0x207031109012111041109030f01050c0a0e040b0d140c0103020306030c0d020a0815041407060522030b01171b06190c02030109080913090804060f030608010c020601060f0e09040f 78
    0x70303135030660f6445031030065111024081c82c0010405038806600396020b03500105502d0303080b5230044516051a800400500e1101445000a9102150001c2001482413658808950340d007130707921821542e2940100000340b54410801254052104c240b0302945186040800310f5200d0369402041405240d84da110001195160791001d00035048034005c44c1c1c500c040c2040c1070348501030705071000e6842c21000070f0311510083c0702050280a9441984070b017450800c0a13804171501001410f0780354003025200d200400092000c03220795000f4004c2035800c0c051070030020741460800b01e4980808940c05050407072200207445403029940c01c025400e00c200c90110349424241c55107030b610b04c402075165182088101c200610310300546840e40060701c0082180410703a15010495001e0200548900000d000c01c010142c814440080301d05260b00e400326005a8440082c0e081d180785042c00382c0035801c0040184170703803a8840c56009168000d071400d1119060a0f40100b2544c8001800103400c10510901200507c40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 151901061 1250 151899811 151899833
    0xc06050c0307020d0f031b0b040b0a0b0a06020309030106050d0c050405061f02010f05060d020a1a0708040b0403020f0a15080705120f04050c0d0b06120a02090702070311090121 77
    0x20f0007524402007500a843c040703200b500c181e54118042001074807404c9031700c200145030b5068658040e1450a4a880b180c984245400004080b40070803074803411014003d40b108020301d001050241c00079600c628580342094207490b099080a030246550b940102e0115000725a50b800702e0308207640005682d1510008611003c00142c6004580e00003c41c1000d602ca41c154000103580c00041c3d41000316484100030429840720361807000c0d610403030895050004d649090350440c06214001a96881c04515981e481c03c5030300550310020481102050800640c20038038905508001c04036944600c0d1800c0608400103106810392900400c10500006102507004800b11080031203041807010761486c2c142020216400c0c105da0889441c0100c00300c0245908100d18070b80d9403280d00800102e03180d9554824040a0207410114041a2007200707103000160311050504c41c090030650740035040c010b095041a0601e058080406802030301e05000401840d8002a031480854a41e9040d68249064504062001c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 151902311 1250 151901061 151901063
    0xf1a100c0503030c0d0f0203010e0f0919080c0c0a0312030c03110309030a02250603091b081501080a020109031b0302060d0603140d0e0d030201020c06070c1e0c06050c0307 75
    0x312000080c4181070869801409180e170031a9020f02c8281c000d4610780d0180c0c0000e02c40d031000040a0340119120800b18414241d10103c2c841c202c44114107030304260010342e10500d000340d442c1803001900d00c0c0403042c248002c00d2030f00303000e6030213041d21031962303940b1030304002e4401c2031034100b55440600310221403003500894003284524548039168182801159203c0d807026840c90054403944c00b0805010705041d00f8029400501e0303524035506468041e0640140c503090404644000030450b0748811002d040c0d04642c05881c81d036005240225420000148004041e00198141da01021180d80140c0e80808010141c2ea80004201c1102403c07110141c001e40503500001d500a00100b03001c0c803d18503603840f08048034040c01030540b202c00715103075250f110455066107c0000b41e0010242242c3e042150724007001b644240300040c5020740d00203041d07042c848150b48010020b08009010701c14007420304030700550104d816021007000100307642ca80c03d0b44c1040e0b118402c103010001c18412903110341401521320013 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 151903561 1250 151902311 151902313
    0x71103040311040b0108010605040b0903030d020a05130f0302100f020115141e090a1d030d09032601090507020114040b040b0907080c15090d0b06040f1a100c05 70
    0x18a45919121106480340300c0d041e4003c03854003800201640c410080c8034100d8220b500d0782c0f450300c0e003000310300c651300d51180703c90341e815100401c0b00c0b0342c0c00302543c070041100b84080c0d80d80c0e64858010b031100640500312580010f60f04404000d080c405070f5118240c004103451720f42003807206501c0700c2000780d014081000030440364031042c030380004018030340c42c0d08101e42c01011030b038140004000d400b001c07201540b40030385103800c6005400054412046603101c0d0000c0c54070704400c4120071040281061455000b40000317506540c44104080c00c040c1c00021040310380f054150011a018002c2c032100500c003d051040161040d151008031384071a000794800039141c04c8542002d0064a4181024200c005082d20111503400f92500091030314000461000e06407580031001d4140383d4900d00800140341c1c001f0030325000da40002c000304401c0b40d9030040b00303e1100d0b109070342600c06450b00b00101700460306070f40b00c0000c105080040380300504e04071640410f0f281104a404455946038440f0489000384503410003465 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 151904811 1250 151903561 151903567
    0x10020711030d02010606020105010f06090e09011104081005060d110d08090d0302010231030f02180106080403020c0a21050715110c060430050d0513090b030312071103 73
    0x40d80c3c190040000c1c1c030602c0c1c0003800075990300e007844e142031203ca00c250400110800b00512418072034061560f0000120340c008108544034021044c80c07580141c0c0860745a034096000c140d42c07a0554001e540d40041d00300c1c0c150400562035100d241811003444500342c8200b0744c107040c0720100007911094a501c01409030501e481c940e828030b03019000b54031507508008070401242c204041840b40304540c8070f01584c114006044140341d40e0382e4080941d1444000c0f40d000101c0d0500e84055100362010314020180c69695074070b03505103410302a090003000f101b0ba80c000c904282007400a407980840b0b4040207014642100388030340f4207081c0309060603455040717566a481c2226003e070303c03e80d101c25088580c2d04a44c0685824000b00c03400c22100f80f051744502d484820200c185516241c00c02c840b0a40100c10b402c004000120450340d44c141402c0039410a100030a0000c03030001100c103c0b000394100600146001006003108041c0002c0d500d01940400312000b0740ba0702c0005d280a0310450f080116030b1410422262 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 151906061 1250 151904811 151904833
    0xc050403120504120b2707061836020d02040e0f06030615041407020606090702060108070509151513050f0a210b04030e09070f090308220e04050d020f1002071103 71
    0xc0c4602c014420100000c1544c0380507107500b0300010240d070481c0c10541c003041c8212074031003000503210032b00d041c1da010600c4004080081c502003070004103100a00c44d000180d5070350074611031342c0702004058911460710610360304003c6180c50000700182c0003408d041d100080032030340d00d0000d40500b0058201c0d0f5001e0200d001840280c0c0e4000030091301501c01229400c106940b000012a80d80c9424801c98640340c0c4840800c02003428000285500088000084840344503074a022505c5031049800082c1d01d0180080c00304a0b806021803808041c2038100e9001140342070b4140003502d60919400b0ba40181c6005a01c0350b0710308000541254203565000c52512278501d42424041c203170850388203085004650000002e101c00c0d200b040c01459041030341e15880b02c1c0b41d0541d1036180707483e00480c00b0502c401198556080c03003120642c0c0d07100e00610003c4088400344c0f80c04d160490030320640c00d0459055510904019004100204882d000040144401611030b032050805070030744518243c0c170719058003a80c01404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 151907311 1250 151906061 151906063
    0xa0c0b04151404050d0201091d190605090f100312020d020d050405031536010c09030b010e060f04020d0203060a0509060f0112020d0c050403120504120b27 68
    0x3120007645146a00711000788080d104686500000c0c41d03081400c0105112030300e441500e080565006141030815182c841c40c0400d0848003185140d50100188002c02102060b044580031041c1c0c4251350a000780e6141c000800c400c1a00a84000c03c030005000000d51b0103035002c12108010340d008030710700e5103540907090040e4440618400100040c000e808540c210540070368112411914081d0052a804100d00c564070010381000d4203600c00d05070f9a04a81c00100007200041d040c05c900d9100e01e00c00d07075140a5815003111a0285145e0a02883d14001c0011456404051f41190302c03c3c4035101c0160355450002d845422100007299100d0300c0880c2010703442d5011b50141d07100712402d031164400d190f00ca500b000341c0c5150849507281c1c07000c100c18543c5400c2d4031610b0158102c811203c0b0150a149182001c0421340c0e42507050800041c40c08642002803100703d001003041c5189504089142038184201079039854006040034198000360404901c0c403200001c009005180d040314000c440c034101450b65 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 151908561 1250 151907311 151907317
    0x2030a21060b0a08131509031403150a0806090d08040311010510211502130914040302150c0315030c03070f091104050607030813080703030525090b0c0a0c0b 69
    0x5080050030035800030b00f1010714999560041e1b600118401c0c0156040c100d00780280c90385e510103d080010b054440300b5403040041c09103025420101c03098206069a0040c450402c0c030b2503202d640b01d54000c0007030100544001c900c228141c0201e151140300c17a41e540c2000d603440088007101d14440d42c6080104440c411030b81c00402c05485e11150041010201e450940a8100c030450000d0140d4001c1d01c04500803031f089900900840c98510390210b02140c0d110716860072101c0e02c00d440d40c01014000200410140d050080441c001307010080c100c280d00303104410074070f0717400018401180c20412004031f41c01641c04000c4041c0d00500242140c01d02a212182d9201c111400d208001d507480c28812810102103440041d40c0954901601e1641828500d407000c41c0d1516000e01942c1d0149545120f00000c51410402040f000c3c0c001d0b01c000c00c507400c103180c00207008541018004041100b80c0810201d4681c49140e841c111400c4c00c0700b50713840b511401e4a80d410000038400c001c0861004802c0068098025806 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 151909811 1250 151908561 151908577
    0x192c04110712032007051b030c0f01050d111303021005130b070201030f0f0f0e12160c0e090a0c0501090e07030f02091201090212010209090c030901141503010c020d02030a21060b 78
    0xd021040e203c0d48060507507500c1d8054129502c03205902b820403082d4880d41c00340004042200c00400c000300449440100c0d03900440d4481801c0440000500a5060103030900034444500d06d4841d1034029400384c610654883323401401554500040d0001c20340e03100c0d4001ea80c02c160290313030070130400d4043e1009800400455490401660601190800241c00071442c0e0144111203184a4a0003e90ba8140282c0701000241240c8042c0e445c1c0010844400e00700181d480780c5203110080410004504014180300750070f03400541080200c186c00d0101603180b012203908403805043c04159a0354404210000c0d00030500015040384980501100440054001c800003d009990566200d00e280030314600380e115141ca8290000343e901e001c01c01d412004002076602143c0380300000340c01003007503441e8000f038001519225660403009505181d140380070320580020304001d00080c00c0e803202505020b51039001d1210680c1c240a1001d09900d441420041000750804050008011040d19200d85081765003003100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 151911061 1250 151909811 151909843
    0x402070c091b032003130605091b09041101030507031b0e04061505030103020d140a0b06040f0b1507060905030406050a1107030503192c0411071203200705 68
    0x1c602c110480c06031150440084d0a03a06909421404078071030b140ea5403002d05801144011040c0c5a00800c01074401c050280c14100080c14400c100104a0b000c0d00001100032486002d41000303200010740458021008510217003008203ca0340e13448810307801040c40100c158080c1051600144550f64801c60700b4246503000c40382004001c0c2c5031401582c0d44040e800d55071000c10000c00060015190443c46920b91034030504034190020003070a4028144040400d003150304800d00001e0009914042c041c00c3c0340302100510801480c070000000a0ba00b11021618515029002820704280503145d003007016020f070401c0440c1c1d5650307a100401840d6602c400d2a000028040481c403000c1c1b0140818000d00303c1c0d40010080d418a5000020700e00c550358905400710a1214207070030b0021260302440720030010320ba02107a00e44800034070000d1100795201401c201500402c2000f0340ca0000700d0002008456628501d00051a0410105000b002d544004042045103401040307130350030010000380e03402d040d003d206 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 151912311 1250 151911061 151911101
    0x308010611060f18160b0403350904060b0f0c15040c23040903030e010b06090604090b03120d09050c0901030503070615120507080610080a080304020402070c09 70
    0x100050b121041558a40c050345a28400f00341c01050b881c81c002c0c0200148015240580101a07a6480e210800c1d0711501d61604085030400c01c3c01150181c0000401000381c0641002e107044400750081c10072003040215024020443c04000d880b40d62040014007500030050f40d0343c44a00084d4910781e041700f00e084080d032040d03180070301d50148080c2c0303160b008982c80f4000b16149810204410200b10081e0000d10100d10400d020b002c0d143e0701d5010301000759000780ca001480c65007501e400d03429990540c20f6203004440030000c0034015181e40c811942194151940080c540405100090800000b20f401404504010410802d080015032110203024498070407104403020382e401303001d1441003d1001400e150070501400c00410500d420280d0601650311545202e980c41b011820a4819130900c19115680041014003001c10204021500070309003441109072685091039240d615440d01c1c0000700001c202101080440d1503039010b440e005507200c4110441e05445043e2100140a01c1e6003580c0418400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 151913561 1250 151912311 151912337
    0x609020a08010902030c0d05010e0604060902190c02181e060117061e060f0c101104050d060f1107060c030506031011090d06060608011502060a0c0c02030a03080106 72
    0x520849034014200e4a9048582e0300e000b020000a410080449040c080704014400400754140302d041c0c0078140c2d0550a00380d0341040002c0c00200e031110307000413629610400c51803100036444084842d030200d13613117441c071a141e10902c041004038103c5035040e845c00710300c4014801c0a0041c07272005c450201c1841d000103c1c2b0754503000111030000410b003400c0c00d80c0786a50003181b03040c101001c507981805100500e02040188881c0800d215900403034050b00b550705c020a0800062809200e12824482110410701403080d482c203050b0700d5031007140714440c840c07088806298108040341d00701408000c00a0800c00040b4018024480c4a41c0142130488500380b812019111440c081e1140d41e008a901400401412040f484404002c244102185e40405002d00c8009455a103812031000c04610a2102284d1207145c410701516001040e080340c0c41e41c0d0701380c22100b1107141d4000340840d4400d008903004605104003840a8644607a000e1000c3d416000d890754010515812180f0b2030304032400f9560b12440341000b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 151914811 1250 151913561 151913579
    0x1403041805070c020411130605090f0d08121911040e0105041505090a0b030a06020c01200d020a050405100921080306130b030d0c0201090909031b08040807080c0406 72
    0x44602d940403c44252010b000b60038540e02a200007410021000e2509946080c41200584a0b070300000001c1e800048040f940d09046581c260154400e0343c021100040c141d1316080c840c0108614080d49094010008100004801e1034403a500b10250080011902220480005034494000ca12201d03214400004581c10244a00505450502c1c02c2480c0d0034100810440502000b405507082c60340c5501d540d180c103076814081a401c06210f907034016654481c41882c01d00b51844a40e044c0d88550040d8202d201d8032030420211107404500c81001691005101c00030b50f0a8010b035040135400c0145039034204a05900111030720151000751030201822011a11344100c512084d0b50018040c21041c400301e2001d00303080303c070304070101c440d08408a92310b5926004a80b4103001000f4000002c1c211541640655800400050103002c3c41601481a072410352070240828122031000e60ba00070500c15108240b01010f0251800b90203010161070030155113245035a0f0780c001c4e00000c14420703468010000780082d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 151916061 1250 151914811 151914821
    0x130b0408070609081b1f0801051215160c0c17070503010b01140d0f090f030806030303040b040209070c020a3b061003090203101a0102011a1c14030418 66
    0x621038000300074a801064113195003011050300b00d500404030200041034401c9490380c40120300a00c0e03541006540c50800ac0150401e02c900030030460340c0250700000081c01d00078400c0e03507110341c5000801c00342c0050b00c4011940070011020140042200c24400300d02803203042d14420754044240115180103446a0805007200c9150501c1d9002c50045a0300b5000c0040d0640034044842080700c001a101810b1907030b0406880300e4410480381d24088000c1c0c2000c0540150b20a600280180d004500314030702551400c0c0c50841c090400380c403030b520650003e041103110b040340e1440e031580648080000c560b100d02c5442c0e1000e480c0d044461055102400c0301034640b0169040c046040d6940c804c401a0302e603042442901040040414209034440400c41e0258400b0032240ca51240107602c002070540007036201082c000800c40c4114116410580401c5c4035685140340c011900c0001c65840d103086052041200c004448a81c0081c40240042c1c048000340001202800840320450130014560200105c40000c0f56 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 151917311 1250 151916061 151916069
    0x807060c0e0a090906020d0908070c0b0a0504090905100c05090f030604021e0d05030c070e0106080405100f020c06011211010804050304091d06040605060a050307030c090c0203130b0408070609 84
    0x442d51803000c1040d0140341d0421200b0502a1000610300307009a950b850940701844010380d10094001108001c010224403401d000308503103941c142c1841c0041000802e640700e588030340e843d1b894440500c83c09200040c84030203d4100c0c410360410415864407030140c800c0d0062003201d8800c0d1340010b40d8808604010901390700c107580c000c08480e1442881185c40714000c2c104440f054008004000d00c03000504108000c18200c03440c1d41c018103910f0715101e40c2c075407408016002003041002030000e00001840c0019000341c1c1c2d5410800102e410388062071401c0080c091041c2014103841510000245010744d80f1402c1465801a4581080b108035800103680048090b6001802603008020412501c10164044040c48440b0b0345900032400602041500e4280c050307509864003a51602400402d1500340743c6080200015005452601c5c59a158030390751003694461040150303259000101e405109008498a01410b04d01c003851154454001400c244c01a00070510f07284176401010a00c1d03400385580401f11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 151918561 1250 151917311 151917319
    0xb0115020d02030d0228021b060403050c0d170708070b0c070209040b1f090b120d020307060209040b1504090c05160206070c0807080102091e0604030305160f0807060c0e 74
    0x200d03407080c0d001c0e0000c4d81b0002e008134020f4410f1441d0540c43c04140118003c2204c1d9900400c0402d150380c10281500288440c100d218020800003000000c001040b40c13480e126003155030150faa141c6040000d08030304c4504442030781d4400001c1c40d81c10003035000c000e010703101d009095101050fa200d06001c00188640d09d006940715001c90000340002c2ca046502c81d5200800300d002c415000c50006030515a85165008640c0c036a07100d50260655040c824021980205c001005141c03103261280040c0d1640f00b4840040c2c0a5030b00081e00d2000c61f140c9402013181004007074413189010050110b0011a81c1041c0100d420a5003050725041d03503144175105503034580342d04a134104640c1486908028050340620000c845107003d012000440d03134030900a28008280b03441c0050383c1c500c5000100480641941c40754694a075100149250a803209c000352800e8030781c14103007190791f4200040da0b0515032411307001c014000071081080710200a886c4000e4043c1b0781c442c0b0000c0c0114007844400303481600319041b00302e0704 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 151919811 1250 151918561 151918567
    0x50a110a08030f0a0219091409060a060e0a05060408010501181109061602040c090f080604150209182d060f040506040b040905030c060c0f041503180b0115020d0203 72
    0x80404040403c1e40105059800503c1d048006e884031100350901040b090104030b06240c01c000140c40742802c0312103503d049400500c945000c00c000340d51510640241c00410034405071038485900c480b10701c40060074000303200a484959480380b46020b00310902880603000310503406048401083d0084814903c1d0000c0058105026542442016003144d18030354080e03079484a5000160311075114a0404503910b030b07941c00d030311410101c010440c4000b030ba00014080d0705c00c000b0400450103014800751301c404078510240e41c50541c5000142025402c401c01c0f0041090b0b041400764840002c0d10b00140700c41d54006200135070f00c00d802d800130b03840000c480717a64100301021070311581464298885075000c0707402840000c000f0720b401c01050443d00e0754441120b041e440005c05800403078007004080d0b4403038044c03404c4900c1c0c030580808040090041d40b19500c0c5404c10398600c020342038080c0e00403414484604103610808003090809411815013849a02c0030141c003041d4040b94644003261100540c095a0001c1d86 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 151921061 1250 151919811 151919821
    0xd23040b0307090b0c0105070806060901050409050c0f1308010606050c10110c032703030313030807170a020316020105090a02060c1203010b0a09091e0504030306050907050a110a0803 80
    0x1100e80d01c018804010043e0004020038515035400c041c0c60f108600701c0000410749003c1e000170b450000c01918161250034244004042c9030b034400300301c03015108400c2d40410703140c680202a00b03503070240030501d000110000c6203030800000010103c0040741c010b0070080c030425070340b140d0503501362044401c04003258126501074005155203401030103861800c061810b02d000c4115113080c0c2181c0120000c640074461050604001070350407450a56541011000386185041550030488900c501010040511646e0000620403070701074551002074905c134580014407490100c200f040254030444040c500c038412404500c24592051042c07620030403907007004010000381078081000303a0304415202561383c411103001c2012904402e0185000307100441000c0e480312400c00020f0040b04407a080a00a40e2030310b6480440384100e08a0419044d80c52507001400c3d4541c0d0404a0203021550451500305544900f80300342c03154842e00410b100480740c3e54001600510b4a040e0780c80d49850741c40502003a1092010503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 151922311 1250 151921061 151921079
    0xf14060c0d021501120209010b0a2d0201050a0203010b120702030706090f02031606050301050d11060406030501180207030203090108130605040503040f0602070f210c140901090c2007050307080d2304 87
    0x420052034600708070340e2020840c002200c03162490be81c0382041c50700711406c44c40343c55024051766400115050056080d0360500404400d58080d99405030305092690f00450320313450080c4101c80d80150064814040302c10743d07040400600394001412402482540c80d07810f08036601141c0741042d90700076600e41d4651391034107003000314a22507032505540c5178881a10155040d550040101300a00c601d803030200d02903250122100c0d4810040e400540102e00421400d00083c9d030210441d010b495003400c0040701d6846c0e00030014800302002500400140c9000240420300c20004040e001b01d0b03407500d95440d900c5071140022612200580f08002c8000c01814052020071032b43e10354020349030786822000390031410507240d51403000d207142d015105036000720a5107045030030038011445c00752841c100c0900103071194040080425042040301940099416511010f5400900402d4000d01c0014112160307280c590f20100d0316112500c1e844804100c0400310200100900c0340ba0390301c40d111602e0083d04007498180c01d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 151923561 1250 151922311 151922317
    0x50c0a0605060315040b010503160b0901080703020903160305010b0105040608010e060301020f0a0810060509030309010e030118110301050708061809100603050f010c02070f14060c0d021501120209010b 88
    0x201ea4540502e80e5a01c00741c400d10040c585c0b003035003e2800e4039001d5142405060800f40201d01003e01c1215400303080c803648481c01c003200c050013030030310f4006203a9460a000710000d004401940d40d240c0520b0180e4580c1020801c80041660f0180d4003c00165006a0064905110380d00c990000714440c58010401040074003010350b0b00c48400f400151400d11502c2d590402c2d40e000942a00100e4040020701c0145a40b0041c03980180c6494182103103480d0360680001e603280201840c090421890441001560702c0070b400c21008a800e8420a135546030252074900070390140090454025071808000501c12031065107018000d00c40074140810b032207801c00050b103c5401c024240c074603030311803002440b528003914402c0d0b000a6000c1c8001d80501200ca40b207003800e5519294006003150300204c0180117040000f075500302196a407002c1c2c3c121080e03412000c55554029003220044a0240403144202603401080b48a4089481500c1c65500d03a26030490030070200c05a540039401812741c40040c05000d0f50b280003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 151924811 1250 151923561 151923571
    0xf080d05090301020d0c0917030703053108010b040b0d03080105210d0807021614010c060e010501120c060906050304030305150909070f0b03040809010e0126040c0501050c0a0605 78
    0x15190850350390400301a5000544210000341f9071010030010703a281521139501c0d0180d40d4000d98038009041e00e0040c50750080f200d144419160110340180c3d07000380c00d0060712001484560300d121030399840448034002d00b15185c000340a1411b00030070780c04a1400d4418240404d9158a4240300341c2d0902080c8004c00c0d4842a964800c000d0024081804800c2081110060103c640c2d41c0e400c0d0b0324001000a04101e441555000300c204256030034410035010b204615410402032030140300700700031400d1100243c6420b000c642070382c0d40707440008500900041c540c6c996540c061400074501503500c080072110f60030b640c410840003d03402d0002c80c000903c41d41049130000c82405841d0034507000c80000424952055501c460550301680c4100051404c080700310004194500d0103c3c1546000d482d90760403407040d0210541009003180314035116030f008544c000e418801d0000d00c1443e04100310052020030b4825501620000820000010702e5841030080322070444011004e01035504072980c84002415000c3c00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 151926061 1250 151924811 151924813
    0x5040b0a1a21040b06270403050c030f0408030306040e0d050307081015030c1112030c13120f03022a12011d03070c0e0103020a061b020411030906010f080d050903 71
    0x40070791004a0640520b41c003480c0994413000d03041c10402c040240c505600c0b040320420988207a0b022100301c0342030320207035440b9030541841940d9a401c1c088480c15840f91410b600c4d014080403d0200b40c0311000400b4505c143c20940b070412141040b800fa8036954103820046400043e800c02c00154041c0c800c112907900001450b02100c611b5031905c110103805840c0d0401c5400103a41c1e10745205c4400e6128564802041c3c156015000f055000540c0380341d140300003060180d0340400080c40c172020051521900300246100c07907200311002024039140a1602907031205400602c100f6500f5082c004890845118810012048200d06070b41d40c014088a04010040280c19568032810020030207044044003d00c0b9031802c01440c0d4600c2a8078144149503480d070003c0d20100961001840103881d40c006650a032402414281c0c1640c1c400f546040c460054844000d400c2402e1104246152001c0005140034072410f40c1594a1680c80d119003030f03224141071182c2c400035071096041e1000e80d80a00300420041c98064 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 151927311 1250 151926061 151926097
    0xf060f050708040608040b01050a0506041a1905030129030402040903020708010f0e0715140717120717090309100203040329090c030d0e130504030905040b0a1a 70
    0x5140c080b483e03081a4890f40c0415a81003c000810510301c004074054442114100481d50034013011401f036005901a1000c050076080c0c000319880303d07400a88014a101c1c90101d0400707002c10703c009013950000e00c5150600410180e943d40c840790b00140280f13145241000d1542140c0e629020000607100c404c0c07054095000301280420300e0182805500401c200c01103000c03900721641d070146498803010381c0c008a07100c031018030710f0b4050960042070b0003c2c000708039400a80300c06d8641468000c0118007510510014030010f0389403081c00b801d40d2100d100d28102d8568901d03101c50152001d01c0d100c0211215130081e0000c0080303040038030b4091030151a8440910450381004d4036641c0d07800400c43d10320182d1200e540000710402100d001c03011401d40c08807200c0c000c2d0010000c09030100e9510381031024228188800c85520328030607251010b1044103501091014086428242406000d81405000b208e004505040807441c090070f110503480100c0b5130800b400c14500345030000065280d0003011084030040c80362 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 151928561 1250 151927311 151927313
    0x180402030a0201080c190201061805040f081b030d050f15090601080a0f0e03090a08070e15010e090403120b030d090b0c2d060109060305030703030f0b0a030f02090609010f060f0507 79
    0x452031b205017010385400006a840c10580c0c6402540b149098030f0501d1428042003000207178540b05103040303950388880c071507469030500c0340e0348035440303403030742505002880040f86486101009802c914002c080c1c8581c3d80400f0344507035070081d01c041001180c0b80d400c4040316000c00c0c4103521034004250303c11941000040c00c0c92501c440e58040c1d801441a007521948040344046c1f26242079540c010041800c0c000504c10182b83c03241220600000403da9007020000c015014040d074040c28240950300c2d001040030712589002d10b0301500060000960100080c50085401c01034140002c045041d200076480b006455454000007154a1344492a003001c540250100b035180300c15440ca0f507012903507044000c240c901748044e032102e25148059000c10001400e04a0800c08140040704841480e41c26140101e22146000d2000020b00008071403c0c0d0040c0e012480001807103c540403003d802c51085840d00c4003600c0341e01c1000405103003030088600e0700503180800c01009000303e01105040ca52420450700f00122 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 151929811 1250 151928561 151928587
    0xb0a18200315040210050309061302010c0204020a030f0e0c0d060905010908040f0315060612150e090102091507020f09090c06040924030b070302090613060c02180402030a0201080c 79
    0x3006070203280800b412400d01c000c510b03200c04102548280c61404030708600d002a0760560303d600290001c29403050000c446802c0da4450301702c03a80c400f90060015941c68034203500050040c00050035523504c0600d40f42c0c02c8c00c2038000104410003180c5006140c0c0120103400e1301d64200600000c0703002c8845640c0d800702c860003e1400302c0540300600130703815400c0100d0f01d50b08203040070030800c0e400d8054132854a60144003480d04001642081c0d044800009400851000c024074032007016048003010201d032a0804c1400c40341500140307814101a1649a031610200001c3d01e030900034140c00950200b41100e40c80c441e420304104040d4403269080c00c0f510b403502940c000c10020340c42078000700c0c0021b0300d841d000034500c0c2d40d0f4402003503a62200b001810900b40356440708205003101900d900100f40d00000c4078140d6a0307604003940c036040012008030b02050341d121320140c004c1c0c4000c0000c03806002400c41581056421000007172103682c018004e8400c024080d801155203410040c403000c0c0d03050003402035508942c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 151931061 1250 151929811 151929823
    0x3091201020d050c1b0f0d0518190603110304081204050a060c02070509010501020a0f1e0501111e130e041a0f0702120a12090302030f07030c0b0a182003 67
    0x104940009540344000003121700c01c0e000140418003c0e81c0441071002c0b00a00000303028043d0703011480e045488842020600d07180c100102005030380803501d9008454900700002c1240d00b182e809850421083d44000740c0b460185c0001c40e0007a05140b070510420b40058500d005040d4014070900c00e881c40c64106541d60301c12070b940080f481c4c0c0141d02008007408242018030845025010074001004207410315580c40c5000c0031400d4000b00131341d0b403805050f962203c20101c02d00340150b0040003480081c05006070410f075a08101010a100e200e542a540107450740c0360111281a01c8074030700c00100900304500081540f4003e00101c0303010088a801c0000821400c480324002c07100c1c0081c40c0c0060130300060080c5428010b031f00e982082c5804011074600e107500442d1112440002180100c0c10300c0540c14143e0840c01a4901d120341544000b0305681010b41c481e85070421103220726545141900c490841d1001c03a665a0f0303140741d201c6840000c0710041011491181c0f4180130020303014000143e00700110381800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 151932311 1250 151931061 151931071
    0xf030106090519080307060b0301060b0c6001140301050a0c02191502030106080f0a0c090b1c0c0917030702010207061b1b06020d080903091201020d05 66
    0x50001ca018401441c1901103103c214000c90001c0c00080c0c1400e03d4aa1139100d00700c2c0c002c0649a6940c0c00460070b031401c2d0040002400c400e1100342d100c051103009142c8800c5c54000309107000b40f09481d03c2d410328815111800c03a101500d00241803054031220854907131103080d684010700000328a000744200c10038400702ca01810900d21002059002c0d0710506003507d0300030703000001c0341d07003071141c805100d5600042070640c3c8c4400c2002c1c05100c0e0320341e0904820508c3c01002c0110414000000461030035000b4001c01d0080c60400cde01d02c015981c40420300d00440e4450080040003520765981017158903c400050705607010b0313107400450380d80e1112021800f00c0f04d40c2c14a080100e600c91108001071114040c42010511411000e146400c45940c0000c0d202c01042c01480705000c0041460b01211048002030a1f006500105212041c051a5000105100a4840c4900610403082440d1010788960b44480c02810000000c50811901c0c0041107151040701c03089a04a40d030900004105442c2c074024a4060 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 151933561 1250 151932311 151932317
    0x70e0a0204090912031a010e2704080903060c04030302060c0a1b1104110310050409030c05030d090c06111e03071514060907091a160c0501120c0e04110f030106 70
    0x2910f400014043d00c40300040582c3c84182203130044010307600210110b2355000200e030036826503500600761034181246014001000c0c07201904004c10009041d004000d149d00490440f02241d44503900c0c0d105600c03560000400580010000ca056450381002a0918410303d0514031002c05010b000040e6040050b0020313681a954002c10102da81401e00c95042c04d040700210140ca10316294500600b04c14240c0708241c0075a130b071220b40d103061610800f2a0440164464292031752080103010a0015101100c000e440e10404904001446801071041d80024220172020709411811070702400b0b60613410640c030a1240c0401c000840003e01d458800c0c4446002010000503130115a40060f065800004e14842c01488280d0a102c0640c0d00503040c45c6c200e4111094a02c146480d4003d800c601d4003950707005d40d070312080d00003140e01004101a10541902c40c00c0c3d0340e0301c0c058110008190252041c0440700004100190840111410950006800c80d1502d9204614000003650301c500164000d074010400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 151934811 1250 151933561 151933583
    0x20a030e060f0f0a0605030a0b07090b030103110f060307081311032b0c03021903030f0207030305041209150c1a27120313020a05060406032705070e0a02040909 70
    0x30f81c88456003aa40018056604002542c00d050100e07a5908520740080d0003500140700086403180319000d950068080308030402e89a594a02d05000000f0b1115022885a0700302e5600c0d480a0915800303581c42000c0654400754961250202140d5882c40320805403000c8600003001e06aa44040110300c0390880c03030b0b10186109003840913403043c039035641000300420000c0040034000803940c0010030b2042081d0203070100c02269220310b0103400a00103643d1100b440c60001c1380380018103030542d001901c224018542c01c200f003c0c03a560110307241d808a00448000048010034646082d119400c00742607213100c3e100b008140d100902020f210014110340f880490030600300b520100c02c500c0c1d00c000402d040441f002301008140d4245c61842408000d1041c4c1a81c401c5101c2c617020b55a400030000018117018002e150b0321620b402008002e82503001d03c9212010301e00ca0988220304000412401031604500585219810825450303e0808013800d5940d581e038081c00b0100e0354081038880c1c80309140c0304080c6015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 151936061 1250 151934811 151934821
    0x9020f041e200703080703020706090b010e060a0b03070e13020309011b0801030c090e030904050703051e0108060103110d06060602211305040b12100b03010b0303040b0a03020a030e060f 81
    0x59a00b44280000100009041e0441d207951100c1070701c2c890f41d0f150a104440d0798030040103c0090040c46000381480342032207202d00a104d0901c0400307041c3d071280305c854100707580c401c400d00401c0c00b036a103d40c14010700c0c100300107030603148207880d0f000d8564001401145020314a0240f08142e82007034920080ca6503452a4642610810700b2600c4548501c1d41849100356240d038460b020907010503c84c00b991591500701c0d00c10749140c24000c0320100c40c0010010022030800030310040040608460425060410717031030000210880501440c122562070005100d5a800e40e601d42242914019006e0f4109401c513205000140003800b0f150080c1a0760390007400400f0901c400c02c1c1c203196100701501050a420003900c4a5002c06d11000e00a40300140c80101d584080c1102150f8103060a415141890180d2050030300100c2d070903009071145c001c00b20000e0055280c1102010380303074400c41c80b6010f94407004102801109009402405015001c0c2c2070000303910014880181c1001012903000b00007140140c2001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 151937311 1250 151936061 151936121
    0xe0708061815060702090f1f0b07120306050d03020a110108160c05030c010c0302130b0331080d090b0a0507050403060504080c0f0d02191509020f04 65
    0x55441a011516141c00403039010800384408005480640a80039440c031001264031004101c601d403e0340070300701d0200c52805048400103280c6c207403004900510b030654040700035885200310200343c41d03800c504580ba01c000d42e650b48010304d01908242050607250390000410366180a200d29409001c2d80180040c3e01882c940750451800f903090403414000c0e820300b40a0b03400070014a4030941601804c286202c50100d082c118074600500c0c005400941c2001c044854959040c2c000d88941c203401c1102d094095159050880b1600040318003d460300414582e140c8108000c55007490116650a09c1d00d250035580d131030717030941903010005131880c240c1c07640c00ca0410001060030056200410020400c01404c142e10010883e12580c030001d0402511400407800b0b0010b11821680d82aa9400458142030701c1059015101c19030340ca503860240c0030b040300200300010101007a030745995001d290114090744035407a1600902d01c2100603a085001108050b099480758800c410030804242c0300c0c00d040da40c041c0c00035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 151938561 1250 151937311 151937327
    0x190b0a03061b0e090c0f03040f06020a0f0e0d050606060a0c02060706020a110a020108010b1803070f0f15080613020d140a06050102010212062704060204091b02070315020f040e07 78
    0x1c0750250741c0f014100311724420350005071825481d00e003001981d43d0302d40c0e040507049904c000070040c10440c400208140900e80124401030500303401d40300d664100c080d101c10003c08405007a4003a0042d00f1401c0000d01500c0c042000b07020f00344040c00d0600d10b0b034401d5000319510b50820213046490326400191550700c640c124540c155100841401060001413640c002490301c1c00600c03515088400108400184004800508109290140840d01038580c6d81d07070704418015603441050300100803094003103059400328007440b14203401a20394182c01e880341800e20802010200021300c06540c248801e11090500e402854800b8083c0d51248156041868840048414661026065a00c1003104d2010040d8031560250f02400480d2a030841c7c2c11428130301034006004100b05040307444040d04000c100000b44d8040c000340c540b200020800300160072a494403175004890201c01592125038104006000800c0c90b55000382009000350601ca00b03142c6100f540c0e0042d40060601c40302d00401c00c8504c60f07000c000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 151939811 1250 151938561 151938587
    0x6030e010207050c01050d140901020d0e07060905060a050f0a0e030d0f0c06020c070f08010e0d090501051909082d0606010c0b040c0e040f1a190b0a03061b 68
    0xc5207428001d50f0b6003981c40f02d0300c50586042c404041040541c00c1a560302540c2c606101c065011060b10f00540c01a00030b6010016405000b403508203a00804000001d00005031942c81c0c580301c004505040401681d0380042010201700401049100303e4000c051014242140707144e110303070700d031003070031104050908120f403070038000700541c6010600091380e00840850089411002c010398803c100310b034484c1000c205401c0740c2d0001c1c01d1020000707503c540540c0100801450541541d00d484505542245c1511942c03003518009001801602c074090310f001c010504143c118140074040c1e45d550319409050502100c1d07048000e41d040001d00031000c46a2101000302061840a8016840d0660029100042010700503003092220000a03003044132100003c1c000e0400503a17900c4883ca0b1514010740040d8041c4401c441640d0f640c0c3e04000f540c00000409402400c00861004800380d40709030005c020a400010203510680c1c2d95030000116010b480b81341000700f044c411240320041315143c080d2101e480441 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 151941061 1250 151939811 151939813
    0xc1602040e0109150c050409020f040e0403080103110906010f051c15050103050108010c09060c03020102090402120105040b0307030201020613060b0910060212030606040302040b0f22180b06010804150608030406030e 94
    0x40c845c518680c40401c0354203441414000680760040c48045580038091504100c990f44c407030509010a041c0c0100f88035040741c2c0300300140005030607240c05110300c100d0291082404509202184c1150707a01a030050280780d52084d88088010030114496826181580003036021314208100500031541d15025440c003520b0000c0091103100300701c1000400c802c44a204c1d81c8100f181112501041610079012101c00800041055456010480e03804d03014030028824070b03110b1840c1081c84c10050601080c800101d83d0160040d044682d1089021035000309212001c031103a0340d54002400803581c45400d464000c0200001c0b00790300c20700b0840b01a26000c2d0507800890005c009104101950f5100403c035000e90703505070b0b000b08000c4061300c00b140c1c1d140900459140c0c081d003d4250004a068104044164201100e03018005030503460f40040000350b8604014025100c8140040c2155028040c0c891b0031511804140c0c0d07144084840044c01c8030010341250413f0780000604000165260158980d5500454 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 151942311 1250 151941061 151941071
    0x60e091209090f1f0e10090905060c18040e0604140601080d120b03100b011d01090902070c051008010305010507080702031210051302030105100c0b0c1602040e010915 73
    0x1000101c1c0b100c0010b210107180e03a0010f001400100d524101c40d540d00e51100f0319480050b449040c0003140307402c200d480c242d801c10307821400105034416005000302c1d150800050030142c1c07030b11410382c0c4107544500403040741c0030044281d00c00c0c40c0e201d40c880c41007a02a0100580f40c10b09003440e007249040d00031038400e102d5500200060201e00008500c03150192142d0802c3e440221408040a018102e24060310342d0501401209501101c41d0f41c0041000003001d80c1c9041c81800800846041007028480711400501c1d008814008200307554000c0030114001c0100410031580c540000b03003a0a45e84000c080001c2c1100b0040040200900505401880904181c00c1034640084000d640c2d020302c0c52554140a8840e000c203001030702e01c1c45e04e00003412000d03000d4036290881d030781701384040c0d8028800c19029038600403074031040a100c0c1c0109401280d101a002109898184801400b5003262111044545042020000680d607a1141041c240e40a10020030b03140c0e4181409154a4030910002d01080d0501d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 151943561 1250 151942311 151942327
    0xd0e1306060f08060d14101b020c15040b070f1101050711060d11030106111e0a0f0c120c0305011805030405040e030408150609090c15090112060e0912 66
    0x111284400760b45078a804440c5540f60000110140907103100500795903980f940e40d0740c80180119486ca0701c1c8100b00f50030302c507804880c1280d083d5001d8010440340103030000d925001051405180b091142016000d04130f0409031184256a0740764443e135021102c4900e02810607041042c0811003d003800ca090034000e0415929403614130340300ca05103e81034400c52002400d24038009041c0d1150900302602e03d555910380d80c440402400045000f60350140b42d225820068507008162401980d0141404000d40310100d21941d0710004d00c0c0003a102159010707031512000c40d01040c0d00703200108240c00f5013403642c40c80740f031810400c1c00c40300032039010b60311013132044012008100000b08490446000fa1800103080303552581301404c41c0076076004100c0302e0180303082140c150200c20700124081c000480d141007464940000c100e83d9000c1a260050304480c03851030418024500030041c000a03c01810614500351490129904580e00c5400c5981450083c005000003a41c040020104170840c180f0228600030320 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 151944811 1250 151943561 151943567
    0x61c060c0216080f070603090501181112061003060e0f031810170402130905030f09010f02071d06130c080a0501290c0c090a0c021005040308060d050304080d0e130606 73
    0x46c0034901c1490b440343c28801c01c1000940c4004888840c4079001c1c001a541403410040800119594902c1050824a031000040e8041890307401809104071721b03c00149150340310000351204016a10650140410584c0000424001440421803260031f8441101071036040044010601d1800810080ea0800e148d40686a103101960802c2d0102d44400110361550401e030050085580014100d0001003035100300070004030054a90044240c1310100307600c490600c200d94550007031140c6109000e50464504c40c440584d40e05a42010000e0421604009900e4035402526a2489000001b40c111020004041164800c0034050400840d240380e44d10344443c6400d480580841c0500d00c80580000c0468000354104910062201c0287c80070440f417804205403801004175015500250181d45104405a00680b05480c0b00f82c7d4944c0f9051003a490b44e405010b0840c0e01800201c0722880b040002080c0f1034401c2010410040702ea90301d015680c4000f4090004140c0d50200c04881c0c04d003460700900602d90 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 151946061 1250 151944811 151944823
    0x315051506181504060c060f11030a0207031704240507090b0f0403020901080a0c0815070e010c14010606030b040209101803021309030e030c0108061c060c0216080f 72
    0xc088107440b1220100b940003d0208107041c002004008000800003200394200544401301e5003d9003042080441130b0801000380d81042444100c01c90b0100006440c21401d980603000141c02840d100204004030f03020181c440c0341c2a5820b80707a00c544102103040c03040311a401e28100c0d40e103000040c0070a0501d40320260080d11b481c096001004004100f6000c500000c400342c0d401160000c00c100001d50b92005a40c0c2c881049060036102080c030840045880c03032001810120039185006950007665032134004840682c0402d20f59410082c0c2c84000c600404c1c400170415902c0c6000100008071145407a8000c0c0072199080d5050380240e00501c48001c981e07840901900070042c10b8181400c0700081d410351240031000f940c000a600c140480840b8806011130b500c2030400794030a450724214841c1c08800c040d034801c000c40905001907a40720020b4034a051906020059860701040c40b540802690780b80030030f46840788509801a0700121041d440100c1c0c00180070024281030f0003801028040e4070041e40c80311 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 151947311 1250 151946061 151946077
    0x50c030715050c010b0a060306030c060c150903050d0903030515030c0307091e2301051206010b0d0906061409070c050601090b010504080d0e2106060d0201020102130315051506 77
    0xc90003058083d1006400e40000c00724003401014601c8aa80300e00c00500244039070700043d614040c0140b808075201d0300400002c003c1c2c41d0000d05035800d180200758680090309105600710200b140a10510240080a002d845a062320948011940c0e246c0800c0001d8224a09050300b88039511890051540e608c0119250b42615001c0d00c0210300d8205201794902156140c90f030305611307181303005020b5550480c1651501c4003510410041c40d410790782c5204014020840d4154035100741c02140041000c1c061080090000882d007001c0491118110f440382c2c0125501036100c94845003650038082018a00400d40d02e60241160901300800c4c2d000340c80300f690b00c1c5814000c0b4400715998060354070080c0e010303e050720010100401103170030040d90000300a1500c4580d0400c03e01445540c5004075800c1804505d0300da2050000f0700038010ba42c2c8003000c00012802000c0e069065541c208031303245001c2082c010b00c070044c6000380911182079900f200140f0440d04010041a008036044c48451942d0b51802c00b1104c0780 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 151948561 1250 151947311 151947317
    0x13050613031d010c020d0503031b09030d0305151201090209010503060f070f0c120f02010e19030c021906050315030601030f030503090106080f0703050c0d121409031009050c030715 79
    0x110b03001801039684603000000690712038000000c1c942007000c000b0007144070381c9460114080148840b0040c040138007848601c079600d60045604060468400d078402d40c1c1c04810610f20603201071201010500d4411080c556103001d94507080c40d10b041d801d00c040003a0040c00107900130309180c80c1501814001180152203607081000c040c1e05003084c2c602c1003c9981ca0136400022602007038140710703c09061419480c81c0c540c0903500704245400d580c000071494541ca10014421400c041d01550740072241001c240700c0c102d2f40082503c0c21001c1401101113000050400758031076a980f82004076840140c2640c10b01e000340f00360301c580e0051000650345003002e0b62040d45420069200c1c0c40d1381e1072203805011a50070005c030030321800003040d9101900040d230344200d03405002030f214440301c164148551401d129402400d60030711407861b40003c520801850070011003242c220b50600112000280c01c050f14011103c6846880d22132507028400c0500407056900c404400400e0a640340541000380c0070024042e000038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 151949811 1250 151948561 151948607
    0x506090709150201020c160608070206090619060801020406050304020310110906071e2d0c1502100c020d0305010801180308060102010b040908032d2d1305061303 71
    0x240c80c000d40549184140c3c010a0300c102800349507d400303c0c1e8106100e40c80000d4041d01c086050b490000c20b9260081e2820009003100f903448490700009034078030040082e0031642c4c0c3c60000898030020310280020745001d40d1004e0b40c034203150042510b049a00d2800655503403410740d800c0d26540300d5004030341c00c0c07000649405071917480d1400d0421006540c09900345c00100e080c121402008000c180040e00c4101d580409000e10100c42115090019002c02c0100320005812052113032641e040c3c41c2c611594958411202090141c444544c1a10f100361a0b50f0003685c0010f02c2c1c403038a15010700450b400743c1286030003000b142d0551003c1000b0924481005030501c103a440228800780d10039008504031350070280041c010150f2928008449034401c4864403102010000003c0c180440d4242928900102e500f01170f995480c0ca41420050f80f961701382018035400200b031411300301102d0040340c621410f0b400000e610306a80d60b0034007030f05086001300000a8042c04802000009820402c000d00210011080d120 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 151951061 1250 151949811 151949849
    0xf120605060126040201090803360d0506010e0a020708070308040213060f0305060a05010602061f1502010203160f0207061b1a07020f0c01080a0504030e1e03010506090709 75
    0xd01d0f60100d000d41000c0440549080c0d42050710031038460169100781c1e030305182540c0d01c00c080d80e200c3c09007603d4910144041c411880c4228601d003030741001050002d941c00d940310000400035810320f80c1810112401d070000c6004002c00038099204507800954100254900481d80d130b035011651050580c010140000b1002003015900da10710b102c59030000010040043c41d44845500c6021100c0d84012103032440340e1700020b4000d07102030050034101c0350b0540050900783c44410703040e81e0a01140810402452001000059140072200d0890003c078280d000141c0d01d042c4001100101007071280a241030201260007003da040c2d002581d80102c800520305041c40c103500c120a00e4000000c03200162100300d42d180354502d04800400200e01800240e021944003081c085401a01c03041d15401d4540465001000588210f4407900015409442031170700403000482c000024060000c4036091821202e41c80200b00c045040c248035860304401c00329502c0d800f074981010010301c0740415009078440d0000d8503d1000e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 151952311 1250 151951061 151951067
    0x30105090115090b13081204050913080f16022d01030e070b0d021b21070501022b060611030910090e04060902090a020910030507021203011e0f1206050601 68
    0xf5018080482980740c0c0c50020130031100340249103000d03044150058801c896402c000500c1102c003194006451b00803a82c1d20180854524541c00c001900c0340f1008000c00c4142040c0c1c140185402100340780d0114008025006201c03060200512401094900d1034032000007940d02e070851461080c00340307004510341c01420422402d1203002d9200c104031a05c0410300d024845829005401416085044c881082e440c10a030b080e5540c46032071074030585444941288080d0917800c1c0c001d100982c050b0700058948074035014486244041c114018448038000c10038056070307021602039680101098034241d030b503080509a460380c036482a00342851003050202542045903008108400c02400c40c40d00d241e20034501820443c0140c10068012842480820000f03008182d0301d109803800c3c104007800784500c8ec0c5440030242e000300400b6080c0c0b0301b503129000840d007010586000450207040702c0c0f402110039440402c80401d450340250492038002c95003c209006000c6c2c00c84203809182d40240010445480380c400503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 151953561 1250 151952311 151952327
    0x5070905040203010f08062503090609080304061e0902090631050a11040b120a0e0a050307050c0f030303070c08090d030f08070201050712090602090315041106030105090115 76
    0x89030842c0c004800040d103c01400c0950041b900028150750059039803c3c103154511105003255001c40d03c13803511880c80b6a12276030010810034440c08000600c0b214685500b0780700c2c2c0044504031504c41e1a520703064418003038035015a8420300300e014140f040e004294000f800d00e500081c00117024501940e030070664440c9070700b01650b0040d0b281c849886e81350300c2c600300040a0302d012201003041d24144140c480030701c8610b0040324100e0780c00742401410103942c40303e1054118006410f01c01419110207102d00450300511030002800e110303074001d603918038243c42e0031307400d00e10302c001c626109040c1c02c0c82e1f4001030f07100482200c0c0d001c12203103052100d83c5039914000301c0301d015441c20344c0e40007104c140b0640c0030950050251082032601342c640c0401c90351031040403070036140101e40401c00604000d01c03180041720260004208680700c1c000160410301001c01080c50702461400c5240d40e94410014041440080b800e6400c80d5401034a40728615810034003c50b00001040c03044441c001f0b900c0e2a50603d1038481c40c51 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 151954811 1250 151953561 151953569
    0x7060c1a040b0108070b040f05010c052a1302030103020d08070303150e0108061609050105130305010908030115020a0201021b031c03020a03060b180609011403130b0702011a04050709 80
    0x180c0c21603400d00c1e0038500d40c416000d002d091441d1103400004161303502c1c0c0d4015a01101d941c141d50020725801c01e0011540c881503800215280d10402c0700c5480c0c103c1030149041040c1d10391445032807a03d403100003040113a110b1042c9054607540b0400050016807076901d028040160061030030340c0c4c0c850b807e250890081c0200c604a00300c400603080003061500200315405e041300d00c0103003140c40e0b90301c5a1070b0302203040ca85035a4500100b540300b00100034030b50007038001d04041d0100030740c0c0a1900340e4030348580782990043c0c141122050340000041c848094207406500e2500c840340b0040841c0510350340081d6403004e51070301106000d041c01c00070b260196420030180e0a00141d11284041103030003003030050040c1d0800c2d030429020a040030b8001ca00c0d80c0d030755000c1d5084107080c4100c2001c0c2e18480401d010a503480300740701d58108400800340e00d450190328002580910800180840d01881c3c6042907400014040d05020031641000342c003c641258a650500910f00100e41c00200f0b52103410040c0c91500780b50380 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 151956061 1250 151954811 151954853
    0x20705151801114605071a0a110408190c21020901120f02040c050c1903020d14030406110c0a0515070809060414010b0d11040c030b0307060c 62
    0xd6101c0020100c00003405894011300700c81060b60720520106401500d4119801d42c01400c031014000c80d244207103c6801040306681002c0d803900c105511284955541500401d159103840c4081c000e07414200d1083c07605070240c0c40310a5051605120b4402c1d2a1007a04485444200300c0d03142000a01c200c80403401d0003801c6004540d0101d508070004000c1c2e500556605901c50405003000040001700240d40b0741c1d5142e400040e214807903e0a60801008008200f5121b0402ca42800050280e01040000819031b11a8418181c007000161500a20701006400390b001040079152a40400138488010baa03001644007002190344424018510060f02070f03c144880302c0d115003c1c07117405008021801140c9090090401e610541c0c0d110020b580c0008269074203412940f00d2000900410104040d0360108402c0d1400486c02d9021170b0f00042c41401c1881013076070015110f00098986103007611403600c0c20300f401c1c00c0611201c4030002c0002d4591500388195400d100c190103001003007140c5020500e4220f007040c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 151957311 1250 151956061 151956071
    0x6160210050f06120705060d0509100603050a0c091404020409050111040b0c1005010b0906160203030a050d0507110304120813090204151805010c1b060e010e04020705151801 76
    0xa02d401400c01020b03101030303004034110405204844004210b400c04d698004c3e01540c50440e0800b10030000b17242c02040f4074103d0046032640c10f03915040340212001075014000500c403101e001d04100403807164a80c040c80400d890707c42d0412107804c001c55074652241c1c04450018044445040140c05401e1509001ca01810001004a50011070344042c2096501e000c7c00c84890355400314030803044400c00c1c003079400310f800144040660341c64890700600c028250300785814980c0340d00d40d0219141d500000500d001160f80071400c003081101e0391103203942c0100d40d4502000401e0b0218541512803059006120b0b051000c02520340071322000d041128089216034600601036955899490003e4015010b20a10b07441000590054140b0520700030012040e96048001004e15180042d1020321011100b11118406078041511a161244a100080c207194840245203c500700c001880310a031710000300d11861060002c2d5000c0350b000a070042e840b01ca500380507104d035251040c905509214a00580000f98204 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 151958561 1250 151957311 151957321
    0x160509060d050c0a0e09042006040803190329060a020316060f241e0306020a080106090b04121403130303110c010309020d02040504110a080a0b0115020616021005 71
    0x1e03c000b0289030715650755500c0c90b010307582c0805c0820181594050240c018032a05001a00b8071221150100c80006090910345943c40b100d007820354211042c44100440c068542d403800d20740601500c040310307001aa400c00e2102110002d41b04442101c01d00750b000301c002140610302e1500030012501e400c040030040030241001441c055000c2d1440c694143d10250a002800304041e0005220b005051440703001c0311030090500724101c0500d42c03100001003402c0130020b000404a40140300420084100d5030f11017000350b042071b81c060800c241030307800148408070410003040850341c120701202c0c0785584008248140b82250b403020f4075500030801880071100044200108041c0c00c49211448001c1c00d509644001010000540444010102c0690400791a5907480b00501e81584600c5c1d1251007200d6140c90401e01c1d601040707010410380c00840040e48146201018071940e010b41764010440c56240c500c110844d504000e44400340070745011803182c071611a641aa6009009440d10000c51a00810061404d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 151959811 1250 151958561 151958581
    0xd0f02090d0516060221090310050a0b0a08060108030f160203061008060f042102070e0903070506250804030c060f0f0e071a13050303070302060115030203160509060d05 74
    0x1200c403d0200c5604861000414900106000d2600a40d245450348004100401130101d5444400820303454020010b100c1d0204085200300c501580e240040041c00000c410144002c452450b0001505a0310010041040140010445015404000c1e90540310000d0340b40302220780d08a403600960602030f03d0304209284482d2060b0318115412741c000c540742074903800c0103180032040555020b808001e4101e41e50321a000b560481200703d807400e1040f64451a42c600191001160940d4031941c3c6030000140003051000400089410410881c00381080c440c0c40c000d04000c1c075549505842c28440b820000800b414007402035072b1030310390300070201740100044c0100440041c10420100d940c210301d800f894010000c00020014142e5000002c1c0d107220542d4110000080d07000070441d00000d8800c2403010480e51024030241c01174a110f900201303000e5040c244040460100b0403081d0080510500c1007080002074584140345203112414425914000c84010a245100303124450032000d0400c014051500c02d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 151961061 1250 151959811 151959823
    0x215190f09060507020d0e0109270606030204080d0e0a030f08040905090a0204060b070c0608090f0307210c050601060503071e0e09070c0c0506030604061d01091505060d0f02090d05 79
    0x40744d9826100c0080c44501c0030350b40d6080540c140c0740040e440c4807051200982c40c00c1944030703150b180a00340c8080080d01103d81c080d244280c0140c00000c0d00890100031402c41004010040d411310b0404503500200303000820034103969807002501e540c1c840c0b030385e140038003c40d0000c0b6000f5041d228824845840d00b002419a50515400103d00681ca0124006191000d01d0203484200c0c0c0d10414401c030340e526080048442d10006003030200e150140c140350701e41c081d200700001c1400500c102092001318035240001c070075180840c10322030144580791310404000b507000700d201415501d26082013034072500d40c0c2c1302c01c841c40100003501b1a10003400701c14200c0c240e07400600c4030682f040304880401c040d03940c034402103541c4041500d0003849541007941c14050351401c1405154041c030050400110341d6611100c600d20880040d105030306045840c8c0040c420284a4099400341c445400c0003030030079628020214880b0b104482802e404181d03903488800d0b030040550100c0e440303984028441c0d589040182416501c1f05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 151962311 1250 151961061 151961071
    0x20903150907090902031005040c050d030809060108030901050a0302180616060b0f0f1e04050106050d2016020d05070f090e150402060a050c1608010b010215190f090605 74
    0x8428000d00089030f080b20300480f010968064003a003600c0000722101c0010700006803080b22074051604000c01c0c1c98582151694482c0e000b9030b01c071120b608029820301e00340307001a044140c048d08200200003003a600724088400c01c001a14005907100d0a61080e05070310004c00c41c0081d40880d0029100c451080c8800820740b0460003007600b00410018403042081440d040c401903a045a1040d0380d0000f01d141614800d0015081c8101100e00740b8819400241241c000340c1220000c10404988080c10400c10701c6004074484442090302091210080d001702c0d90b009180c07196030641408540036046455030f80a906025510a0403964400d40b100b0440311481c541d805440015881d080c441e2500b90b800250350013009509000307040c501d49a917001e1007519400000c100041c0b250400c80800000000c12001d21031001c02068030401a05004046080d02e8500540604550001e8480d614a405900001c0d80060f0950085010848962000000740c038480b130004242d2803401100c1d130140105a00554490 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 151963561 1250 151962311 151962313
    0x909032007030309170705040507090806070504300c08030307171909031709010c0f030219080601020c120102070b0609010e010b03040606031202070312050f16060209031509 76
    0x22415825039150102d21000e000a0000c4908100d80302d0f040c0124600c04d80300313000362010b5640740c10125041c0c440036104880000c00c60791041000e15018001541c200f141d502d4070500c0d041c0b802e99049402e034200c0000511504440040911155170045202500d5602c1109000c1c215610101c0c5034483d0012181132000c1191307407141d0120a11102100c52140307200c400d4101e05840350f01301c460001c2402d95030417070600c80c4050403015030300c41c8011800d220703040e42000450055004d0300b00074444614442c040742458010301c509000503800004510340e02c2143c2c0742803d03c0743d44190040f8a44805503060340e8100200700741103031444606400500307a440c0100c0c81901e440c0c5962090040d9444c092040c0e000ca000742000610200041100450700036011b600d01142c003d46940ba500c1200c1d05070380060000d80d000240800412070b00ba032042d00c3c44080303410300c00d0408195050303180030b070311070300c800d515544486030b44400c100007080d8151203240c000913003140d003031803194014125819400c1d10341c0340c02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 151964811 1250 151963561 151963607
    0xd0309061101060b1204050106050904060c0905040b010804060c1404030302010501050a050d0c2c010806060f06090a0e190222090605010e060c0a080a021f0c020a1b090903 75
    0x1032078105004940c1202d500d850307800e01c4d015a8a5035840d0700e0001400885840d502e0310400129680c1e60402c06016501418000440c030158040250460509905c081c0c01203085c2003c03503c241c2c2c3c000d40042ea21941000000c0390501100404031260140c0713064240008030040707008018150305510a505072481614030010315a2620108241c513900890028170140b0119410b1001c90010f005040c022211825185900d150711a80c80c890f5440c260030040b00e9910003000c008940c42c151100001020058403001d00c1c101200000c210f0b140500e0040c40d14194032540803c410796600359040100041c5a60708545039055a81cae90043d48045600141d403050f0148804110f205080c480c10040310302c142c40b0891030300c0c3c8a030113005080e023040710710f20707200d0148511505c00701d108040100180d40065002c0c0c64108142154507010010800e44501d0302c42c41c2000c400300d40780c0c00041001c1000d8200c50000110200980d94016039201d540191607414102841d004c01c05400c0b4203034081c0c1e210a8820300d00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 151966061 1250 151964811 151964837
    0x40501050306090304061b02030706030f1415040e030c030a1106010603021801080a2a030e060402031203040206070c0806040c09020a0806101206031b0509131b050d030906 75
    0x10b510181581c1c0d80c01c207500100000c0181074040d03002440c0d14a25141c404034501c007650002428980594020004241c43d11046440c800c010b208a10402503002030b41041410a03020f4000f41c201101d20f0b181c01556100d0004031145002c04c152088500d400d01100c2d034503100708800504401c00b0082d000b500740320344000031400500038001c1d01c4000d9035214403101ca1207400780044842c1200549180d5900341d40b08143c100303003107088441d0030721840300103e00c00c03580c0c1d8032220040444100e107400102c15003140c0b0a00c0010381e004260194400e0801f0001600e83e16280001455881010340c0101800540350b400034016102040c25071140703004181300803d4650341ea05290aa109055828002658600028101e85010004400c0059161034210744550301c40540b40200d41d641c3d0800c4d10440180d00406140002547d42d0790058002540d0340038007030134502100e00c030880c840c41c002000d41064042c0382000c903840c0030345c11009140050000c00701d80028140a420241a0702036000021840c2e5a000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 151967311 1250 151966061 151966063
    0x309010b0102060c0c0c10050405040504050d020c0f0303040e0a02040506030403021c03141315020c0102131205030f0f190c05150702031e0d151706040c03020907020f1b0405010503 79
    0x5c007001d00d1407015080c10154102085a0301a00781c1155090003028000412141c846118103403040d4450401002030680408002e07103000b04005034644070f100031052444aa031004030540b41100c03a5420b11059507102c00a010010740a10b17000950481008810002459800a48000703e210a1920039403020380072031341102550b0303283c44000c00b40f040f01c0740400d2501d44402610b81c03a140c0201b40303e01500f01e115401c001070781c0c082480100f142c1c2d00400c03c244018131204a00000f041200030f00c141c064040e40c6d841d500d0b8090692100c40c02d040115400610100c83c0c0111024040300040b82d005007041240d004e0b10a000d0690166001d00c25503010a08039000891301901a82d41d580056050005403030342e42c196118920180c440c03020040c002102020054003034418000314180c05a00f000d4280500d1288001c0310050500082c0d002505200c041345084841c041a070741c056500308410f035540d0b00103a25100400c5c18003940c138481c210071148100d500300140e00c803001c0212420710099036508201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 151968561 1250 151967311 151967317
    0x30203070309051c0b0612060901060302090603070635070c032006060f01091d01050111060124030b090709140d08031302150705071703030907051903080309010b0102060c 75
    0x21201300c00d0088114004030302d10f04019a4402c03030085c001c4410101e40c08403107080070300035030324001560345541c1c0c14400c5240140d009035100000b1b80c002e140349458544018501306040c007030741c1a10502c2d10950134241c400c0e075608503201040110540f0440c00e2041000300b406041c00c8080d4000303981403a0200141c40c004a0440300503085800825650b1510307410040704202882045047c40f52241c80003590403604a02c00e105140e0029020619615160000d0711390300000345026440e4000000510002101c42552004880b2402c5140364031a01d104041d4001d2001051141d031089040c1c00f0801c0c0241d2100105080c1d80808407040b40100c005401c0c003d040c0401c07100208112400e2001070b108009000020070464001450030030244603003000806154000c07034050340d0607000250107108441311803607881510380c50301008501e9443c1c202d5283d40c40d000d8900070b06203c2c41540449056610010015031302440d08882c24503628144213143d80e00901c6e00d4070110b400b50003104001410b401000f415 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 151969811 1250 151968561 151968589
    0x9010b090901060e0f090c0d0507180b0310030516051c02060301030b0604060b030109090b180309010305040606170a050d020c1f030f0203090d09050f0a030312020f0703020307030905 80
    0x552070399900b0104191400c0080c200354980000f640c00d03040e003556a480070b0441c01051101c6055680320215411030040c0c42004040d1000d20000c1400c90f03504003502841c400441c5c2010398402c1d240e440c0c0d6102103440d031480ba07001601921810703807404e40d20140301c84110201d910407203903101100e0750300301da8007102c03080c2d5640030790302910500041011070100f045140e84100020000501292506858013154200381c0000d880195a0501d4004106070503145540180380100c400500702d2802c100142d41c3d20030706d10100e042544640c041403c00c5119007059018117a0b100a88191060081c1c000d6950504000c09a07840d21451070040d17110341c008030760105c840e40081c01908240e215448041c2d032154040c410182050399940003411032465501c00707507000b00082e001414240056110040012605810061007031a41400105c403941c0e51b4244903048940c1810301c05480080d0040c044003d000c0e034640184450310002da608100356011004000440c880d48400b40300d140c03207005100c00c515032410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 151971061 1250 151969811 151969819
    0xa08180d051b07030203340f05040b040603060c0e0307090b060a1b05060708060f031b0f010306120b01150915030e010f0f0501080705010201020c1005040503040306020f0909010b09 79
    0x709811550020348a410241c640752030071640001d13900d50101c1c0c0b802030440100e00520300005030408103034601c04826501103080d5103c031440c036400c041c4483d480100c00e1051900c0b99940d0122540161543d40001c4011030700107504100000302481e0243c980f0000c0001e06100f03014100f0041010102c40c42101007054014000505100100303105039060a5110050342151903030128001c0000e00070800d551050b0b0107642c48003070a00700340092104d0082561400e9100341c02c00780030f9107119015264045445c4208841c4035080c0c007060001a401404240c1290a5400c1c011162500f4000a0142241254543c00300c200510241036030480d4000c8290180c14610600300c020554920300c66000840d45040080c00021002e00e034091440440d0a810820000244c030394004100300e0b402402218001d020030300095140c16100d2244540b6001440e0203008500eaa450104045c03090030802c0d90301452340010115074038ad01e9844002d61903080a4192071107a229200007080300c0c0143c4041c0d40e05460007070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 151972311 1250 151971061 151971067
    0x30203041d1303051b03181c0b0601030b0a08010e0a0b0906010e13230d0801050411040b030705071e0209060109080318010e0307090501050f0f06030f040809060a08180d05 75
    0x183c0c1c12100d5074490400200c20000c40c0b491401d1021082c001001028589440b013100b0107802d801b4858450080008204a0341c2012484070214072858207031070f0701032801d10700007460388204c20025000700b820380c00026403980f801d2245504102d00041c0785403090b018462050076565801036a503510a000d000389400010201c000c1a1341d54800c28038070141c1449512881510121141580412200d004403200c4030707841140f240d041207402c05032881c09000269818002403c1c11518002103210324801c6c400c00b010000300140015100b1019540c0c42a030180707144064100040102644200d03a105c1680f04a40200100380958000c010207011034900ca400346042c0440c0d070780040c00380340c0411240f074140071440c008807607580e805010342c4002d40030031100017860354100000e1000c21100071645c0c50158201034480130161307030b9103000c2e25400f402e002c100314415a614500020f40f401003440c0300390402000b0a0405206821140306031081400103449200105500e140c503644480907031416010840c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 151973561 1250 151972311 151972313
    0xc01030e07180f060e0421030204150206040209090601051c02030307050a0f050c040209100c0203070f06020a11030102071a090307060f020309150402060405120309030604080a020d050408060106030b0f040603030203041d13 97
    0x180340d541c042d02c7c280c10018209030791504d0b14a159101c00008800503000b401c02c04c011498000b801c0d903001094800208107540c102408140c0c510055a030f41d202c00341180c00700c0011990100700300c070140c1c0ea000d42074501c544014038058526078961381d4220368178010094070700414103043c4282c0303d10000003880c0044000c41480c040d07503561500841682c160007201004100700c0c400701061310042c80b080d40101661001c40c20212104100344007154800e074010003403280401c4a25114007500070303400844540c0ca859403444180355200317500c001407940d1b05000c8070441c4030590742d000c1e501c81c5403114155500b60400c0c0c0240c1c6e51024088900130b40c0584140070601180c02c104041d50240b9407144116440c11030008000380ca0824100e40441e41000b00260442c4000e5040c00491400803150906c40c1c2490f08010980d5260035050103138508042da560b0504546544400b411111030341e018108100070381d01d03410000e489500600504c603010107403081c01d00c11040760005080c880c0b400003824042d14095 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 151974811 1250 151973561 151973603
    0x9070306021b06090d030f050f011719030e0906030105040201090e0c09030f06060f03150106051303021008010e07230f0f040806060a15020c01030e07180f060e04 71
    0x110101207410380700211818201004102c070f180139880203001018007943c0024020144e51490205041c0c2c00d04001c02d200c04004508401815100040c3c22202c4104001c003505142440d25031300308040851000304801419003009403010036000c1540c07509100d649840a0609039001514001d00089000c1c2c0704000605400d00c0140c1c000b50f0450105262180c45000286441c40c00c40020040740c0000050210500c1e1241e00b88141442c04d0b8058800c46106415218464005202c0c0106010380001d40208209903800d500000d15401018a01d820300315000081c503140d400d000759003d8089a0010459280c090b0900099030005210000400d0503442101030b119041007802a000c0340007804141503150b2040c028001a080100007400e0510784a0204a0220070700d41c07007680d503504080c02c500046640841c01d6580740e1402e003004600d070403a98030742a01d80310b055489900d0200207008600c0c92055250004d0307208010002c0c09000082c0c0b079440078240014203a03130040004440704080700403400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 151976061 1250 151974811 151974817
    0x405100309110406090b040e010c05030408280201242603040e1305010b010813060510030813061101020408060105090a0207060c050304030f0207031101120906020f04050310050907030602 82
    0xc814051005110031401c0450309840c130030381103440c0e1039807182d0362401c0b241058410003959203543e00080c00a0300c460980034050303200150000e041100c001411881c0c03041051141440104006018010f10031a440001d00034000340101d01111003d5402164802e801450881e00341c61740304154000c0d0b10500d5405402407403108185a8250106000000c2c070403030401d142c28815420903024200000c19450b0090844142d440c04905101058050140c54009042503915840c0c5c4002d002659468084031101c9d981d045070303c020700807100005c5403001c0c4542a4440c40c11107240d602d03400c0f01d80002c0c207241400e03405140910007060380404010400c91402d082c1c8581c00c0341241c400140707031071025110401990402c1c411500856000400d10080582c040d1071145130a41d540f01403e00d207421690380309d0b504a00034801d41e04021444466a4070701040303900041200790710039011035440a0041c12903149420078440e291103070113420f0030854491424020b292080036807001a00e04107056031380f440c001350 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 151977311 1250 151976061 151976063
    0x6050d0b040e161a0315030109050a050d02010605011704171605031801052a03090d0c0611030304050721020414040b100b07120203130308070308010b0405100309 71
    0x154481110300010744451090005401580c0040c0c000c406400030046140203455009180c16101000d1180c02c02d40030006a0703410204128040f82041d01d01d1000a0143c01856009011801008690750030020001246550220550020b000785681c80d4010f4801864101c03c1c4d08a407079440f0006000181c041030100e0340f9820f603c0c000ca0418001e025400420480814110fa50364800180100c2590440c19100034012091804618207210251010501820068241c4030a1619001c0949824050050300e4200344090070404010740300d81420701c51069188200703008580f0300b030b00030901c2c40300100450b072045070810002c1908510349815503403200720708010744081c054240140310041e40d84d401a80302c14a00d41c0320010103800c0c43e003404000c450014107480e9010760b580b1000c02054040a043d0350181da04440c1442640701d00a409038154451007840004681c2a1200031040000d1440508502d6010b6130f00c0c00710983c0c80d1514081c2c1440355006541d030119a6420b810022846508660002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 151978417 1106 151977311 151977337
    0xc04060b07060507021207050106090c0c021804050709050106080a0501062102180a0602030408010f0932030406020a050c060f0f0d02070506010311120a0b010605 71
    0x16200c0c4040041a050b03e8000060301c89000303103c0c1000240c503107014551340715120b03c0d10300d008052a0040b50300c0985400640b09101c1d2040d4074a103e00c56000d8105e060110b54140112109903000340110342900c54114089501e100500600d8000d00c500d485400382c60a0501038001540c2051300601c1c2081040e4030801d10310440140d100701d0140200d44d00507030b038852107814148098118400981c00010882c00040c0c2d09074004020b10486102d28001c00141e80c0d100580804e42d03802002c042c2030031070901c100310300741c012a05100940101d5001d505512020588266085402c00c0c0c1c021f2002d41c000191500c20300c04180075509a0131000c40703206e4a03101e071540d0703a84018014040402c942c10030104d141c2901c41202d90482c1d4040e070700801151055a0350b40760404e203508402d801c490040b15046143c002e18003001842c04140ca500c8100011a43c0c01c0c80021076582e00101700203404 = true := by decide +kernel

theorem cover : BRFrame.Cov 151798561 151978417 := by
  have h0 := BRFrame.cov_init 151798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 151798561 ≤ n) (h2 : n < 151978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
