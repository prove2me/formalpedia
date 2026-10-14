-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1897
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:04:32.736561+00:00
-- url     : https://prove2.me/submissions/7cd5b6d5-9d07-4a35-9478-a20f6488d901

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 341007194 ≤ n < 341187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 341008444 1250 341007194 341007217
    0x120706020622020f121b0a0801020a080103140c0607060b0f0d0809011d131a010206190c03061203050325092601150303021911120f071508010506 64
    0x4000c1c265a0030b04c034001c0c812962495020321a00e0003260180070803c050a042c49141d884403890108010500c000d800c095080701201e40d0040241141040e042488641100e42c000c280d10144204189468141003001412030360001c4009440814407410360004041060201c481401c036080300c601708420143c8a01005211400c240401c04441d80110b40e081d080c4904002c3e01083d9030520800103481c0711050300080035042d580c5c11134800014690468004d030401c01e00090580d410318806c0a496403c1d402480140c2d6500e501c8220075507131182d04910000c2901a40700242c0c410a0b140c041c00300c1e0021540d00340303450f48003e824800034094504d100c0742c001560325904c08640c10210f103080e41800c122000e4072a03840c0381200d81d140305801d00c18120a01201c4000d6441d00d403d40c5130080c1004c44041401e4180742c4244006004129401000c0c400c2c58400c440b0305403822150080c0d9030400c1c0100210401c0e0b806410800503107200713200c0009403650b0302c0313507901035443c1e0700d170001c0000c1800303030b801000c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 341009694 1250 341008444 341008501
    0x601050d0201050307020c100c050f01060602031c0f0609020304110a0e0c07050a023606010509040e0a06050a0b0a060305090601031103150907090b010c0f02040506010e1207060206 79
    0x3005540075800850304071000c0c0c03050340c00010700f410200f4842e0030f01c0d4024000041d0001d90500a008050000f52160000c00c0000d020151400310002e50741d0040c0000380310809450f03410314030340710003660041c0400c111100c024080565901d01c04c2009410885042c0d0700c141c10f19181c48500d10702140d54405441d01020161026120315103021031503000660221118403881003c030000d680d90182005421480840001040800c0100d001104a004243c00024440001403208681c1c00005950b4080300999000a6030381e441c0c1815490200721a0340548401c0c07030f00090200d00355290308156102802601c40083d01a640c1c0011405c4540c120b407110f0860f044900103100245c51002d090703080c1107004040b58292200012081d49109080d04e22802683c40044100a1074249008207223501c40c5c02d081c8590440d4061b00c0346903180756800c2c4003c0c42556201c00003043c603030080c1c0103003e40d168050000111415404100755641d0380f51f015450240c896240011a40c07804178555140c2c00b0207114102 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 341010944 1250 341009694 341009719
    0xf060c0310050f1e040905031b01060e070219031707090e060303040506041a040506030a06030210140a0f0203040b0a08150d02030d12090f0303050402180912070c09050403090f08060105 81
    0x1304c041d052944040340d40943c6403104100802d00400140041c581500da901e104420304001132401c5480c01c0d440042141d460104116900e130700031403000a002e841d880c1c148031160303103031400311944120000c1003450030108006214044d80d20010080954003907a40c0040300341c9a0600b015924003407417250341e030b000804220a004548403240b10903640800308003024205921540083d072941c00456096203180c2c0d0f82c18042065103040402007000455038201130b0908500f00b414121688610a0101c0600000c190b0b1400030740c1c030070411280200703800500c0c1a220404030070014444c4030140c13a194130340c00d0004100e00f61031400e144080c2842d980100144505050154140e510008100c184182c03165501d0781030000c111514181e4003c14440d2360005802c0c40c06204200300c2002501005450703807207600420400032000200e84c91104000d140c065101c0c005894040031105003900705004a40c00c00060004043c0c0001081c42a6450722480407041601e0301c030440c0c0c0d00d800034842c1a0f400750304074021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 341012194 1250 341010944 341010979
    0xc030608031e040510111005040b0406020901020f03030a0f140610080a020f070609022409041e15080d0507110d03030f0504150b0102150f090f060c0310050f 69
    0xc2c2640040182c2c0800e00701643c43c0b0026800c2842500e4110103d0510f04c1510804e080a009002c1d0030740000c04104460b0407d85c07510141500000c00c003c108560005440103075030700802250034003039805c0c0116076903031404a12900c042c00319141d01041c100c0c184421750030308441d11032000e885500040c10703004034400850701c11200400701401800c2201da003007007020784040b680c030000c241550054030040780c1004c00d80b042c0304101e2031044040590000c1c2044030040088803800720380342c01c64100c40105d0380c101c5001541400c0803108003c403510501d0480565214214a90064116105101503680340b560250080d902485510001810030003140c2e44400913181c4a82411140c5001c0c0c50001640b100103615001114005c3c2c2c0e09440d0451944c201100f040790901400c40e90038800e201030000344081c403406203d4840042c00d5901c2c03244d20301002402e03102e010400d50300060704410480d00642460244000390394800c0e5500e8422192101c004142070400c148004000300014080400d69200c000a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 341013444 1250 341012194 341012227
    0x403030917030901140f0f152b03020c0a08061f030f0309080c0a080c10030207081303020a0504020a0e0909030c0304032a06140f12190c03060803 64
    0xa0484001281c100d810400225000203148038910907400040c401c40b0814021306041320080200341006581020000700a8078200d410303800c10042030312003404440d004001014428516603454403400c0281100241e0340312103880a0740240240c081c1c4600f0b42c061801d11195088500074685941e00070f102213070200c81c5c0b40044000c900381401c00f40000644a90702c504c3c0340080c3d0001540000c6d040c2100303000040c0309000483c1d444004407001000b1318a0000040d44030190000c0c0395204009600344804c115020b50100c03078140d03601071006543c40b0300041c250020750390039000503802014100c3e000b25550a0034400c070bc0200310103480e0811400c49241c200903d9500085c090750143c0000c1c40301900c48002007010744040e40c4140380750482c51031500c3e01d14810300d004854032241e500d40b2120421074139801001d101140c4400303010455641090040780f40940c821080d1106400707444900300003c0662031080d031401160000028440003c81c06030450a0790b1441c01448800c0d007007000f044d80b05000028 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 341014694 1250 341013444 341013461
    0xf030201090209042003010b1c05190b0103032303060d0f060f06091503020f090c090a0b0703030b030d0e0622061e0f0207030206030a020c010614030d080906040303 72
    0x2001040000d80c9602068000d24140e40c200c03117030b202c0d0034014005065002101e4911700000da000b00a82061900051420800c0000700107420b00401c0c51074060110600070f42d401000c403920601007013803441c074011a000c5c4007448180c002951002e0130300004005100080d010750a440781290031a1100402c1010524420808480d6109800207880018905001e000108002c840d4001101d80c98520f0050035a43c0e2a6444240d04101a40031300040e0f90345900321900c20000e07640302c0c401b95078410500700c0d10b101e425042580072100385000501c88001000802c1c18900c6581c0900070480c41d6014156101c4030088000003080314038605c0d100314107004019044080034144000314401603080c019103070340d145401c00000103403000500d040f81500a001240c21004a10385080b01d48207510000b5140d4440d404001d02c504000004222429001e8064400c0241c0c0c00c00200324181da0342440e4034030030b00c2401d001d82c043c3c0180021030304800e0180107194464103400c005484a0303510740c2c1e0210010300218 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 341015944 1250 341014694 341014697
    0x406020a051b0303070e0603040812061201020f0d11091005090d020402181017010e040812071812020607020d143406020a111201090303090b130f0f03 66
    0x2070040c5500c20350803070444030b04460884003456481c2070015004000082c4c80561038002c01c400c00906c00007403000c200b1540708000c07100081c0101c2c0c48240c0042c0013031103400840b004035800030444441300118100200010305030001c0400240c0d10303408425040d4090600e00030703802a541c0c405c0b040c02a0142c0c00034035030044010504d11402e00143c0c00501240c01ca85540182145c0d80608580e40c1d0814140310428a00d650900c2e0380c0e00042003c3ca03540c1c9001c1400f070002c42c0e20403440860200440b15086d52501111200c01c91594a803802c0000c01c1040e415242032000120a03000242aa804084c9850385940243c480d41c500203103502801544ac004200860b464076040200900d00a002d21007500c900352050342481071906541001c003406007100240c0d43c2003c155503810801c281d000900704110301e0784882108403005110b0001030703200103106c150134800c1d401c105945c0d00701641a88080401442000120f201351294101d00741080d10030b0030f006042a45813407584004c03030002c04030407180d42d10a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 341017194 1250 341015944 341015947
    0x13060f1b080d11030115140337050709090204053607051207021612020a230414062b0606030f020405090a05030a0c0305040e0103050a20090406020a05 66
    0x2004035040c0c003c072030409040c08801400002e004030001c1002001510744103c12184040744440544006005900c10205004541d40e241e803500c0c8071400c0084a41d4900c01000f950414058090301080b078806000501119000c00d10b1813492003070318207440700901194410611100703002c841c01c503082903010031850001c0708070f41e0000070840c8580c400e440315034079561070302d078540025054403030040c100c481550090140059400c000705020012507606044031010041c250010403130314003141d005862039044030138403450b40006050580640c0c0d80c0c20380e0100031301e181e18107020042071401c1d038401b5401954000b04c01030f09075142480d1030314001075039142900c01480781d8416048a01a50045500310f440000350340c107614280c03113001e50010210010300a0440c441c0d607215224441d01c0d40050074040c005040000b810700c141c09440c09044048000704880d6183d061659a44501d01000c9a81c03210903e02c4c0c0c0c80004d210313500c000c154070300941240034035104c6646031806500010b2103038080000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 341018444 1250 341017194 341017207
    0x8120c01060f0807030b01060507020d121206060905031911010f1e03050a0e0a050601170f0105040503030912040b0d020d020904021201030b060f130b040905030301090213060f1b08 79
    0x102d01d180c1c800142524001800e81518501c0c003254800f1050b80041d003070000034030010000da2550203030010b010f9030203903118007490210075080d600b02c580101c3c1600c0382481c00c031f80452032030380240302e000c20f90b10120203c5d00c105d040b1590008140c4262040181500300002c4001c01d15401410480301d44001404c0c481c40000442e2190b0000401c0100c5502c00070703449005008181030b80d4801c85502d82081d40140004160985445540c1c400602c00c4843c0c0031484c10054244403400d00c4420300341c005442c024071a03420300e0b017406990390b0015a0b0700440c4d0300501e18500c01d110001d800b00c03002ca03150300c03480600b0600703403240c4103000b500311032100205641c0800c201c001580c1c40e4030003000e1940c05201e500d027855040d410043c80010000b007103580aa07014941658060f95000400540c09040c2c0d04082401000394003c10086d0900140040407840048004900845c5e2600a0320004411601a01410303545140465441c40c02800c0b038004101c0380300c800b011051551581d107080600a105061a008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 341019694 1250 341018444 341018459
    0x30e06030c0310060302040803181203040f0305160303021c05040e0c03090705061626030108031216050706091106031807050d1a130602030a020a1808120c0106 70
    0x610440744110850310010420008a42c02412400a00450300e0110f052030f0800c0e40242d680d202d096280da800035214081d030000c50f9100c544812000c02d2100959031115696640d000c02500c0c00c3c003044419008000e60700035076a1000b08942c1c1180d4056004020381c03519141201c1d25201742c10b5140782003140c200000300e01d049001c4600383c016000303500f40300e58900c2c100714002c2c10a0035075000070748214010407200510b110081c050b00c0c0f055400100c100d00303020001140316907e031250a808040400c0c003100014041d2008000741c60b1a480c151008006070b59101d00410007104240b004c06c1c040741d01400a10003148150340600710040c400c100310a050005200060010741007121600202c9614400c80304010f8424001c05008190907a80080350b80442d5881110064480e5100c03038403c0320400018240c0000c071001201425049001150380703041600219001e503010402e524003181e12040148848a0381c008804d049500c0c0c4000b80000c80d84000150105c2c0d0300407101e41c0d11303075900c0b20f10108444 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 341020944 1250 341019694 341019697
    0xf040509090f010c0c0b0604090c06050a020703060908120f0601020316030320030a0606030510050d020a0f060305041e03081f0e1006140a1b0830010b0705100504030e06 74
    0x94441791242907220301c176032401c41c14808000b8045130081d42000800d40005e6426045007055801d2810056121203282504030720b0310000b90700c0544041e040048100921020b04010984443c120051a040780d40b4590710b455001e40c00d840a50050748200005c2d150022030311140e44029101c0e01c0c0106540301c0804c10151109468107140710803c07000418010119102d20540e0010515402c0078016031030400345003041000c0a220700c50042d4500011402155a605aa4170140c0150251505156103807800140140707803c4600700d4a06201c44407c0c9084181e5011a0b0205030f41a80d65604a81d1841044070f03102680501e0302c4c16181c0030320303c00b00355284141d840c148900030241c48201d0786490703d41d0081140d1042107420224000801c424106a03900c101c1d040c1c60148080e02c2a40b2a003100c0c43c0c920114459841040100c030f810300001700074114900c3e00041402c0b821414214640d807110705d03000081c4240c050090066001c2c0d8580e006000903600142d0b4010301a0a00c10851600346002c0340c0103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 341022194 1250 341020944 341020961
    0x20403150c020606010905241306020303040201020d1e12020c07170705150f0c0c061c0f15090e0703050610060201050c0301030812130c27020f040509090f01 69
    0x145500c0312011901c0c03507410000c1c294000801d203007240d0100c3c03a2202044000c0100c0c02407009034504ca0240c6000142801c040381d05100400e1324400c1450381d41c0a009403640c0090360120b005000310060352440300d2191254080d4081500110341c2c07160541c030f5041ea03000c0c084400c6400e6043d001c0c041080b10000621104008103000c006543c4543d030015200c0c1c1c1080102c1d003003588682c0007214802200692039058841c0c80c58050002c40ea903550601e0400c5c81d060011004d55800b44000032021030300e00d403507002c01e0000030f20a6800e103e585428207040c4180d07201f00b454158150710302041084044240c1d0042d903241c1c5100e5003515882501c940b141400c088044406a00c3d00801120820519030709105450384450069141c07030455045aa8421240c0701d045800219400c6000224144c0d141c0050000545603002801c0f11308281d41c0c890341805498a40e2685202500d14540d10842c3c0e4800c1c02101d41303600c202c082141c60541020208030304294050648a050f10070a0003641d9042d20074400c0048 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 341023444 1250 341022194 341022233
    0x171806030720031b070b0a05070309030512270f040c0306030804090203100b030702030d0504060b090405100c180509130f0609061a0a06030515030303180f0a0512070303020403 77
    0x2c1e6405100040a1061034204880c2da5651004008020f03a403410801d5640c40c0300d07e444e1650b41e421050030200e0b00062503820191441c000c04d0125000107050078014000c0d178460b13082c1c2c0d0142d01401054001c19010b40040607400040c0c440300f001c100c0c6000c0d84005200b208034200016541e8036610307440c0307460704540c2281c174446900000340510420b002c00114010844922136070f00d94074019000940b00e0085000c0914102e403600080f500304444c94000d0590307168041d000341c10915080c00e00036620700115114070040361410248030b84241c45800e204a840c0a04661010003520300000c0c480b00b65801400d1700658410861150002069501450300701c5004010204030000d0701c0c2000c0741160f080ca2200046800350b1000b00e41d82e902ca4002c00021640b0604000516075a000c02114080a000005580c1030000100f0030500c1c01ca12014a42d12508040849508580412801390395020340030024006a003c0c6a00e141c3d1032020710b0040101510a29000d818140c1c0d039503403004040000811000f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 341024694 1250 341023444 341023447
    0x131803180e09070603060f0305030913020d09210309030e090414030a03020405040b040902420408011103070207030813051003020913051302041a06040602070317180603072003 77
    0x13016503850f014481c0580318054441d00000d00d150fa40355074911400d020540601c8402c034400b00007076001d42c1900e00d8081984818170540c0c1c41c070715104210a00900d0341c02c01d04081100e091034150301c03910079212035984c5070311482c5810220100b0040c0d0058000c01c1180e401100c04e115114035030040c0041e0100c44034541b4056100c1d410a000c01c004d48050030b0b103550056241640c410050703510340c07414250403003844020440200110030303070445030265064100c81c940c0150303403211017025070300000340b04407000c0100801c9142c2d644000c50044d0710040d646503005030312006050000c201204002c1040d104000c001040a980c0c81000c0350605c22a05001d01c0800c1d03011a400c0f04500b00b100364440c2c004038810080140c0d1424038058503001e0300c3c800d8080c0c00340daa10700d440c400310a60070058040000d0005c01841c2c5840d03491100a6076811180001c0b101043d03904035045505850406540f080e084450008900500400600c042c0d07820082c03201e0200940f117aa98101c140c41c02e00ca845010840f0006103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 341025944 1250 341024694 341024699
    0x705071403041d04050d031503020d0c030611120c070201051207030605030601090c0e0d05100f1e06081b010507030e030a0c030c06090609080a06090c0e09030306131803180e0907 78
    0x30360514240486506c107040c03d11411b0428112009030120680740d0494020083e8411030502079080513440d04001c005910308000401c042e406140540071403001050340c06120354a00c7c0c5002000d024074070001740400c50600c445482d00b50000303106640030004e03180c009038059035580042d1500c1c030f00782e1004070020780c0c0700703038140c80c19510000c07054a0840a6804400c0d0030480d66270142d0368000071001c0c51010303540e070b072108104240e5600450440c05020040c9002101020b03521001003000e4400c4071118414072006d60144514420b1401c504c032816100c0301d04180c050b850650b1a4402d003160254540140c411482c00601000f06520196020312101c81074182005800b03488200180c0010081c0000002c013040014000150000c101e41e10403008148082103242c800e00c0d0308031b55008071500e541c2103010003480c200d00001640c0f1650003110345160038068850880c044851021113038001030702640c11503001c42d00074150501e0000880c000f10030543d6480b1420a180c00301519150704070340118408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 341027194 1250 341025944 341025953
    0x305060a05100f030c030b041104050306060108040807061d160302090612061b0f0424080105030a141e0f070512030d0504080d020309031c050705071403041d04 70
    0x102001d05829541c90010648214024060006041201c0101a2101d96881200d880790b0420720903d0b401030420721041301e003442c0c0303554107404c9402868041c7c4211030003d2141d602c6a0b48090185821103001761802209448000103072220001e403501d15505c03211802503100c0100103485104080b140312110380d07403d600c1040048080039140510484200001c03014504002c12043c0d00031030510b116035461007040c0c86140c0d15004003d411454840040390006800039450340600020382800414841c00a100800707031080c0384280130b41a09580034002010026000c1000d1a40d0000310a00325440740c009800c1400b800551840c1180707403900002208854210308020030380c041c00c0221812081da09001002c9507907401038280e0400056200c40c00305041c030000300229100320083e268290350720700e0f16081c00d0350303654000c100a00e03000014101d0540c04180700d22400d4061070503031341c800d0714141c81c5444500d281c030351a05020905002c00c100000701983c0b540f5054000141010703480740945880d060 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 341028444 1250 341027194 341027209
    0xe0112020d121214152b080307020127080c0a0c0f050901050f0f011d040c050309062a0a090b030103030305190b030703140f15060415050a0b0708120403030506 70
    0x2d0540c1c0f5048040c4106503011702c035143c0c140720080e180c0c46c426a01411101d80d00c0003204181005034050040d0002c107000c48040103500c00d920940081c02010100140403ca0920480b61202c0320f40580c03000c4000260703070074010f254443c0030804442071010f02e41c540c0c0003a51601e9102180189650404121a04091103902e00510007125403100781c0d07881c01e0100f0303641c0c80050903590412050880101162800342003260002e40c0c05001084003449030000a480303540184d0300050507101d41c000084040310000003551004000902007106024000090102904108100d00600c48005000f18510312200e014600a50203542d001c50786090650300222180e80f41c05951005078240584100c003914005409011250310458030101c02585036810b07410004110b540207014001c060f0641c00340720000b4000d5010b480121020003224201c0d092024441d00b0302e2090541040640a04208905020015020300e5008a480f035151076080e041c0b5800300c1c0400c071800c07008240e8500500c80203081045 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 341029694 1250 341028444 341028461
    0x207080f070b0f030c0c16030212030a020d11010608010f0f051b040e18030c0c0102160f0b03090f030c060a060b030f1306060801090302030d0c0206010e0112020d1212 73
    0x50141060904040250342d45105030368680031200000804542c8400341d0001300e580c0c001111040ea6455640d0f00003403008414903100682c8a0f283c03040881c81d0b2440d02000301c50803010190010b08c0d403411007400c01c0e2066181e40c14852640e542c2c0342c1000913000d60a00032004620700c40f0000013801e5040c1d4800c602107400c06088800908049402038074030031140002c0f9006c0d5502603e000149554440c02d0001140b00b40c5e1001e92035000201e440d090144000981e040c01040980a484040200400c3d540141c102441607640c410303214030041018604490045411401c09000c0d22214180c80290f64510b901c003008000151348032100b0004400d030305208807001f401c3d003c1030075459401c0204031125140c9024141e00032094101c40301c107041001c9a8403000c02849140000d01514030982400794803a0001070b280032642c2d003003441c55440d9500c0858680d040c2c4540c60781e1240c07a81d00f00400040450f0640c2012030b0420f6250304a0340c00708482810315050f0446a0340c400e0b10030400080f02c9000d6402e080c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 341030944 1250 341029694 341029723
    0xf0506070509060414040f0e0d0906031a090405030c030c060f0606072103060302030f0a020103180c060507050a080409050a0e07030506061201020f0d02070c0609080d050c0c03010507020708 83
    0x2d008501e000d94400d0225003c0740c0100c3c1440141d5000080003600804550b98030703061607031520a94030326607400400c4044031403e0b039840d4962010340c0e41c40190107540c0e04042c0a000800a03655032100d44c0707032607958550000d00600440f4200011030550625585c009605401143c0c4132030b04108444445106040c2d10882c251001802c15002c0d40e02c409200c40c0a0415821003218800d00060080c4241c1c8071100843c0c0040455900100121807507403222845c0d80c05a0000b13007403400c0341c03440010303105e101281c050b40006494111403606000311281e0700400c00c125198012900c1c0400400d0511000d0005401d41c51000201810034002000c22107030380340500c1545801072030040000c03c80c0810342d6070380300b001915a403040310702505000340207110b007041e00e040c024404611034003582900d5000e0503d02c0d21906400c0b82c0e880d00c41c4c10654804165201c0c0a8160340f2030250441014802c03409880b540c4a51402c940802030304100103429240100c5401005900007481000340301020041103c0c0c51890 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 341032194 1250 341030944 341030947
    0x2007030507120f081602030c12040602011415040b130207121b0c050405061908010510080601141507020909061f060e060a0507020a060e04050705160b040c120f05060705 74
    0x140303c80901055001050201070000700300900344940e000b4000c440007805079500f95807c60341003d0114826030400d005c0c0000662901d044100c800400500d11030003080c40e68151484401c1c41d10810020344a02004c0c2c9411189100040640c150b00d40041c0405c14030410320074407d50020b039001891280c04459901c0c80450003806000402d005004410a9640960f400b2920b66104804074440d0450610640c00c042010640040c2403a01076000c24007400401c8000040c8581e5003070700782d540f40000c1c0596078a0750f40c441e5140416103030950b0f44500c0d4060b41c00070382d0b04004044d0000b0f100032800701d0342101e8035081a010800b581c11180e1103154045002e0f00050b140341d04200c1e0003131001000986540c0510703400540055a203010b00142d4400690042c0110942611904c005003081c102c41c0c01c590282c0d04040c08251a240948281d0703a01c1041d10b01c10080c20f004503203600000390000ba100b903484040700c2d400030403c001003100164015005181034407070000c8502d861860000f000b0102410030a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 341033444 1250 341032194 341032217
    0xb07031808090405060307080703060f0515150d1b0807020c011107030212010603061b0f0e010f080a060f121b05010c0209090f030417010b180109200703050712 70
    0x460002c1d6000d40c84241d800143d81d986074004a450103d0310303000b003400c82c0304040e0000208040d03a00701c0e10610300521400d0000e52210341e00203d4802400c14410b900080144101080d01c001d4406803251020340c072404100300c0016250240940e6080796090000b400c4601000002c94040050b2072000900b0705c0e203c54000120f0740001d40f15021030000030b02c240041072012207010025002280a5a0004004c00c001c0740107030541529995240780d03050205101e0315080140501601090031a00410b031111080070358510000ca892020041c041c00c1410381e07606000c07440e081e0b1106140f02a101c10140055911041c2c00d18060004200041e16014404140c081c410740c0d81c4110401034040e416940010703191151840a41458448090f6051510003c20300040512241c0240458503440c90001c00200c0849414011030501c83c42002a608042d100100026030b41035000b8a1610801940a01a00d03482600810180d00001c01070f030001d0408900c0d0011302c01c200301c0f55490b82d1001c0c00c05111204 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 341034694 1250 341033444 341033453
    0x90109021e011d1c02040e03030f18030408030f0307200c040f0b030d080910050c040e070813080a140f07120f0206070e0a1707090510050105040306050702190b070318 73
    0x920281d101101e10740b119180744111b4a4680254200d007800c00e00b6a51285820000c40349140f0313048070301503485070880340414141d00c030100c02c41d010350b1030318400f035890528089a80c0c0034582c405414882005041c0710086103100c0003801c001c1000800301c0182216024100800040d55070740107442450700c2c41c0c040c0d03a0405650025071441400c015041040090382c4000300c0b50b0612a0420460800c107050508004804910000400a9500b203d00140003522007400071121480d04440c83c0762b02042c600941000704003808051300d40341c619450304001c8507180490216850300a10070280c4c24410200e1004200013104842e41281070051134a412032000501009648850140c02e1070709006010b003880b10551500e400100150401400c01007400032004881644c80b4007511420500c01e1400e03003c2001d5403400901442140c0d81651418241411601d50744010174001d401d92040d0701c01c847c8070100940000125200550255200494034640064090203861407654426600442c2030308034000207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 341035944 1250 341034694 341034709
    0x1309030809160b16081b0d020d0507030c030e130c03020d0c020d08040b09010b22060609291306020d0224010902090d17090a0e04080a08090109021e011d 67
    0x89141840c80003801c4d4140310b1403500c518614261048555070b13448003011000699040c51440f40e0b802c0700d59480442c44100c03224019184010005103045018030003007440b03242c0d19003907018010601416000038111080490780241c000c0c0000ca80c0100f5106580500ba12600010301c4850002e1701c8030040c060802410795000600041c0390040100110720030300800d6106089200001d0501c1481e15503800c0e42c409240100c48081c040a42001404110740e440345488204440090b00a81780010084280c00140203010201040851081c0700303449030341c800644101c000b030203660040c0c46000c01940000f418030030503044a004000b260307094a5000500d004040781103c20824006071101006c00024000c07200810029100c1043d0400000300c4c50031080092603240300c21a0300c45072150307449002c803050390421100035011480038041d10000c5030150281541c80100440001103283c010b60010b198900c84803202c0003600740c208401811542c00c10350f82c03030308407641c402544030580c080400103150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 341037194 1250 341035944 341035957
    0x2031002040f0f05030d1e020a05010f0504140c0f0f03010b1e0306070905100c0203032b0b012105090a0c1508090102070210030c022d0607080f0103111309030809160b 73
    0x71120781e400a47c0301c070700c01e00c1a0000264020000d020803801e0700c1c8000d020380300c01d50b0291000c64060411440340100054514242c000c0035245551030f140c0442000760680981c4100b503015503d071a50446160b55100d920b08029044058401a0300c6402041c5850710500419110038464030700000e02040c1d036554100c4401d80c001c3e1414614942e0148042030450203103103c018040281440601c0300c540c0c2e10b504040803003203000f10810000e4131450045901e10f081400040c4110f52010040d80c59190700e41040c0d601c0400c4d4401c441540c40107944100281d2001e500400350215403400e0982802c3d0320481c0190010071410007541007a2003500050504200b14032b2040034103655403010381c800c500034030176440d001d42c1d850600d00703856080d00c60b41c01d0420f20f074034403c035103034043c01000a812030f0007500d141d401503100303c0d00c24070a6800c0d41d6a119420481040b0341c0d0340075805641c0d4081840c414061190040d120b80d0311503206080900341d0a01d404050701e09d152804035480c8060103032840c50300a4840 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 341038444 1250 341037194 341037227
    0xc0a1407080705031b100207111e03030409020703090905071b210e04060e010303140a140c100b0603010501121d07151205010308031302031002040f0f05030d 69
    0x656412030301d00090580b041a070300904500000c580403502d12034060020303107105c445c081074440c0061062039140480c4280b04008082080c0381240d402c003070904c1001e42101d0400d00e02809101c040e4480000c1c51600300c1e9102c01741e1141c00080803002c2503032180e81e00000700300b554400d000d17500f05940e010744100c00c1341c0d00d100b50f08040440140188080c4559a000302c0304016100040500c2d1240e004040700b421011050085080c081c1c0043c04148070310382d0303504036a010b58a0b100d00e00c1c208114882180d10000e510010000d41e0b4112103100e070001d0b8000d0901c01c1182006100e80742c800c1c582042a03500b02c1d00e51504c5002d061004100d40d1740c000702c110f500c103001c200c4002500d012181ca03010084007242c2c2c030b0b0342c0144208513002c218072031042081d10101c2c50a49440d010700d00c1c500c00c15020764500b4003004240324801e0000caa6413413071100002454510003020f95414182c80200c01c02260459030000140b41d05000c2c0c200006500740003403501800d0207a018025000c0700030005488581076203011007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 341039694 1250 341038444 341038447
    0x327050603060112050c040911090d02060f0708130305010507031e0b030f0708030703020f0604030c060b030109060e031c1b0e0a030818270103061802150d050c0a14 72
    0x8000e60301ca840300103069010100200301e00c0c145041b049115820034041c0307000e00d900d4408200b66400e600c1b000c2d601c10b5100201003090313111569082c0480754010010101400304203004860010f900300c005000b83c044103803c624581072450400ca401e444020700400e080c18540500d02c1d0910b9441500111900c420f044040341c0300241e0400700b490058200300c4041c050040c00404145400d01000804415010f03074200c03141258280301e010f4030b89505413801804a0b40844117030700001c24982089652110040001414070704507207604090354000c1c035007107106400001d01041103002e5240034610526500d0030405c00c44801c2084007903c082d0b450100b07c180078004000c0d1181d5616080080d000c0d603480520980c846403810301022503030548108003841a030240d00d9149090380c0703401d040280c00d5020180e020b083c1c0d2035500e0303000040141070a100c2481c1045440d05c005a1501107140058141011501d0380d140d5100112904132400604140b2100da000c2018071400d691005044c1026100002030381e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 341040944 1250 341039694 341039701
    0x1503060d0615030206030f04061b020d0f050d090c050108010b0f070b0402041d0d0305180d181e030c05040b0d0b0606120112170f1e120907030327050603 67
    0x1212440299100030760041c5e00004200345c1960814110303014520410017804000560310807200385442059520005030302c00c0500f441d040d8441c102003080c8031154200300d4603206214050800381c1754150700c242e03101355129500304540c2d41d01c140801d00401d006041d4900700290541e200200f44101c00c4040d08141039000443c0941d0750300c4d8041991400724130400503054240d800d0a540b140200b28052011030300e0000091380c01a460120181244550301c00307818400e050940070780d42da1100303080031041c0301e10124000c108039028001d200e02c0003440c001d050600e640fa40c5010841c2c0d01c07443e00602d02a0b81070416648880d00c465901101c090f6200424050954034200403408030700654400d0151080c0500c0001949200014000c243c41c1c05040110801c10440c201580360707100303030444c0900c0a0700c10003032501d00400d107185100e8059041440f07240303010741600c01e01b040340c00700b540c41e00c200d50480442002095000400452584020380780101c11044008105100f64210300c64680500c1c0e002001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 341042194 1250 341040944 341040971
    0x5030a08070815014e110901050a140309030c06090109120c050a020604121a06010518010c0c06110f1501050d03120c0203031803070215070516141503060d06 69
    0x403d4000348401c5880740722a0507603505e002c60045071860b407140300c9820703505c844420b07815070150080180c01e0250351460959003400442c1c490340085031450410500c0861013064070406001140904039035401540c80340c070680c2c13505003042d0001d0141d0013030340c3c074101d03d6000081e2032240011035040503040c103c00d051090300f401420a0614000207601040003d03002c40e00e48800a80c1d0080f03280950195014020f11942c109a44e0310260741c0d0b01c0c0491001d02c0070f4448484003a0707a0f800d04c4141803402000c4103a1a40d0340e40d880e9030b050741003c000b2602c0c1300308190258030200300c0090036500b85001401c1805050340501e019103018003505000d20040b0380c0000a0500a0008a0340604440307410400400c11050003500c80c0c1041e5140b1b400252040d0303121600c0f41001054580040d00140082095428038114808550207020103d072140165902580e40301c0d070300819a401008030701040071200030864104103007040b100801070038007203062040c8103a64480c0da03100411164050b07000180444c3d001d00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 341043444 1250 341042194 341042237
    0x81002031b13030b06030a0b010e070e030a110114040f03030302030c16050c0a0f031104051806010609150507050606120309060a030603020a0b0408340305030a0807081501 75
    0x30036144801e0005000b10302e1024008440d040300d01420398041c40e600c1d20400c0544402c15020041c004000c202300600030317070745850a102c0d0010030741d09101d4003200e00e2002180c1419542c0e03106560104d5245415600c551b0003c000c00c500c1a440304a051926007841ca0000348003000340006010194040001038028484c40c00703c9a0b038158104049204500381c0c64142d03913905481a03401d01a250b8060000340080c58000c101c4103880e4024848070079100d822050000509004143d48018506a140c4030440541486018040c084c1582c610304054104884004d04900740001d49080040411080000c500c000c240c054004000703c849407200c110805800b031950244069583d40000e002600103039640d00750b4440b1040300d10a40d2a944a280c0c0d4000140c040c2c0070300c1c4210500d41d0440c0266000840a03003145454103245512880d0b01ca04a81c03244400f81c07407030340c0c004a56a07400066400700b480e40107080d072540b008081c81c008202d450020f2054403507c207440c00d181d060011500b66044603811554 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 341044694 1250 341043444 341043481
    0xf0d020d06050912031f06091a0c0c15030a0b0f1f0207051e090105030309100503070507050a032609120d0e06091606030c0c0215070c03080d0f0608100203 68
    0x640d80798403403c1064003900c00d42540c8200340d030500281b0400095180c0034251301c07004c9686440c294004107400b544800c805500a04810350107002d05e845102550b0b0b030314010807408281c0204d045d41c40380b600403440341c110307600b00314072901c07072014018114510394844643c492403040103090011140c00000040c2d1030070055801c025800010a0416116411204803800c0f6000c4101d410711007599072070042c5a101c0c481c6001051b081b403000d2820010581c001d90086030041082e2130964a8841d0580320329052401380e20303086000840620403185031400130881103034107080e0311070016901d007042105075a03507081d12080b00e00d8001c00031542680341012a80199025022181504e40600d0a120b00d6a2205001002d0104041e9150f00115099200b8407455403413901d96207072020380703010907006c00040211031015a035603880204a10400500307000d01800045200b000420744603480ca54441c002d940400c0d21030702003035207004810800102c00188811817084e1144006a0b60346605046140c03071080c09 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 341045944 1250 341044694 341044723
    0xc03021611030c09040506011707080307061418070e181e06090607140306040b0d03020d14130905040201051e04081615120e1203060f0d020d060509 65
    0x389640018040ca841201da00360700c0c100c003640d0f206281c60007002020a01030b9000361a903070050740140505484041c1c050344040d192006c644c8119034401d03090340745074001d01049907040e0310b03082c520781640e0030b2001240e0007080c0c280c4407a502c07814401c0010303603618181c8901031481303174a1004100b405103e40e401d080d41c00c1c0d404060b40c0c4114840f80720307140503a03410203010f50b0300e00ca08400150320443c045411801071241c0c1e030b5802c0c0074011a05500d421500301511036907000d99190341104440c1d44500f50184080e00c250090402468110300c082c1152400106407485d4035400c028205644070108500403d039000100d0019083e1520300040300d55000d2482000d100060400e441d0018140e9000a8421034160303600310b402da101d0b20480c403a80d1008910800503900303801d0300042e0b499409450491001460030f0000660a09940ca000380340c0081d003a250500c0403000028006c3c24100841101c04003403054800640481c2c150f4048ae00c03001c03000b107000d0110b5560f04041100c000e030620036184520481c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 341047194 1250 341045944 341045977
    0x1809090809031c09030f031209030f0905060a0903060218030307050703110402160f0203120d15050a0803030402120a021509040506240f0909130203100b0607060c0302 73
    0x500d4020032581c00500c00034400c0c411880c8034803240e108a20200d03540708165880070803151455481c4042500210811001c0c4111702c0b01c244c0c0b10300e0301c0b803080881c41800b940c0c8044e00c6002d11030014000c000b00b50410b5000765010400d00c41503540050003201160b6008034011303030711455a102d114000382c904011640c140030000702e02042c003800203259003e0302d00a881c2c803441e004041d4100400c030300c900d08007450028411810800030402103195441038500203001c1e6484049d01e14100c01300d035803140509044003035459880600c4c0740018000c0c40040d2000740e6203c90a141000751a969a0000400091040900300c0c4e440340008010b209101e44a0341c0070342000081d07481d01c560143c03140c0101c078045c0d011703070315000c0042d8140c0307084e940c101050304c4106003c2c0160002068034410750ba11069860600744c7c010045002140c031008980d07441140007600103c4005014410182800b00314045e41d04400e060406900080c2d65610480344500d40c0b128001034031749006007040d03000e80605068410318130725 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 341048444 1250 341047194 341047211
    0xb030c0a0207081b10080103050604030509011809061805010e16090305030409061404151401030b09090307060c1d1912030e0a06030c0c1e05030318010501090b101809 73
    0x51022840c002408100c03100005445e0031902160a154248000350107940008003060109020f10020060020180741c040f101941c005160400701c0d20b154050940903640e45c0c002c20400a5042d00c06003400560f5a09000c503502d400388070758002802402e6103205408907040c0a03c071600038210030008540c0501a030b81c45a80e03c3c0c05450061050740304509540200036002c0d401c5180600c41c40300030140070307080e501e613450501e000d40225404074094141415913034549a4440d13a00c5c01c04039849054858002d5941300c0749803400f8400c0e202c10709881d90134071119070413688100c102c408644030902c0d0165110074a020190038042c0c411541d03684003000e80d000e0300114905055020300f00c034508403404d40d043e403900c81d90f4640880442c0c02c2d100010000914040c0b05100184206003080c10903000385121051082103901d402e800c0d9441a100910729868500d0b075091110000e010b081c0c01400c08a41c00c10410b0110780105d84200d04c00035149080100a41091040381ca0751310340344001e415000d80400c841c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 341049694 1250 341048444 341048473
    0xa0c02120a17040503120a050a1422031a040506010e1f08030304050d090f0303030e030c01060b0c1b0607020904060f05090a03090b16020607210e10090b030c0a020708 73
    0x40c000c4c019640640200c001c5449040501400c5448103145941d5080c40d21540403800c50360710480c2711940500130030030410b18409802c02c14200e5940400200481083c03441c45c0f4201d9031180080c616000d08a082004000104901084c0181140c9010800011543e84d00d50130344440203024080d00310704d8449480c0130451080010142d0320441c442c0045031030b5805000f10548100109114004c10350084ca40c1c2840002e121340c0211840e03040c00d074112030500141080044c04c0d111241c01000240320085401c4940082c00c210074000991034103181405c08404001248481c0705d8000c02034054903404c4042800c01805070b2024005044985007001181801901140ca811071101c0c01e500141c1d60300350120300310019804984403500e599080301001c1c2d08540c24002641c00100f41542c00d04407921a175180121540710b10080044640d8a44401420714000c11a141a25800400401240c000d091000414400032030341c00600185c0b043d43c5403607a50b60f0072403920105404c03204890207034403c07104400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 341050944 1250 341049694 341049697
    0x12061d1503101d0604050631030c02011403010f090b01022e1a0901051c050a060213080c090402040f0603080f0301080613030e01350f09030a0c02120a17 67
    0x1000306032109032008011051041d07030f603002a03801410907001100403507036071420b0852310005030607c1d00040900c01d103507054034000289030010a8000c42e2400008104569001c0709545603504140035150955041c120340b809c01078031602403130752980d81c0d03101c92200681c020000000e10742d8003c80c0d0304e909103034140c900d420000402e20b03480c0c5045090181311003680e040c0303c12200c0102d102501e48680c5a00c1e0034100090074205003c0910b02001c5070031070300c02181003441400d8680d80249400350f0398404494401d0741c401d20641c0b1903089504410495a600d0b603c0540d12038003d030301185e01150f0031184c000000010526648000d01d1140d00282e80710310890114042c1d4101c4040c1010b54406030f032695246c5a4813130030510f0040c00100004100d29070fa41c004e0004020406190710402141c120405422509904221918820440400410002d00311540d101c82d40272003520041c608010103c48090041131807030500030706c01d2410b42c0008104940030000ca072400c0e42c2105211600c0f481d0883d100d10103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 341052194 1250 341050944 341050961
    0xe060f03011811040207261b030c0709054f021f02071208040906090f0c0302160b0a0902030a0803010303030509120a1803060c02010b0112061d150310 66
    0x180c50003180c4803034040c44c143c401d8601050308000e2100b490700c28a0018500c0d070308084d00486d00d4400034415021542c6113101084a40011040155520007070711720300528001095024009207428001000070341303680150003041c05681c4900321086c24009503424188a030380000c145410b990290034101242d0302001d020300c46103000b512414010410359004a502a08101f841009a0b1002c6800c0000300358444070344840d94042e802c80c90034a900d0703c0c5101c007a01c10650101d061070391200d42006414055114080824201c1c0c00d0462038100714800906c0c40804103500600b140701103400003828015560001e41c006a40201504d64031485484c00c00f400360420300040d00081d15010000d1030340600041c4002440d02400c400d00e05014955400303c0300d0b0b1408d07400340c0d4013140002e80000000fa80500480075030075140d80000ca115164030000400501c0420041043d0f10b0804d81c04202e03c4128a600030140c9204000b561400c2d660031128480310003200f103207590588510301004080707800c03030381c0309145 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 341053444 1250 341052194 341052203
    0x7171605160e090706050313051c09080124090c03020408010f0204181406040506031c0305150105040b040314252c06101206080318010c0c0e060f030118 67
    0x80d60303d903080020ba94818500450001c10b00800215040c0220f141c240701c0a9480b400842d0207003046004c071620300c10030310700109002c50000501408065401c1c0900412407205842d1039a1144001030038155140d514800e070309001c0d81e51f068400b4818429011140604030050080c8104000e1299a40c0294030902c950254a480240000a031804078003950b0b01c4005a00c0b10100e4648034072042200515015040c19030610907540d0081241d4010174401d83e0001c442e480000f41032504181d40d0b5264813442e0511410040308000c24091b42007804291001d498105450950010345a03a4151414804107400e0031050010154115110150102007050f6034650070420210710340c8107601d000440038180c11820905850380043d041e41450b0146030481c451601c1d1a01845201c8541d1200321020f41d000407103690000500305200b6080008c161920400c00c2c42d15034210010750311041c1050b4024010f40b10940c10f464013142140c0d503182e2081781000002002007040c2851001031203c1440e12900840e03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 341054694 1250 341053444 341053469
    0x1c051b030c0f070e01060f0305251706030f0304090509030f18030d0c0f1502041d04060b0a0e0a0209060904020f120a05150105071506080615060717160516 68
    0x64034446880d8040d0486503107858146c7c0340c200800c400e40191200905501c001c0c1100004030030000008844001010346940300c524409003007410000e100d001c000e0506001e0f9029040006500100004480850742c070003000142c103403102500c0c14110312030010004422400410800c0c003444000c940c40486000480440e401003102ca0070549080c3c01d0184060440041c02d81c4201c0403038a80c54007040f214210f000f00503d0315445200740d6a0115a02003915142c10b0040304000030408540b194084c00a000c880e000462403500306189074000c0004c1003a5012071f008500780e0842d883d4081946c046180050040d034840b221703460000540d80000c800e03a030000c0b113040d0114548845034030484e0b0140340254103241e0a14044070041d640740d0302000c411610081d030b10710188000540c40c41240c01030700001019100c05c0c1040184031042d101c0c034480d0180b1482040000030002a0001e441d100702d4980103807025100c500d00030203800d88074805140903000d40154981d91041110301d06031942070b140c13104080e9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 341055944 1250 341054694 341054699
    0x1b0d060908123301030e060703020403060b0906030606060a1107030f0b15100e010c06050115110d09090c110f0d02100b06090f1f030c0f021c051b030c0f07 68
    0x100f08008040c05080e0400c5501c0341c0b004110f41c0f20a0901401c41c41810045280c0282c2c4240d285000000c60700c0d8000a0b03400f140034801c014160041c83c1c44280100d40d10342a5007080c4001a440d1500580414401c950015081101178000c04064016410344400d4443d41030307a80c204120030300c007400c0c400c54413114003800280e5920012248101510070142200518803140c8805444a604026465042c48031101c0e80701c0026206011341c5018040004102140329440000540062102d41a2031800d4101c40e88010116501100000031110591000310720407074005010f542185070040720505501174507840100b03511001450011070b080c0c3d030f422925000c604034400700444110f04601540400204164411450580e11403216418000c20703190340701030400544d082d030b030f2425600c82010070f8803000b0252540b80c000c1034020464503140040e0a60480c0306c010318420307500c01618042402070108046181700c051490940d0000251002c595861280e031103800d5890404013203407025446412000b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 341057194 1250 341055944 341055961
    0x50708090a0f0b0709050a08030a030c051e070c05330702090109020a11160f0509042f0d03031a010f02060f0606090907050306040615021b0d06090812 66
    0x200020300d810100d081d5076101c1d42c1c0d8442143c0c40010304507604010984501003455510102900d004001c004001c6640d440c80000c05402d036541e460002040c400305111051440c02c585002c0703200d2030034a40c900395881380302e0b1500b84501d99803174011603080122810841c2c042c140c1105004c0742164008880324211884c1594211184150500250000c0d04480100700d40d910540103070608003080d05004002c84110034140d4a8211000c000d445003503021001003145041031100300c00607040130b856120f542d1400752940d103e41c1c2600820541050301c01680d001007810507088500e074000005000001049113400e008020342010000581020004001c00d80c480d80508014849980e076a006012282d48040309060300c89401440325030440010000314005550300f65000e449840a600c5a980b00e05200c4140300c01c45225400c00c0c01e00750802c443d0104625000a10f03040c1e00c10450f00c0600580008801140e1501503490008220500307008030201000804030180881650035000511079a544201 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 341058444 1250 341057194 341057203
    0xc033e040510031d030a050703081f0608070306031509030327020d0302030717030921091011070602010603140c0a050913050d0206060f150409051008010f05070809 72
    0x50395501040441695400b180203401c40395000c0301015068001e01c1c01c040c4403c2c11984451141c10000d01d000035a07500301600700510f2600b0201c0110295041411003440c0510f005c80342c000e24080c0051070001544403446500140055a4089020007818905850781c4e80030b400e000c1c00807030100f81030241c6024040740c5c501c40e0710704c0450b2751865006071f985540c0a1010203100c1c1d1900746c08601040100d200800c112003810f85c040d0b4064011690f0700e18145900d241044100441c4203500f00700b000c00d4180070b03081071041d1085030800b1035428000300c440300001d0304c07110a515405c00090040d03e100042468065120108482c098030314051604214051140c4814401c84030340d6000e50ba03442c09020600700703000500d03402002d410091000e180503841c0c451400c00030340c01c05001648940f00700100750511000840c2c0411054690948000000302ca0b0b1041c0c0c0900e00400c8011551040001d508042c07200300c000003851440000c000c4d08200804450140900701c5043c004684100007140e0900341c0000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 341059694 1250 341058444 341058449
    0xe0d030e010609051b1e12310b100305011d07050a0b0a05030403030906090f02120307030e0402030603030702130b010801051804030c02040f0e0312070915030c033e04 73
    0x441540ca00b1401041c02d421a00318501000c05075001c0d2001051b112a040000c0c403d08070808407150743d615202d10000429440d1810b41c00c0c01500c0c543c2a0303100039600746606901198403076685181e0b90b84545c04502501a41e038405401507080c0f1070b141c0c0400703201c840001d00c05141c01b4281c54010740c07a4000d014110350544100c0e0200f08040005c0c044041c4140e0145401c035100e03240c0881e45007085d84075142036590700c820aa030090100440d80341140341040901d000c183e804801746007007800700d40340a000007200b441d80b140a6500000052000e030343c14400c42e124903a00400c04106050b809203e0070040140c60f0640340030907209000450f4600c2c3c81e03401415207010005800400c1d9641c0d0340c084640702d5091404a030031540702c266000b1902c203580a04030801092600454803402c1c000b401400c46140980a00d09200d507281040c00360452a00000404290074200030031031390788402c0c04400411006081c40103105001c0b01005c004d0fa805144840c84195142c4003180c0c1d50381d807100c501c04074480d51 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 341060944 1250 341059694 341059711
    0x100618060f140a030f050f07050405090307110a030c0609060f0e090112020f2d06130302060310030605070f0e0109050603070c050f060c0705160302031f0e0d030e01060905 75
    0x190401c0041c0c00341642d64103034042002d0859650f00e03680c2d5951901c0d400d80010219036a4200700c0304c244602c00104406c0300244000c48040c00070b800c1a04215480c0d02c01d4480c040c01036035a402c1c15051a80358032903080c0046074461807403d0500d6480c03100401358186406180000341d44800c0160b00d45104000308102c2d008002c03d0b20f0390310703440e0102403a0307406c0240320300b281c01640240045c5019a03661600d01510028001c0d1420120800036034001f4201804003800d1140100344420705082400080e0003064aa040e030b6055981e07102c0720700d9141e210090740e000400690600d020041701c4d5a1040400c032040f0b8250312518554441c00e8015203410149001f0542c001c0020b100140303813548503030300758a0201d01a03c26540300d8090750000302e082c420102e4608240316000994203040200410042d04034143d003070b03031039544141143c0c0000e0325003083d01c58648030b940c000080d030040c90400303600009a84801030101c801c600781c41c03403000e0060261030003207040c1c035480e000b80001e00780f945001c0c10740f107000d60 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 341062194 1250 341060944 341060969
    0x3030a09081b03030d0b130c08011d040812131b030c06050309060c0f04081504020a0803030403050d0c0509090f070210020f07060c03141e1e06010804031110061806 72
    0x400403203c020714010b400303039901050f0450900c012254510512340908120341c0d5001c030a41c18036800e0000949000091500c01509104010105104400350f500d02c0da03003003c45200944440344401800000c0c2d410240c00641c034250b81b4030b0b800c01000084411a840790f41e4441e000340e80d0f030100340ca01e80411117100c201c94000782d000442c0301903100e0003002e045041054180c181034075440759510300030448040e40741c10300041c0184400e40c034207141c80e2401070600034029403652820b03540040050081d02c00d180701070f6481d08083ca0700c3d036000300195000b001000d4402c40c068036200700c40d80000d0009459100c0035029541d80c0000000544c0200d42c0580b407004401854514035903261801440d07044840d008040ea6002004d011310002c4d0b420500590002c0110310302215000c484060961010f00f218056042c000702482494441903015030b8004004d0905002c01da89908040d520559060f810041500a96102490380103441c0d02c0340b0140c0355034401c2c00e110039000d002e440c1c00715041d602419413a10708 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 341063444 1250 341062194 341062207
    0x219090f14250203040b0403050609060a0603081207032003060103050702070f052106090601080d02070e060603040c0b0301060c211e050f072102010b0112090c0503030a09081b0303 79
    0x30416089514079409204a0303191640e924880d0841f50440c1d0800c84941c0c210a0070302425130740802c0317519042045214204002482c50f5190504d6119a848040d58100150f00003083c0c0c82c0203910881030f04070b06081040038200c0040a400c03280e8011103280740824908070100e42d40a02c0081c2c4601030700d0b451020300307110324207004c03c0201044064001c0b01140c03614142e05410444248406406a03402034001c103801d5040003c3d0608003c640318803501194450b01c0c0803c10880d00c4801c554001c4001e5234406d9580d26613042c41900c0341400e401140506034008000140b0690084a681440e030107a404000b00d04c001101920012180250500004000c48103002c942c1c1490f403c4030b07041e0a0f050803c00d180240044204600b030b000007001391825580340300b6240742016110303800c3e07203140340c40c2c8020130000e0040b40001c0c04e00342030703c2d51203d20641d0b1418414200b211581010004d044010106d07a15480d08420080c11521140034011960003040c99251514405240804042c08002d010310306005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 341064694 1250 341063444 341063491
    0x1605031e010906021b070b180d05010236030102070b010b09060408160e160818031c020706061a033105010c110c0112090219090f14 58
    0x144a032500500d540e03840040c00003540510003445400641454490310205400c88a420100d40b80d202e2210701000b0011016090015040c0416100b42110f00f41a040543e06206009004100440080c541888500c18100b084052441c0d02003070400c00501452080c3c40c281030a03401180c000400c1018004010311407010300030090000e011003d80b03d45d05240c0e40f451914034012403040503403c40034201c034082c010a40d912080d5a4004580c01210f03040405090300200400002030807031050100520003500e001500b0300455000071210007080300b41d480140b281c14002d520101c411030350300f440c10303600141441c8002c0128200304480040c042c1190748540b54402c9010310001288402180341801303828000d841201c0c00d40150084000144802c9841c0c0e001d041520b500380c600c840e940c00012100116039000e18070f0303601e020400d50003003800714081c400700d424049800072004012080b0f60f4042620fa1465000082d090b00d04401480200741503c40caa804440c00d59003403a001c40700c20f0704d016102 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 341065944 1250 341064694 341064733
    0x605030721020d020924040507020a0f0311011a040b090103050a06020c070b210702060907090911060a3605090402130203070e12030c0a03120f1401050102160503 71
    0x180003600b90040070348558009450004100c031001000780805030600310183c041c07105940d003801b082d20100010f0034025070296640c0c40388240200100d0825002500301407250203082c0d840b0360000000e11032406018200d00c8132340701201f0400e0050785000f003954030a1a09680650499421070044c00340240140c42d1800a58080d1003400101d108000c0001741220b500340041110301d594070f110031094802c481071540e05030009440300046511120a22880740c502042050440300c407054001001e281a1030100910906040d40c2039100300c4c00b10b184100c4030b800104030320480111500e003500410b1400f01c00c2c5440051018440300380b6480c0ea5091049042c90138865810a000410702040503504807841c20507680212510070003d500341e2010b81c0c0505200000d00c24900e03c89026500f00b050310b882540d030381d50303103580090b00308a030494001c407a2161788d0340003003040071011005100e031200d080d0704d44440032020f2066500502c20141d9034801e20704000c2c2504c1c00d48000802900c2c0f0302c8a10020020321 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 341067194 1250 341065944 341066009
    0x503070203040f2705010b0a0c020d02030a0b010f0f080a150b0a06030b030f06040803040f030c080310031202031801231c050f09060a110909100906050307 68
    0x1540300400020841c0b0322401c0c40280104051340f06000d22010401201c0308006110401004c29802c02d00107024001c1e8042c1a15010941803810b00e01000076400000d800510300302e0080e40600a0300301010030700c2020501d041c140d03040c000e010800b00350383d00d444621041c0240b00340b442076001108076100007a000302d02903064402e20007000c5112000c2c02d00080c41041d10f60b01c8100440d6403452501100d003402d02c510b076050703580d510142645152603203540c601e07440010402892180a10481401c0601506084d11211b4001c1412616464002c0300e84040704410302040c0c4840c5c8040140341002d51000080360302d94080304000323108401d00d10b00191a030040b00c151482d6054200da4000046c10800c1024202d1200261010001c8850442e031141c100d800c040c0c0080f0801c9200020418051000188241c101c0301c242c40c0080c0099940100f00404d0041240850b4003c000409019080fa0021200e6003074070061801046015a01e41c10195600001e22802903183e803c132100f0006a41c1c9160098103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 341068444 1250 341067194 341067197
    0x60901110d0e04060b120406090519030f0e0d02100305072a020f0301020f19020c130203090c0f0a060e0d0204020705030c0601120b06091e01080a031101060b0307050307 74
    0x440d0549080c0c607007003100d80e40586000800554005a0500d880c1c010340c8010b000c401030083c84c20249056400340508020300103401c03281c0f180e03105420460700700190141803030080903001c0c403030647d8540100301e600c1220020b03000450440f40c50683d480e2050200100c03030350042c0038190304002c4a80c03c2c0d000e040000e18034414003041c1401c413450200039140040c64155403007400c0c1c12601c0640304001038541030212060090b0b2052044000802c1c0d0842259002c0d943d550f030403880c50504078000c038035010000701503503000384407001c900300800b0154025600500001c01640c890303140920a002c01100c100401c5988a44103550400140d030282924240070b0b0300103000140304c00520740119050f640030ba07604070b80c10b0f840014400001c80c424030900c0d0161140341d01800381d403100b45d00d07220707039040014000c1c0d0f00c50743c43e02c000704031071204064800710740040803002c80180e5a92030042c0d640310049408241d010580d0420160041201842650140c0710031040d4030742541c07a80c41040b02c65400c020240300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 341069694 1250 341068444 341068457
    0x402130b0306090a02130507020d1124010e07210b010306080d0203120c040b0403080d09020d0507080d031b1b0b04061505060c0c0f010c06060e0601030b0901030c05060901 75
    0x42074a052040e5403085503464020042c14029105004103071501191514403c0c1c034100500c0000b03640815143e181003c18036242e641d4411a13a03506040082c1441040011207004a003180034895009500c8d040700c070a400008850ba4441c203082d10902c030b00e5402c07140729160510805180d0003da5100d89081c00c0c0615000814035100c0d080c90b8900700703004c00035002591001c00c0000b420a10310303840ca0f80c0007030186042d0f070030b040c5013450796000e500480c000102030a102282d94006503803da80b00d502c3d2260010a1031045030140c0c1415500c1d012907000b4100c40e40201034118000a0080c042e01c8004d034100c1143c0c80440c40c001d0350482d16400c007140f646445050141c0030001003900d400300603010b60700440d4000303004120316540d1036011380c4a070310440c0100010311210000143c003241042803040169500d09108510000480c5c00c641841c0005000ba1302c0c02c0030214944840100d0140b04000a8078200300b4101d00804000c0840e109100003002850f09141c180580d0034400041c2106080c18144113 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 341070944 1250 341069694 341069711
    0x24031713080309090612070902030c0c01090317010609060507021c050d050d06140108040b070e030708060402090705090625060c0e03100c12020310030c080d03060f060503040213 78
    0x940e000382440d40203032007960011802c24850314101070402e800800440e0400550000c4640d21500c0700e0f42c40c0b06c0d06c010f0503408800a400200098215040840900b00800c1400a0f514000e00750303404402c040c15449510800102d03000b40144022402c2e80e980e52142c82c1071500c036900300518080405003420b0144003203074000002510800c01c400035641580c0310b82d6101c01618984038105d402c25846803480d010071482c03001040c3d030003c032402c0e0020f4026503684500e0340e4002c1c0503103203140011601c1e41c25110b10000050742150100b8001d0186100301e4140c0055122800c0464041c080c00c403000303031b014604018200c20a01500c00400c004540c03103d0081044800d43c880c401112020382c4200040f030f1940c1e40e40ca049207028004890203444c2201c0030808c098800b54010090001d850f0f8120100c0e90000c04100343c0c00c21003d40100035507100c08440242521403502684483c0c00c640210040303818140003280002440300c0303040680301a961342c5825170340c658080045481524074080c90305980e98903072 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 341072194 1250 341070944 341070967
    0x9120912070303120e0303010308070308072d03060e1b07060b0a0902040306050f041223070501060f0b120604020307051204110f010903020f090402190603090303240317 74
    0x18400450080d00c4030703010a0207138415107056481da04014089600100014400203102c8816034000c56010b01e001c3c0d40550720342006454120180540c240025007034980f1100940c210150000100759660b401d00000f540c2e102c2c0454924000d4460450b0b03410180420050344102c4806000300a0266102040c101d102d000403e420b241c10b83c0000c1c04198000800b401802198000c2039000f07040c61320010307000e150588034014511500c021203010011544644c24110082010a51a00b24003800a9a83e10203514080e4000c203442d00c261307141840001400945102e0308001e8582810213086482000c0c1c0c1d480b001c20000b548020054010710209010040007450340d15280d510030f5226010b07540e201d440510402a0081d5418280b81c1000040740d400e20040c0c03220102c0500000c4151551310745920350b803000940c04c043d240c0d110203191465160008540d0b502d90452042a4004d0b1800c000100140c1183c2c028440c48011040000340c050340200009504004041c4550103080d903a141402180b004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 341073444 1250 341072194 341072203
    0xc0a05061e0408101407271802071106030c030a020a0309050d0207090b0a0b1602010e03030310210503031f1e18060e0a09050a02100f03050a0509120912 67
    0x1c074903d90b41c440402501d00c00d00d103114501000c8600d04840a040c0342256004281030b03e80c3c0800d184005000c0844800400c048606078082d244c03500000c0b000400c505a40f000a40161405075080c195860030f007038607030030305034200c2c1e0180304802c51561a503a54056410040d6021900d007004165a496400c3c01181080c07119019035981e642c00350150605e01041041aa076040d2601803003040158402c10500003604d0841750307030380c42600320041074821130300060758242020a080c07501800004100325140030310385400020765441c03c000452a00e502060560300d5418445c008003240c4c420004107480e041090508540000c1c100031820086031280100d003202090305c407075200051082c12060240030895180300900500d202c05c02c0080a18110b020650f60001408403c0c0f6266100491000c2c0300c401d00c07601c080c8a40207024101c8103405550b0003046002c1c0c007182040003a00e004003207003034511603004590007010700d1b000414065200c4150500554000307417900768084c00075045411002410701 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 341074694 1250 341073444 341073449
    0xb0d0803040812070504080c010e0301090c0b031608070912110a1707050d210908010507050301150309050d1214090a021302040305032704111b0c0a05061e04 69
    0x8486910b4050740710781100f941c00050103074400c1c05000d0000b8044010005081980c80c10246000c0b401c3e0714402e03011900503c45244c02030302c0d1035201400130504034560030085015948001c0b01c2001d400c081c00c800c55041e4000d4440b2000190208010020103807080100c4040d40c1c044d02c0d40c1c42d02c2c05200d0f8001f500107011503012894010400e8101c20300e520007072001d5402480252690301e144e0500d50786088480c00380c04518081d00d1005034100e140c0503c2880782d0703405009800020441418142000381090b04244034528a00e00e11482000383c0603c00e0080314070715640708000713145c8140702d00410384000707041100041400d0b54032500900c610495031007403401440014080d09000c80140103204450400d035480d00301c1580100020000140c0010880719030b90001040c00ea0b60820b01060101c10f0036045403c00d501a08000c030511510551400404c8088120f0310203401591031003240c142c40314000341c52a40e011030184810030103414154002c000100c943d4044407100348281030724000c540c00a4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 341075944 1250 341074694 341074703
    0x3040b0403110a0b010f0803030921040f060e040b04020c0703061d010f0903020d021c0302070201140d0f0e0106050a09050c04120305090306071e11070801090602031611100b0d080304 80
    0x801088405100086c510240002c00059483c602e40049415601c031400c01d0b03c035a41010500603040810010800d5401410138114007070200d9a42d0300c2e005141060a441044c07203103240c440c08851915140c0b0844444840715405020020b00d1070721410010483e80c0881c5c010104005080c00740d000080c401c503208407903510400201c8403ca41030003441c00000e40c45d03a600351b500030f1041145140c00f4806500150905181c0582d80d10302c0791004985072422206440310106011074194419903c1c1c0e0400d4410220b030100801c100c1100c800c43d60309840040c4a420b0300500c0c0c610302072000e0702d960342200b60b03c1402d0f150300c0d516140d518100042212202102540010804205035200d45800c1c841142c12841c0c03880c1030740407030304500214550315805243c00002d0140918078819050030034028240100342d41d2000b00205602c9007016406548125140007a91151440c40071045c2c1c000d41090044000d09002402c20007407110450004051038400030740c5c03144500d0503410008004d0310003076114038402c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 341077194 1250 341075944 341075963
    0x60108010c020303041a130602030108031c110a1214091507050315130e030f070302010e010c08010515090d060f0507020c0306070311090901031a090d0503040b0403110a 74
    0x14515024210707100c0800c0c11003190003c00c00d20000c151031a140e600c000058481c450300c0c2d900e48921b4880680e40425004202500100000a8401010024102c5084a002c40e40f0070500c0b80501d100444240a8110745000c1041c00f000314894840c01c94003c2000c0e02420004100c0c81141003408501c0d400c03a4240d409501c400961507011002c0b0321000d8104215051190860a01c2c0f02125000c2640403006409071507180420884580e0940000c202d0325420001d99680c0c41d0010621842588070800540140d804c6c481e854140040511070303017400d00038650740c218045e42040c2c20480183e0a010003120322150a03c002c401540da0005c90b000703454840c1c0d80004a1243d074546c40016100000d02c587c1c159003010f24591a103032804110382e81c1c0110140f41c006140400203080038914014052400e4110030508004002c01000706088100200d0101c00000c3d255900c4100c15a01c400c81d1300f8074800200180041000141c00c012000d40280c82820103003501c0201c00021840c22000d000f00350b600100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 341078444 1250 341077194 341077199
    0xb070e2107060f05030c030403140928050105040b0a03021b1005250c080f040306150503070b040807030f02040603021e120102040605190309120c0611042405090a080601 74
    0xc00a898030892440f600707009080d85010010400b16000c0144040c0c00c0c4405407411080c840b00c4130088950914001b002c440141480380007a600d503041c400b0f044411007400c00004120340d8001c000303850131140580c3c2840c1c0b8180300c14501f1006500301450012032462040e01d12105210140189103215200c1400065107140c54410101e000030b10b0212899507000e00702d1110311950b4840c82c40c2c505145c000c041c40750b55425000c120406846680d01c040c0559181c94030009145152400d4002220070880840300e005480d0384c0290b182e0700c40c1d88208011540300000400000d965009881c0030180001d200240d80e9640e07801050030340c1c0d203c01d80316507200e10b44201800c45140c0742445000c41d041280086042c20704045001c2d103075101d204e01114081404496402c16948290880001ca0fa8032145190700b0401e90003001e07008200001c011110307941811002002a8045801d40f004c8415038060038102803680c181d0440e5085d191070080c404c010040201081980795042180010b00001004226039071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 341079694 1250 341078444 341078447
    0xa0e0c06041d01050418030e0f03031602040509010c1b0303060b03280b01050901030203180d050705011b0c061a0907020304031a040308061302091509030d08040b070e210706 76
    0x9005070001e521691400304522407111b00e220005840c43e40c5410589090b0b0030440004a40c054100801e40e818030000850840e8a03c9030741c80c0f2812a8400d480c1480161070310303c1f200c0e080c1e440c00b18070038000845048070b8143c545d100c0251100c0c064040c1c00e00042c0346460f008004d54035802122240e00840c1000c0341c80c2c40100524030603180ca03004a080402500e4810340000741b6a11071440c0d89410143c003c800704205045041c20032160304a50f004a070844a400030002d0500d4000020603241940390000c040c0c80c0b20441d90b5566500741450751341c400c150740c495582000030315200207c1074002118600402c101e4075101c1c20305010354541d80013181c0722840c51810505414440480d10040300e2100140b0000030380045200d40c0140d030894452858245610007003000380252000c4030780c40b0002c0c040c58951501c03181e00901d10180c0c16410b541107289111300903601c1e51819a002004d1070b04040014910038814410101490001422820300d111a504078080500003107000d13005a403c40902003140d107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 341080944 1250 341079694 341079749
    0x8120411060a0e1008071d0f0303031018020406120203130c06050301050a0f05150a0c150f0f020c06040303150315020a020c10050a0804020d1a07080105040b090a0e0c0604 75
    0x4d1035600c1c29460f01d20740484024036a030240780e480518401e4a140305107603030b9986048920b0703002015048a45a24201050403c090b65034442c80361040010622040c0108041c0211003e0b1031103500c50305205282000c0b80c8000f0351000340a500005826651030000be44e1040803200184095560503807294104410403800300070079441001950310b00d00c03007002143c407030350a194000b0815481003611056001c4c030543c1e81340c500080003408110902c1012083c1c1d1401d030710840d0f011030712140030011600e04849880c120301c0f540d4101c84469000741d00040c000703842a003001d01ca104000d80c50520b030755500d560390200c1145a11090811540210710221404c1e8100600300b02c40000b100d404500c03a12000c17001e0300d90310034011280200808000002c00355140c0c4000c031140141d000c6c200d08034512801d41c000c4d40600d000c1e03500000040c210000042d1500e018010744504400043c44000c09448603c0644010200409519131900591002014550350800580018180c03001d01c4a131a41d40900d140b03070503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 341082194 1250 341080944 341080969
    0x108180316150e190309080f06091b130902060f0a0203250f170f0a050702090603070f14040b100c1b030b0106031a0a090c03061208120411060a0e 64
    0xb1540f900002d0840b0010000741402c250304103410604009545090840b02c1c0701c515000740300b062040c0d000030814a10009039162141d102d4a06940c02100180c4083c003800c211946d003560f20514920900030b0103201540102e80492008144500e0041500141c10309900541c0045000d0b0b04046011444000441c03a509141c4012400f8500004410344c2e0340c203540394500700c0c090129600c0b43c0b04002c5010f40503040311140000d0b1010b00c1c8e152003200d80300902650200100300e00130061400800c810742800500f0005840c05400003100041c28503004102d900400701c016070344180c80d2401103c844c1c682081902c5012280d5854040030852810101181942c003a0030f6103d07101e2482c02000800c0a07500d0b8181550001c1c940400d1000350221101103060030011881e5015694110000304014141e11131800e00307500d86c41c28441d841d43c039510002035503030604010f80040c0c82001070005842c11180701d640d00a00ca40c1241c0381d2925110042000e903080308100802041100d10301d481e1615168259045 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 341083444 1250 341082194 341082233
    0xc0213090503030103031d0d14100c0203040b0a0c020a091d0303040b06090a0b0a091a0303070c05010c080d0906020d051302030705090702031b0c19140108180316 71
    0xc44503551419501d100c14400a81040451144400d800c4034009003d04100310050110100d00c1c5030341080d20305c1080344a44040e880c4607a074003240d07200d015030045100d0140c030703a006582070524100b00c42c107103640146184010881001003050040c2d45641684c8090300d080c01c1c0000d20b01403005102d10404081210300c420540c0300340104030010b584004c9040c0e10010564040083d0303100c0440d91801f40c803450f21460b034080c1104a000c00c3c491401c1c0d001c0344c058045074503220001080c20048c9071b16841070706070141440b940c4a0040c0711650081340e43e0f4480794800c48003540f0b400b081079200d80494122030801c0b03419540008520b1483c40e03060066540050700d0881c0e02d4001c281d0b66000958a1040d40700c0d00c0d01035191800000c070028004d00c01d030b800b130000b032091581c40b100314010115180c043d4031000034424503c40311080440c401450794001640d0600d132009101d116050019208a01d00621501403041000c50b0041041401e01c040c120000140380c1d64154500c0d00c0c42c0402c1c142c80c1e103814244 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 341084694 1250 341083444 341083451
    0xd020c010c0c0804050609040609020c0c040606030c020304090504032705010f0e130f0b0d0b01050a0602030a050706050c1303050303070305011e0303140c070f1706070519030b040c0c0213 82
    0x6021583d48001c6504a6100321500da503141d2074039000c03d0180180f9800782052a1022510074540e10011480c0c81042200316020441191a41c1064045a8030182440c2c0141c0c0709120600403445160302240d0468003e060044150345030703045030b03c280c0606d84001f81590400340e8007003082e942c1000d11070420081e1814500742101c06480482d041d1502d56900e1080c550303c072003401c40b04042a0340013401c0d00a001d0314007041c101c91414100c20380b02084c13085900928070b101c40000c00d94404400d86110000d941d580c2c0b45001901d40f2000060a070107800300c0c4444008100081c040c1d24141c075902c00551041016507124505050040c3c2107a03030503808107070071040b032600544c060307142c7c3e51950040da90315003081e41c940799510002d4000c900a1007180305403485a00c00c0440c004942e07103020001c550620316421602403151030525201c80b07064500c4004241d00388031a10300d84042c00004d00c803000d41c40c507000408020410015040e0b07009180b05801080700c0140350300950400000c00c9403400110002032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 341085944 1250 341084694 341084717
    0x1a13060509011a041e0c0512010509071418130905060907081f02041d06090703140133050c0c120604020409030c0f0510140609010b0a0909020d020c010c 67
    0x94000c2d000c04454680720315545c40c948200032000151000c80b41c100480200036000c4a80340c0501190b0208243c0c00410005400000c0c0f545850168284101c031a66070f00c0402c000b40c000d10354102d4012901c2c0001c44070740e06062506980704d400055060403d03590000c0340041860500394101480a8101419078000303401c240102d4200040310381c440207000040c01e10202d0141c807010020b000c1d58000c0036040c10742c1c000c1c2d00341f00882e50740014080d1200f192010082d454911b01603040315282d00c0e00400c0c40e180c00004112441c508006152070001901112415044103d0010252165442002d01089003c01e0b203481c0ea0904100ba801c9800c829100c1100485030265842d90b14080240300a10031616900d0314010103224050340d24010703502405c03039501306981d480c119848aa6400c00e108165240c0700c01e1f2003036000113034155800b5043c06040004580d00303040301c1031081d81c00950304400340301d003d0000040b0b07a00c543c8014500e28105410050325030340e44030f01c0c55003940ca040406000700081132540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 341087194 1250 341085944 341085971
    0x90b1302010816110105130b0105090f06040b01030f0c020106080c10020a0b1003050a11030d030b0d020d05030928050904030906050a140304050a1703090a020103091a1306050901 78
    0x2e0540094818000c0300d658407008608a90110380c0000b4140300c0d500740301c04d020842c0c0d5400009154680310b54030b0102e980c2c0c1c990090088608080360500081c04501020030b407181000d5002d00500d586c1031501041201001e203ca40590310307412655030040c2c0d0744410422001c1818441d6403c00c840840d040d00300c01e540124029a030348049078014004202d0300c0c01154844114400800c01190301c802901c8103003040d810090301030310200030035502902032002c200b0205031007440b030442c8da410700403c61500707003405409010b0b210700e090408a03010720040000d0343d2580c0d00c4012412201d0240a60111041401001407446007040d0380150f000745142028000060303048400403094900300c1c506240c4a403104042103c82c0301c10350a904000b44400414042800f501041d1801058001c444880c01151030300c0068041c2d00c02214030b10969081007c2c0b910042d84280c0050b0800fa01480c0390768000c0c4084883d1000c801c030141c4a440c9461550010a000c02c103180c040c450b4040e280d07400030003000c0c0d00c0511 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 341088444 1250 341087194 341087207
    0x1f0e040c14090f030a1b0e090106120807020406180f0b0f03060121020a091d0703020609100302090303040605091008040b0720060109050a150f12020a09050901090b130201 75
    0x10390300e103d00741400000c2210381341080f0320307010341d42c01c4504241e1042d094108204481428040c0d040342101442c0082d80c0c40c4c20502031401108c1c460501460502c000c0d480d401401c1d0400c0c0c0c4100d90090300c035580014141890004641c0d00a5505000110200540b400c0e008070f138140312045024684100c1a00d00b03c1da0085101c50440d402450104098440e1140d500c03510024a00e00075800007482101080319901d03640882c1926812100404445008a4010355a2182d6110007548140c1c1001221170302c1c03c180c40881c0b6101c0c13403410054100b003c5200060f046811a42001000481c049030070602803030324036520390210100341400030b0700c0d0600f41c480700d1409400422003020302408401e0001d1911408031010721030131490042c0d0f010303940c4a181c4000075000540344a4960f9090191b1220807200c00841c55040b9203502c000b030158245009501070302261040ca0030307a88420fa9480c00191b41060740551071043d0703040380000860140302d18000e400c11038080c010400c2900b6010f40000141d81101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 341089694 1250 341088444 341088457
    0xc0905180c030c1b06042a0314011104030b09060606040305030403020105030408070f12020c03031c0905150c0a030f020a02061f12030804050709110a030b1f0e040c14 73
    0x395116940d40c0c62060070b4031144a51540d84130107503403030000c1c844001c00c046602402035200380c400c80d0100c100c0c2900c01040300245136810303c00141120003080040c1906080c00d6908259000102d04000b1140004425420550040c0e44002003d0704010032941e00b0f010159001108a0342907007001d0540d12001e030341b80542d020090600c1000030104050242d464207560748994004005a00250503150604818810720b082401505c24800b490009150100030f54003041c0080c8507002004581c0c0f035185000c0c1440103c01d44980c05a008054040b1042c0d8410500c6000300080182d640d40360848020100e508002c01294894818001c020616501081150708403000500414600f0740e50b030840c0c02e01d405254032804010b140c0c484c0d481c0c101508028a94842c90080d402e0f1040c83c0ea64143d41000d03140c2c640c0c0c031244600030801c203a01240780a640300107014071018000e92041c800c1c96481c017040c056084802c5000c80c40900140e00b4500c2e142c00769190040c42480c0c955001882c500b0946032500658 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 341090944 1250 341089694 341089711
    0xf0a20010c1205070c0528090507020d140702091e06010509100c140f01060302130605091b04082d011401050609040905070605030403080a0e0d0503070513090c090518 73
    0x741c44d0140003016030590064070008150540d01e01000300030094441078015020503c2011660000d01031450b44105445041b2a402070900805c0300170088410b80140040d2082001d401d210030b40241e06c07444400c0c0c1c03081240a05410380340710425010407403080c005001d60304024040015142544400d0803001c200106814a024000040d15091034040b0605005c40c00d2031080c80c190091305881500508201c03402030340e41210300101e0101c00c0d0151541400b441f500000d02c1000315440d40102d802080410b80c0c1909094206612003542c181004400c1501c044c0168400000d41e00c8500d802042415902d00c190080101e5090382e640e602521005102d0b03580700c0c03d40400c4941c42600d494002156803544201504c00c29619160060810340040e01c050300050318417000110314207a00e216418500c1d5281c0b00609140e010018203c1f055840100781004100040c8401848580000300e804c01034a90305ea0081401d10000c90014504005980034a104800701041c049803840c103c8915a04003220 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 341092194 1250 341090944 341090947
    0x150c0b06011b03030b3f030c0a030207060801090c0f050901090b03010306052d0a02130e1503010f1e020a050403170d0c140a0309050f0a20010c1205 65
    0x3103100695022028050800100d0b6602801c0c1c0109a81a48004003650b012a01c402e00342c00003803110000152001146c0175603140f0784088821000c400703600895201066821a03282044040f50b090a01a031410201e000da0310881080c4001038200d4170450141130026030805c0713007035469500240354111203c03814046c0100001c101d20580d2103010200040c001401c412039403540d580c50003a004060884040340008035050854070b011b5442c260b0350074044406d01040040344c8580c61410000d52150000508130000c409000500148454a00744605c07014078201004a03000000e150a44d5100d684522485142c0441c0c905c00c140841c41c107004032014042c0068580c030203024162003d10850708050402c448419081508210440003032040100144040c800340800708410b8890440c40b1000c0c0e01511000e02010100d10322070743c400013480d40120b04941620540303144d001e0606426520680b40c208090943c07401c0c00c030020901c2c501c4904286005007000c20343d038503007103181d0070007140300c0041020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 341093444 1250 341092194 341092201
    0x80603031e0d090309081c0f050306012318030d09060c050a140a0c050603010e010603051312021b0907090506030a15170f0d14090604080a0303050105030601150c0b 72
    0x10800e00b540d000303004122081103954010b00f0041e081d481c25100d484d60501c181a40c214030300d0b146900d01d6042110644804401084152080d18a90801010355041002100410a44481d0700d40b040310001140d40d1050345c1c030303a401420550b0128030440300130b01990181c0f210a5409500c46050740c2125110f01e4407200040076031900078100300c0c01080113801e00c1c0e040da45000b12140007040541000744511074402202e560740302449100e00091294800c601c00f11801001614040d07000750b0751012014020001451443d40c9a6905180b0040c000380180d03c100c083c400e0f0700d010700d841002c04050442e00d14826107004407008090150600403280074440102c0030a0b58018a034000c62030715144404842c40e141e0302c440d40803042c9c0d141e00b02e4001803442440c04100c500c1201140076281082c603075031124411802c40e11664481d0388541005600300390100310008440c2018044410b1441c4650340108507545490100b501e02101070b00080003070b01e51325020500d20f54014814885c540c1d40300e080e2110302da5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 341094694 1250 341093444 341093497
    0x10c0b060420072a0305061b09042f0f03010312020316050a1505090607030c05070204060b0c0105100815130f050a120c0c030803090a200a0608060303 66
    0x8081c080002d008401c0855160100400c00002030815198a140f01d40b0007059a002000300da44248805400c070b4000b900031031030300138a001c40340107840040702e9810301d85038104006c90104c842200351135081002880e800301c03418621740c01000c054020b400684d405e007840c02500030b08520043c4030041c06400908a480140c50090003580d900090010241c102300b01d55080103911002c0d004d0301200c20003007000007202c85507403900c9074a019130881c5000b8002559044820703801409203044400a110b020700a020050b602c0c0d0260344003811084122507210015132025509450300942144a00a0b603294240440345001400c2520b2181680b00c0e040c0603140c4200004240c0248500a4550a00181d81e882807110000da080441740c4074047d45401c000b08030b0b80c1154000391901c0c00400d807409458042000c02c505102554101c1034100c2603842028195941250591268002c80c168505d1294101c6071441c000112000a00017824600304520b07158000130740340e12035030030344640401c1801070101c03046 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 341095944 1250 341094694 341094731
    0x3031f030b07050306010e0a0e1f1e031703060102030703030f0b060327061506030a060e18010e0c06030a0c11010e0f0f03070b22020a12030806010c0b0604 68
    0x40d6044a482003860408000c02070860303008568250104502c0c0000e21001d04040c2140c800f1550280c41c80891a200c1c06030341310307400d0035004801e00d01d500d00c0c240103d10030f00100c2d511880c20801d1400d10340314030329500e03200c1c03198490074613803510034103080c020821683d0f0088125066580d040c41e0010707041c203043e00300070010030010084540280e000b0040092000580d8018800d904200c001000d140d015a541e00d691881c1c21100f0002081b011030303500f0041d041c128040d58101c01c0c00c0030007041703898450010742035091040b00e002c0d0038003200c0b2080c200300c0031003031242e100820341d040040c08c903484005000ca050707031102034001041142c3e18400c22003480d20601c0500701c2e120110000b0b00c4004040480156911510403604e091409800009100ca074030000849941652140009181c0c0d5a806c00d84c60002041c00c0c98401818017500409006980380004080a000d001e0b07140a00030005040040aa100c018100381c14402c900b001c0034041041c880f801503007c04101c4010070300700b102004407a007030b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 341097194 1250 341095944 341095949
    0x50d030311040b030f130507090902043b19240f1e0204050f06072a0311010305040302070b0a120f0606020c09070c1e0807060501060815010203031f 65
    0x2144002c02c01103601148100214000d4100c41100f0305c25880740080004004d544403801003183c4e220344420050107215400c0850000c0c00100001019030b9211204040c03c0648240d003040d0740361984000f680303560300646840d0000c2d500401071010424085212443d00c48403c0050b04010680300140ca0035594812524010a01d100c001d000051050f42c0c41005040b241e14464540002c000a5925505e075906c25a42110b82c010002203440303401400b4020b19034415501615404000032000c2c40d41031038004074540000a8070031458544e4650304101042000040b02541010b05020a01005c282d0010391401559400c094140e503511414038156500c1d940e644a2000b05801d110440c4028505540020100c849980039900480003040402c8940c1c201203440d03002050f10401c0d6a00455400c1e1070100c00203043c5c503416121050b01c5c0e19062900d41201104a031459102c0f0014807416500040254114101a80c8200c1064203880043c0d00c0340002400142d08407071a000030f900284c02900030200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 341098444 1250 341097194 341097221
    0x7081b0a210c050306190503030c0c040c1103070201032a18050102190f0204090b09010506010201110301150809010f1d010b0604120605061203131403030a09050d0303 73
    0xa450544480282080300c00d01d0750340000c50403048400394120310901404040401c50756401d80396170f881a08020881803c2d510718480c03480440c0300440d1b5510100010903e20403214000d000400c2d01e14100800d03110622184400c000031500f00040c000c9002040d20b6055509080108201700c1d45590144211204420000d003001040800700c1c1164100300c0761401a034140c03c0e04900350351204010b99a0300d0120201c00e0b40a003100007400c0c045902c0640700b1a91510040002c0750848003a10340c1841c1c1c03e01a0744000300c5075900c10600c402d5603024496100c411017042c1610b421507260400e0842d1362034810504074240490940001d94001c0298045207002c1c40380e0b030040040c45030764103259000d080160450900742d0302c0d007516110245407000994003125001e0040794091001a40d403503010f024041c186075000300d41085041007001f414801b6101c40c4410380c1c1c8403c0740c1031602c1c10700c0c3c181c0688203121500a4000308903620324103038002c00c1e03182030703400584815005c49403a01d4107d00510009845a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 341099694 1250 341098444 341098447
    0x7060b091005010914060901140d0603060e06100e0c0c07030b0103060e121306050d090b041101090909020f0d03020f010203070203120618010e06040612120f02030a0807081b 76
    0x26a2100c040c00c1c103000e94100381e0310008629142d0aaa9000c040f4500074542d211800380100802d643c8143c2c00c00e600e10342c3c446400d030b082c00c02c0b01c902101654200d4104071800d580b90724611072901c000700300c2d481d0f100105a4030740c1c01c0703185403184000e43d40b00c0c040e141c3c084200e40000e900000000800520004bd0380c02800d080031581c0d28100780d80200b04408000c43c0c81d0082011400340020a44c05591032032a20340c10208000c0e14213002550198040680c030000a40c40d90b5941c804951000e480d9845640122005016400c9a41c0010198440307030700540a0390b86891000c0016071a44101c44482c608155140c084614103800c042e864105580d0740c440070340d03000204000c0c45a034040f0152941300c00407544111a03071501c02c03c1101e00305001d58412000121a801048040c80507400c07940c0010300a44002002c9840d1650030282c0104040c041e034882c81034281c030381e5203180d0290500d4043c291a10140d07050101060707000307120036005007841041140d10000b1506141803611000c01182c01c0c4950706 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 341100944 1250 341099694 341099701
    0xf1b210e06090c01030c02150a090309080d0e010216060504090b2803030e090127021303050313141309030212040303030b10030e030a03020c0f0604200a030201050a0507060b09 77
    0xa43e0344400c80c000309400a0f00300b1043c0c00915000160710500b40c080b4001c0e401d403c3d40c908004200900b03c1d00c0040d03040062042c1d00041c241c00c1800040882c02c00366803194041901540064600741207504012680c00d2840010061a40e21800b914117541306220007044000440740060256180d410041a8452a01280182205014154104880c80794640c1c000c01d410180802503110300134840c01403503107d5001c0f291104644a031801d001c2404080300142460741041c84503001b002c240d00125415400060104102e0a41200c030200070070040154004600d40c201c041951041d2403444010140d0321840c1c1601058000c0c011740120b4a0080040e645503035480c01c0060251410301005402141950b2217405040d20034010281d251015800952030032511680c01c03002540841310f80c4200b0701515400d02a000810f00030180600d004444100b60f410f040c000e0080020140c3c54031038881c180414007040140d070404c059540d048024140a511342da15802c00001526010040d203900440c10401c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 341102194 1250 341100944 341100961
    0x3041806030804120512030c0a03050a0603170d2702100314040f060b031b0f120d03051b07030e01080c091801150507050c060c1c030f1b210e06 63
    0x2200c91040c005d900b11000c3e0002c102d03280070a13120580b00d0489a17141009a0440e040c06500682d4000c0b0f11040c0020b00c8a907039483d80b580c14195405541e4a00f03500099250168500c2c2c00340110503098004010003401004004102000c0301c82d81c000c0c001c0502c006660780a501a40c401c0b02043c05021030a50700e85024030703000e0a0245040b07012111a490030301c20340038900b00040c101c0c840349000000390074800c0034481040320640181d000d2a5010f01c003175560184940302030150000d07001c581c2c0c034041402c0c18015088012040c0202078011050340502004011a0b40303c6421444490203091009042e20340c950f00c0981c9108141507183c020928800d00c007142000803a6060413140614104004928a43c004503a1881001800b805035813000482020ba460500c00800849035801d08641c00b80240300d080b40240d80d0600600e8010983c0c420b4940d256100c90301444198125032040d818024042c00009884034100015036810141003c02c6d149210681d41d10034821201c401017110751070302c0c21009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 341103444 1250 341102194 341102219
    0xc070602010c11031e1602130b03010509030f180109032010030618020d09050601060201090b060a080d03050a1e1d070e0412030b04050115090e0903041806030804 71
    0x302c4400007144507115200c1d038040030094580007204c0300001c4c000c1c44c2510260400c960020240600d52140c496402ca0069842142980071449040300210b511300b0100101030171914003e100c00c40e9904104560300e0541c898400b124074400700740f4150423540414030300407907602c816030300001c020b044c0301e510044007180341c1c4e41140c1e03096108817001442002c04410840c1626994400c1c003500303240780180004120020340150090440038800081c0340d02c0340d034595605d0407601380c0c00040941d540e4552403040c01a01044164401070583e0b08109480c5001c031950340d541700e0b01d070442c01011740d07550124421008682144001e0081811102c881c00b2094040d04010170314034112448030071904c45801e040490104803c800c9551481030501c0566075915140030381a4007007040c0c4201a0740758204581552144101c50103044030340725945614119007000b40409940e5000400c81d20112030802c01d450038000200d40942e410380e652500e184440c1c81502014051941009240c5440403c002c03541c4145880d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 341104694 1250 341103444 341103461
    0x11060f071101090503120906070819020d0c0f060903140a0306050f03070f1203090b270117011a07050114061807050711031905010c11120a0c03050c07060201 69
    0x8031800d034914580015100040d8500c04d242d05038000c0640b40408100350009070084600c00b0f81140d180c8245603071100c26551142c450690b8030b025020143c142c042d81040065019035060410207644185511502610490420b0041c41c00c2d884201003001c15104242e481131082a03a030110f612030018920103009001c86004241c014070b01001e81d4000d503c0e0015140007100e40d8a00486222410f10810407418620740a0070340500803180000105048203c0003005060800c0744e40280684410006500c00340305100380c0d50400c016088400081e40f21001c0e001e0454111101094001a03080c1400346c0a0255070b1000d81194070b000d200030b4940c0302554005128030b10466511000e107209c101c81180206090f101c440016800384a1040011010b088502d400c1d50028200d40c0c1040643c035814000b540040000c85269448403181a840d541101480c0303550198940500280c00f00a03e0f03484841c002c40c82000e0402800100440c24140039004955041030864281c4404580303440c00a8040c0c064103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 341105944 1250 341104694 341104703
    0x24090a06110a022103042d06060303091e05120c0319020a0605180f04090203030c0c01030b0414061003060e010608041b080c0f030f0a0f110a05090c030411060f07 71
    0x2101c1806a01504c0c18014080c0c428004040b0306645954880c180c4002600908041070340c0b400301200381c85940034012a11985c41010045442c5040d407a0080c20030035240d2001c0301070350068030380c004c0c5540f031030440c031050742c4094510300c545140c0349421510700405d844540703415000309503000c41101c0c3c0d0b60070f50018441c026101b58101d40c2c0c1c0c811040f5410302c9000040b415101c08a0320f000110728092500111201004101180b90059900000d0556001ca03880300060350280c22070300313407a50301030141c00c05803003084808000d0846100c03a080054100105070f5031040b402000740318103503030107a80803101420403c0c040e1200d079a10355a01810741d1506840c2510281c1800800944d4021249a02e00c107491040b406055182081e20a001c1600303020007007558035020307a0180d2102d03441c0406c031a01b40355025040c0588104914140041008120b00115010300841d503c140b0151310b8000e9401e81180d26085440d6591756a401c0ca034041141e2440026170050001518120f900d03070708801b805040e07008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 341107194 1250 341105944 341105953
    0x203010b03030f1605070905330109030f080415020703050c0a1a09030a3903050703170f0301121a01050906120312010602010c020d0224090a06110a02 66
    0x26402015624083c03403800e00d0701810204151007071907141d120102130300c902c600110748000307441d248000c0035150100c0c0c02346000003040109101524400c200c240d501c420b44407446101414540000740203220314000a0414082030303000b0410000d400c0121b0303008000601d003201142d2010180251520281c1c401982c042c0311320625516140b500e00419002c40b0207030072016106400144200c000c980107500c45d56410f0268940c010702048164107001c2c4482c03101042d401c4101d0400000d80400c070074a6031168441d0341001c1081c80080ea0019407141680d40080e8072018844800480380703401e204124041c002c042c2d000c800003d040d01c0002c1804800c45c80351440908a010782001e10100c80380902c9050781c014000408290a420440d040c000c4406001060ba45000e0412483c21054403007070307002d140142c2d5581c00c048219a8180030108403142544082c01d41118402d080c02101022005607a00310f6014101082c2e900d10100038403410345921100900c003a0000100d01c030800d811510829002d8002d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 341108444 1250 341107194 341107211
    0x10507050d0c051e1f02090409110a090204152007090b010e120d03020a0909090b0414160302040c091805090c0105090d080313020910060201180f0b070504050418020301 74
    0x240135502d640c000b400c100040480308101000310300e41503001c0e00f030444000d500b040315a045444a00911b1800c13805a50341d02c3c20425110140f0a0350f448032380c00001070920501003488000b800c001440103821140c981030701c56095048002181001c0c200c0000c3c44c5100c0d0303080010b080c084c650001d1b0420312098a400044100c140300340300c05815142d207002901c2c0c002c0f2104004240c02a40908100506403800c11030280d190b48602c070460340c04d0351080e91003804880420040041c00002d045c200c070008009441d2100480c44c3c408001001400000d100382d848001541d42c02e0320410060006040b580702d12501c040560b0941d4006103401e4401a020740201d850703001040d4000c130108c6850941c0540000300c0460280c50351030f59a04003400b500104107541e03d130100940d071844081c50080d81040f8515405600e4000082c0c01c40c0c034000300d40051207048007281808200c13498184060250003140100803a030340c6074001c13209482140c1015030b0061405c2038103558000c81400c801e240c1882a4009c101c07841 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 341109694 1250 341108444 341108473
    0x2060a06090608030910120212040b103b1515030106051b010e1509060609011412101a040f0b0a03080703140318011505011d010507050d0c05 62
    0x2040c038001c2c01860343c070400c641d50980c1014010103030094111f01d8401c40e418100086041aa4404041c0d51134280d51001404140b28a040105401034a41d1040c052001d1400ea0303948001c4005000440b40c1c1300c52403580b0f400080c80004c2440c00c0c030354034045501c900c0c80d002554520840d51102d0310f5000741c085010440c8100d140c0c00441b41030700c07419104d55003400020100c903030f9612a400002401c6549951260741ca449042140394494011020010400c0c030b8021070003850408010856072148041c08010050402c0012101078121015210405000b03071074595503141840d4104ca0351103a501d06022a40b230780c0d04100c0e10415241044505015600855481c0400d603602d000d0b4845c1c0c000010740301000041d5401004180c414440c0c00c00100c0c803da056541151504100c424100c080303034004040d464a0000e1040740068403d100b079042d002410304000810b088001c80300781d41c0e001540a40100c0b140e01500648007255801021034010850a035401008245080002c86161140c802003c5407803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 341110944 1250 341109694 341109701
    0x80a0915090305040510090e0901110f091804151a1003180b0f0a050601030e0622080c031803061905041505101503090b1b0909010602060a0609 63
    0x125045100c103200e848860855100030300d46540300b01d05000080000003280c0e00c450141c032444081a0b20380318000c61400403101c5203d40300806c000b07560303494041448540f20645081e01d400400c107689894803404a0404254601c4414911040340c1180c201044100b0400743d085100c031520950050101a0110202043e009641003603103901401c000403c81c0043e02c039a0042003541e080b52180d659018590b114800d8059045d100050070403415410448004921301409401510030320b0108142c503070030a141503d030200030b801401e19448140e000599458101340c0b902d55241c0000d14640d0fa5080a243c40c0c0d520742c08000d42c00550a0300d40c07a140814600401e510340314880e6483c6000c1d00114030207030b080043c000204100d40303c0250760329a01205030544903840c801c1e0410072100d017119040200c141c0203620b0290a446c03c0609102070100051784031308031a50040c0321081c05580e9024070054000903406204a0903400c180c42d0000010b03d00d50008006006805403803082020945804d20042079 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 341112194 1250 341110944 341110961
    0x106110c010207180603080310051903153c05220609230a0c08030f040e0a06031209031e2103110f0408120717070303140115080a 57
    0x1503001003004011a1303910108801030346034244000a0010340f6507540303080e5900241c1c2d01e11781c640407048082c0601d0415160003500400000c4880016601d9a41c4011600707a2400d4220081c3c2d4990700e045191001000b40c840300c00040c85a9001a55000c0102800c031080c0080f042ca40282004041007c50b40c06000c002043c40300841311244581d07550702d804000d80002c140c1140d01c0981c000b064060070b44040aa00c20441051000c3c00150f00e0b03504250908014640014140e0b80007040640c221110000850701110072800d150f8007103644103c11140106016840a0b2003160703c916080c000c03950003003008096074072903080002100c203420180054203c441070010316140e804140e041d50304042d143c5500b180c0b20649004196440c0500030910203402500c0790118410700401c06003c40761080c049049114000200d0740e080c9102c40d15460030400662091540140000a84000380742c400e8101442d10060780b64100d03110b5a4440158103da14441d40d40800600001d0201d01c082046001c0d0552 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 341113444 1250 341112194 341112197
    0xf09030810091b0c050109060f0209150712050c0309090403080603060f150f01180b070c06021b0f1f0206011a090f0409051212100501030c0e0f0a0801090c240203030a0207080d0f050106110c01 84
    0x2c03403c01d04c23b040c0c407950320001c030108251106202c02e080943c0c400c02000d00c00c41c8207984202d0359081217001c1c50300c5c2c424043c3c00740803044090741c00c00c10b2101c0c1100289131401d808489000d4190959001680c2d103490983c0301d059000c08507480405c241d040c0000030040c65101e100c0540c0083c0c3e582c40c0881c0c6500306c031100324900c03142c2200041d88034901304494011012008000e0104203403003841035a01082ea0034202c0e0050307003199004001840e13088440205012401c100c86107080d060780005007144406c40c2e02c1a224030741c0e40c0001000d1200400000c2015440240c0f920b50380c0c406465140c481d032108445d4441500c4040e03202140d0755109001b510400d038003680b02d090700042100200b011010aa2007269080b404406e800200d010f0300b4081d10090314051003007201ca4504003038051029400290030a2144126110321f01e80c1141e000040720780c0700c00c645400607101c0902e4038216405102c1c000c1070b032031a24103028100a00f026164003450403200750351640500d81d070038082000c4c0c40d480142c82c2c090 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 341114694 1250 341113444 341113463
    0x31e0e01050306041d0a03090909020616031e05070c0906032102210405090c03060603010b090604091e0f18080d0f09030810091b0c050109060f02091507 67
    0x10855016102440e04541d004001048005a0100004c6401c030300b940808504d80c4240c10150505811900e980d0151070314040601400102d82c001c68540e11868105007800b02c840004001418030541c0144106d0803201e0342c0c408098040100100301da01f00d000e00759003204200c04c0016000b030050cc101d1080ba41c0c0080c10b00080400c40c440103103a0f07010305e00e9403819801159036441d00343d5140c0da0044564646505a9030b1031b03e007064140410f04d6001815250070340800c20a028090751840242d0341100c1140b40c20641e0760480c60042540c0307020755441120300764202070581801c0a08214104a02c24150100704010040001020280c1e178040d03000c20600303092820356001041910b00102008140356101180500107135045808175282c0000981c00201300d0018482145c9402c141d942c01412250414001007207904440c0158080b9a00000203005811100000700902034200c0352000b0340105040020865025060000c1d40c4500345e4544104614440030702d49840b400c00f510301e8281c10054a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 341115944 1250 341114694 341114717
    0x70809011a0906032425091e081906050105030705030a02131b0804060b09160e180903040510080702031204050a0c09060528210b240603040314030c0d06090207031e 72
    0x4142e4406060f00c28032150309a00d0003045101007002b25680101c0d14828072003001d18941407074412901e060300010301ca0781108030100500c0c1d40009101d00d64640454500390a480701d5020540140702962074081103d4a180a0740c19030307030b00801410b104901070041806966281c0301002000d40c1e0884600044c4002100b400c503255104403200d0380340c0170006c1d00c1440c1c0302d00324072500c0386800c0c003c46540c0700a40c0005002d00080c00c005088006040640c01d01030200d0619a6001e900c0380140c04244000c81d2031100000c00380f040400c40190301302c1d04410492801503c0e105000081c1401e03000e49030007000f4011894078008080315a44a60800010f00140054104064240c0100c04028140c414061100c807410115405052550060001803c19040d80d2400c26010110286011166201e03280c18420031020079002240300d960390320400419a602d0303890b5101c0341082e0080d0300607032040529200c008a0003041e40c0e0f0052041c18040e880340d41c403c4058045480c0829015040342d400694005000e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 341117194 1250 341115944 341115959
    0x806030601091e15090b1909091104020307020d0f0f09150309080f03040b0c031e07050d0227060309030d1a1206070809011a090603242509 61
    0xc407030f00c01d0005030b802d842c440d1265126000d8403105404a900d80f0a02e2808000201e1a445854015401a00ea030141d24401a150f02419040c0b4440c000840784c9a83c16202040b554015003903500350020411500c030b04145800035550101c042c00d24022072580d1810040750f0303004030700e400d0f000802ca685070344003103007080100111403000c4885e40060603240c084000006074501c3c042e05101c0602c000c1c0640f24a01410201550b00002e030076182c41c0d4000b00180315600702600c1613520034400301d401100060f154820101c440344106400c50841906c08551544da80c081c0010382c03804074110702c94410182d0809420880c05201c01d0310011a07946c010171040c2c1303044005400c08003c07109078152091144491801140744019041c2140c00d640d0040720800c40700d43d80000800b608903d95900800c007a01c0d042c00041d0035850151a69441890700000103031080d036082090740716040040a2000701100303000481556400261281141202c20f9100900132108001daa602007006c1959524038007481c2040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 341118444 1250 341117194 341117201
    0xa08120a121812140301050d020d050c06040803130e1501110a02130203010501120603082502040e01090b0f09070501051c060f080c010e03030f09060403150504030e01080603060109 79
    0x407084495142c10b08102c42880006040030040c2c010300c618010320143d400000c12948008850543c094418401400b507038666081c0300c2800b640c103603840c00418006040003440d2016000b03641348d1100000034045000c080100c0609010ba415000c903040c1c031a01d4030703200c5580f25411180e042400b1400824004150f02c83e0301e5410040c00c0b010180c4603040180d801152541d00b948003440c0b880ca40003c010400303941d20650498085100000c10031030141599100c441900c0780c007400c0340642026488400300c6d003a0070355080d2489940200100020f201810200740038100c10041034601880040c0050642819a1102e42c850011403020300262410800103541c1500059a0601000756100740c1c021310f84884c0c881d81000e0308140340441030103440c20464034078116000307140341c0c100006410310f4006500d00206949080b0b41c030100080d1504603903001300c1e030640110f81c0702134540140c6440380c0c00140e078189c0c0002e020718000c2d580c41c404c0c2ea440e0307001501c01070702c00d84030729405a0001c001040400c030941d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 341119694 1250 341118444 341118467
    0xb03060609041113020c070f080a050a03030f06081501030c0608040803070c060b040218090612071203020f0a0f031202030106051909120b0105030607031e0216060204060c020a08120a 80
    0x2c4c8104040035020003524100e810200401c91a5400320354140901ea4500c4503003401030035210020309203444165035840c1c40d080902d900505141e03c9200640c1204981e40094010f005000210b4209160407803907544548020710050714040d40000003c6115403003000c0a52049030410882840d54450031000c445010318071005039841540c1b00d0384c13508d4a603500c1c001007480e01c503801c2400814088582c01c001e080200501420b22403c0724510050038402d010480108480003525000c40c003103010300307050b0305003028036280705440d01a0b2414801004030045140384624000c2d0f94003015001032401d40d40c1248801c2c000c03640490070030b00241004032000810780d0070010040c50706603045a61400d598001481d1108201c449821250045c08541420000103911001f2440e0602009190450401c444910300390b811505640000344070602c110002d05200c0c81942c4200d0856a807960b50304000d1440300071000481c07240d40030140c0080d0361540003c040f503100c40c0e803a01c1d142c41d281c0096019101c5c6507080d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 341120944 1250 341119694 341119699
    0x7170d020d0203010312020c030f0709050405070923010518060d0309080708030c010f0603170a0c051203060f1e040b040b030102031f15020709020a0e09190b030606090411 75
    0x204a5140514680e00243d4001c5224000305809180c030b080003c1e01704030203121850302a500212400704580000507107442294000d49001a00391078505240b414030325150800e41300076090010b200914503485003002035035452540d035140c05903291800c01035120a28a24294010000000301d1040e151031800f182c1035600c02c0c10030071061640e8040541c01c1c22030940c0400c0554002050505040d8020b0003803040c03015041d1400c001c52421030342d07004441c20088600d12500e207030100e40b24103d1809001400d04060b040800c441079050300700d88003400c680c000c40b4254000d28603188104101d05049112010503007040c640301302e00c0c071161028000105111000309070310984400b074022598900307100640c0145e44422032080c071420100401480301509500c00b9805d02144008070020300e0f4041000c40940c1c0f401c903009603594620b507a080b00c4c080034032a2469480b2116100303110301500c0032130295460b81d007407160a20141109400b05611000d00f1501c0581008041c000500000c101118401e07288200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 341122194 1250 341120944 341120947
    0x120c150515031509010c050306060a03110c01151508040b06130b04020c010510050604060519030603201011070306021b0706030915090f06051005061606050c07170d02 73
    0x207500020303242208480c061109141c0207014030006810070302840c0800501030034081e1450800f0700102c1c5451090501c4a0300305075884186a41182481e81158a0a040003009200d100320242c50b0903900b80f1948a005848451200590741540c0101a0f0328451a0400181000c5968000500500c040340b844c8410b4030964800c440505a80c2d288050001108600300004580c68100e080c0c0b4019001c98100c50700c502c20904c000c01465074480c089441c0030b0a020f013000b2840c1d0184109801406140e0002080010343d00c0e03540150301e1854800a9160004444800c0b420000000a40b081e118040340003805403c852030174801b08941e500144050900300881000008c01560010f041207450307000500080c0d00c070040d520602c009141c8440c0740a10703002042002118964951941c200e14103801801d40d910f810028035400c4403170003004010720000c0c01c01c07a510302c1d11119210340c103d00c401084500920b00360104a10552001c2a9503c0c0c0c0d6000d03d030110780800070404800039410004c11071084540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 341123444 1250 341122194 341122231
    0xe0402100c080405060c060109050a1e09020d0c151206060207170f0d050a020106050609090a0e28022103160501060b0a030212070e01080a090609020616120c1505 71
    0x51740c2e0018032011207514081c10103541021907100c1540c0000d4102d00c462824080d00780b40700700c489210719109203003c010024224080b071020801401401401424050340c03a000018003800c240c10102c035140c159a20040300c014040311000456055015100c01a440a001401942982c0300110042c0001034201e41c4804111a603d6281114001c610390000f07d01140b9003030000d8090054002808080751254207150082d004a901c040c801054a00c000c7d071601740e140d94030502070242c00400220f6400100840e0340442801401e4410890100e02400308038401a0145134541e41410359038518101441c0b4104090080f0714001003c0c400950b800d55a906000a8680c040401814400c1c41900c0150711031250450300303002c0c441d0081c51442031050304034010513140c2e40401004c0c0e004100400008001040341813910040c408148000d4002c54000341002128604a185043d094072800703c51a80074440001168070100e2224001e05502d04c141403281101c05c40c3e044182c0c00078250000c0810802c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 341124694 1250 341123444 341123449
    0x607170a0207080610060509011b050a03050a170903040b0306060c240703050603060106181806050a060f0507300f0212071e08040f08160e0402100c080405 68
    0x60006040c00c015074090074082106480034403406911000d103422038400d441c581038004d4644c0c0704955100781000100c1d91548540203400140201283c0c0000460344001c8441c50060120361003007030040080741800b500c00c801d1141068205102e10700c0c41019608207440c0081c0e120b05608003611240d800f80d414044a4950181000681080d20701d80256400994881440002c068000341040c0200760134581000043d48000501904654081c40c0080c0b0380b040c1113a045044c030149402a443e40601103d102005414a812500607204200d03240c03592950b99090583d101d1000301100000718805200c804041100070310b09140c100800c210614000240c1d11641c00040d0800c204030001c00c141c440c620b11480e6041291240086920740220b00d080d1964a810111074103180c2c541c00c0c84042c0f00303110b904100320790007690700603c08149868026901c584080742c0303c43e410000d0b42658400e8600c002101005503140c1030045030003504c01090b00d8100c0000710b0306001030318000c4c1c4400c8810000003600d41c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 341125944 1250 341124694 341124697
    0xb0a120f080c1507035c030a060602010203091504050102040506030a0212012114030f0703020a0b092a03010605060a030c030b060406051909080a0305040503010f060e0105060717 78
    0x1600900204021031074004401703000c03214400e443c061010940c041400100700d42c01d0302d8201902c02e050000d010007006001501030000311420070304481e04040c100c88944200e0601860140c08145070500889884007000c074200d0204403007a0407658001006000d008550800c10b64201c0d00800026181c10b48600200307009a10540348a464294001021202c00d408880500e000d04803440c0b21810840c0c0003805286001034051000d89800f034503d1048044c00d40030002c4400030342010b03071180d1b144c0c0010300b400303500c41605c15000c0d01c01040f4200060300c1d10f82c002c9038204002d0101110744000c2e0440441d44ca18206212140613011743d0b8a210204490351a42c018000130f0449a03000f00c1c1190305c07600000c0030340344407503030380760050b40140400c0c030409402c1400d840d8001440c2108203001c4040200440b000503440c6d1145c0313402d010b080480030a140d8490001c0080c0c0703c0070f0b4000d011001100d00700008032601841440044e41ca81d038014400c61a103c0b0040075028090050002c8040308038020f500d65 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 341127194 1250 341125944 341125963
    0x807020301060f05010e0d0507050114094f02070201050904061e0503030702060702010302090a0e0a060e0f0702070311130f05010f0e0c03061c12020d030b0a120f080c 73
    0x1c02d40740c3d00d0108207544e4098200c0e1720402c0c084c0c81c908218030803580c1e40e55440300940941414044006070030340040c000c44080d15030b504001407020801c80c469480d044020445034035403803189040700d41622002030000650f50840d0f0402d20696244100240351440207400070101281002410055901da035a40c07401100c01402c24040c4000b042d000e05005001184c4075680100e0094000380640409a0b55040c241c480c1c9540a0070096902c24203080020aa014160000b801c4912644180480d481e403650000098030241504d4002030f0b1a03800310300450742011603003100140d000001c01e0000542e000681035908001414403150204106c664106490700070b660b1810f843d41d0742004000240c920001c003401480301c4240c11044e81891420481d00f44002001503000e035002000c05814080310614080c0600d4001b00c0500001d524035900a480340451800000020301300501d04003145007003100d200445141c80c44030101d00b0b44642e219040c8901040d0306550b28a0144000941c0c5001031205030203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 341128444 1250 341127194 341127209
    0x11e170601061b1a040807020a151206080604030f1e0309020906010801061413091e05160c03180906150318020a05010e0d060c021509011a0d080702030106 68
    0x40c03640c14940e00034410108202d8440702811524000008107959080c6009201d0019000ca80d0f00d40d902c1c05e0000309031041c02e00c004d4010038102e90000325800e042100c2c600740442c40ea101b1a2490f115640e5805840c036500408840303400c000c1c0450f0000f8046d01c80305204808909124881130180890015a00020030506003c6a00d50b400d600451806e01740040e0721100900b4010b5240d4102003005101c031654140c50f4048900000e9000d48110001140a00400c9800d030140f01064410545858016848660790466418180401c0702c4c1c80e40b081150302c900751541c0d981d00205200361012160b140d02803691310414201d84070007107501e84e00c50244c440a4920800c58400c8480c0c07401c4010102c03021417101d00360b040307401c10007540166101c10220042341c8007403801c1d540b0501503900045c03a15503104001860640f0b400e45811600340c0115070807081d800e06d198407034420b80c2ca0012403426101100c0d000551200c031013030139043d58606171411241560049803183e0900085a012030b0858110750031200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 341129694 1250 341128444 341128453
    0x3161104051513091b1a0a0504061b02030a060605100c03021c0c05060709030312050c09060f09040f0c090501170726010906051f080601080a180f02010e01050c06011e17 74
    0x1072541b100f00c0320000c0711a5200310700c0c214040c800100030f0302940c06000c04102205141440c03540103400c2d480c10594004064804524061a2139001007840e4400c0d140184442107100e45458000e855460f01c0d0360300340d000b602210710300b48481b80024002030114401d010319078080102180040120901c1000240c0350090050b00b1030a0103004c425042901c1da10b00e9007041c0820a074420000152420320200b41c131006e85894002c850203015002c0c280d070b0745400030f141041603a0900b446821003000503a0301e88031002010348882c0115040201a108182082250303004034580b01d00c298407052a46003806101000030080d8084e05000c0d034001c0e48910007264071070809006074940307103030078a540c01540720842d0030800d00c03020080d00040000381102c0c184484000010050b1016422000c821031200f02145000305280c60403207441401c45d00180e0006921602c001d2070b95000305c003142d600d64108030042559030310b00141ca0440c01003490700d41d03400c4400b010b400590340b000c203050704141c540c0d42c030050b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 341130944 1250 341129694 341129699
    0x60307080a0b150907141308010c1805060a080606070c150203040602010b060c1005061504030803010e06010c020d08070602070b091507050f160602090303161104051513091b 76
    0x4040380f1500c403640714070031090380042c000310541009040340d44a078003109003900e98407c001980740c8510f0315072042c105542000d0141070307960307031107100f580c51080700740310003d02c194071081405914000c00da5500080703450407000ca0000e1400e0400b074403140388a103d010300c6890f16a0f0508030700c0f02d801055080568404182400f9035a0280601501314000b40d64460800440048003540c4035448150070101c5a40c0380041080d1f900d408003504c000003810403006940d296280340070036640c1d100f44516498840c9540100e00f003988a1103000d001c039078000b03005580010071526a500e00c0d40c4030303050840d1801c0d400c1060800203811040500c2c4a51507580240000d040c244500d0140e04400410400c1080410882181084204030580d603191010280c9580000f15924100000348141491540d03d1b200102e4402000039100080c424603506c110701d551440b9080c0c1081c0029a4802e903040507110302e690801901e64146a85410078490b42d00350049001122601c90031241a44401a1601d055800c0c405 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 341132194 1250 341130944 341130961
    0x6021b030a051c0203070807030506030f0d0c03080a050907031b0f0909021c050715020f06040b16030c0e01031a13020921250812030a060923060307080a0b 68
    0x42c401c0d400c3d1121040d4034510b4100002003004000601c0e8905266580d40818070300d4500b001141c0000c1404412a01e0786400080054402ea209820440c00142e0010004c0c14528142c000c1600550700c410041072240e0a40c1c0e103a400740d903003208055103161039075240083c000a1300184000240035140e8002036881250041c0031806240c1c0ca03090310001c00201300c0f072000810000d07400046070b40c0c8400320703080d0300340d00304080341403c55003120140284501d002744024040208000d0b405650140071201e0419030482013034094540d2207602002045e803010700031070154040d802524074042d1401e903003500e072280c140024150891800c1801c215a9000c241a421404c08040481e60f040c00c03190450000b03000c03402c04543c0c1e40320030111202044c000a09003040301c0c0000b5900130240c0a4401a220310b041c64034140c84054008803078003094075040400c002840c104034411400f440d900010400711603255400300d90340c40700c03014100581610a0b06000100f0680030311102c0d218910482c520051070030110306 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 341133444 1250 341132194 341132227
    0xd0504030e040c0302070c090506040603050f2b09150522080106050f0303030c0a0e0d0b04020f090c0a0305180a0308060a050901050d15020d0903050a03110a0c06021b030a05 76
    0x1c3c250203241c410002000440c1c2038146060850340d2444020030213940c2d005c00b0501a103202c0c0d0000b0800d10640049181130140400c080d21110b21800903d13645060400007401e50b092043c41440209440413030600c6156030466500c9801001d60614624010403036001c82011008000c0340025034200c0340c404d01102100b07004820040200b1540c4002c00303030320140000c0d1244400790400f03640700e80000d0b800e40028090f000780b030360310903004003548041d142c9420000a201011034049100b02c4a88013101040d2420800f06070148403640c0c6101d042004004050f4014800600300f030302c02c00040404d464151108200461703c080c0700f40ea61071640e08200c01480303003003a070701c3e0440c0d8482d12940300184490b884400300c4410042e04221003c0745009480c0b5140002c1c8031f0790040c10340c2141046202018140c2100051007641440d6501701320803100307068403483c50f02502c660390000551090010380494482c0c0c010300f00d00310780d031040e41c40d520440c1e20602d1b1443c0e200aa410f004a403022038452418040401d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 341134694 1250 341133444 341133461
    0x9020a021002030105061605120c030c0f0303100e070c02031c1101091113020f0703080f180c060a050d18120206060f01030207061e2711150d0504030e04 67
    0x1402d50075941000002881d07802030508a503400c140c00c01000b014001c00b08083d54807100550220350741c852116602e07988990201208902d41d100d94224094800400001c0301c0c4601c2940188002880c14880b134641300e1180078050500304007001d0352200160b41c0911615010301c0150320541401c814004016003108021480c8a019902d40701540000c15081420110844030458801c041003440c0c2446000a01074243e01c0d10111101256210401d908481e031039014524003100354905503a001050314001006c0340070791850307400005511456040c560080e18070b0f203d0b41e041081c2465080b5680c102114000301140c059609090080750038001001040d8100391040d102400b190f103410030100b82c01d03503d000c040c9810160b001401c20248415a401010b2030a025a8103190711502c22050b4805051061410700130900d255440040707501207014a402900e0707022022240d45106c0700104819649811015552047c0c10080c281b1506800d00c20385104500c2034503440c0450000f4001c2c80708880000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 341135944 1250 341134694 341134723
    0x8330f150912060f15030f0d0203030a11031b0c15040501060302100c050d0507080706020a0801062604020f040e0f061f050622050a0306140a0b10080702011509020a02 73
    0x1400300801020a0440c5d002d13400888550607040c0040201c0d1a12200a103244030500030070f40c40c015000d5000c0300a60044540c0c000600c000c4004140e618070500c016a441c00640c0c1c1250107040d9110704007005050002040d1081d1500c1c44541170341c1c00030301442106c0c21112a503440c4001d000b11703e0003a44840d08600740d0726109250001035903c0c81e0f902c00c40308103140705000c0c02080c030508000016003200c540b5035100500390340366006050702400780301083c012400451629038000300341c22802c103045508403200c200550800e44440c0c0038420f9204080311855045a1100c4040e032518508112000d00310040ba80201128940039410322a8414006c589401140b080c0700b0810007036076603505030341030300d143d144e0100502e500300005003440310400d80c00b4a030000303641507001060010341d9209415000d40c03018544000e9030385000500840700300281c49580109d44003500d080b2a803041410036805080d034000040d48405d5840c0301148a40507901c4188925000281c0c170280d150305104840c1405d004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 341137194 1250 341135944 341135953
    0x51002030c03041103030f0a030f050106210209060c01020301080304090f02130b090406030b070c0203250b130f03080711040b2112040306060608330f150912 69
    0x41240d41d100351001500107007100041c84025080c55906008851203040c082207816a1090440c20180241c0015640c10804d5458003000061103401002c90102c01d81003050310b1104003132070f000c0c5000250803140216811401c00d03c00e00980d00c909100071400303020715100458540c3e103800360060603900d40c0722101c1c1901d401400707403900e1100c0381789480302562a00090123480b036900c00b020034010601ea0340701070300201440041c810b0040c2c0043d100c0c130390a4000e134240c400c11030000d900401d0701c244040041c218a503107500300b00600750001c0c0c003401d00d0041c0b11a40d20311030380d5541c540740f030544995041580e442e940090030a0800140422412050700103540a005c500492000205045400001e0703c0d0760040500c3e100201c5641800a4015130200b00002901e4640f60b081c4140244001e00540e0302144192021032241c0520b011202e503000c4014000c5111075032407900c2080342c60343e0000d00b25008890610700040c103541d185190f050740a21454425110482c0804000d840a4107062581d5141c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 341138444 1250 341137194 341137201
    0xf0709020c060109050c09040906061a0708041217030403030510080c0a03110a21230c01050a090e071d010309050303060f0a03050f010f050106050c0c1207090609060305100203 77
    0x8150035044030305044d00082c09544204010945100d000702166006141c5002c0d0800c001540d80440191619450b403c40440304001281c2120311a8400141c001d51080c4002c110300122007202d9040f1921070f0043e45906600d0105003801500140c40490110781c4640070801c0700b030700d408160750040c91450002e07c035405240740800c0412140c0c0c00090007809410340d0b404100c0e21802c45150080c000c0c5140c0c070081050484210904041540c0c00300c440e603200f00030307507e0410090340b001070b81e4450724400f40280309502d40054a00741c2c0f1041c5480240039500307000041c2c00241c121201c0c42940b8a481c0c14041d9084440041c0040c070300301d85640e0525161190b6400464000410750f6403080068407030700078134022900082c40a0b0710685c8000d1a5208202c0c042d4602c81040d0080103051005104c24440750740c0f07560b41510300f40a540440351055001803503181c5c1624100b40200b021070f00f51010b9a922035150740d03c1c002590ba00390030003411507444220404c200f050401201412140c1114110304500307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 341139694 1250 341138444 341138467
    0x1020c1b01080a0b0613120b0a14190f0c0203090a150905091e0412030f0c05030a05190614190e04021012140103020f181906050409050f070902 63
    0x104043c05448800d40d550b0007040c555101c10040300c12403000701152100c2c0c1070b81c0700359406608a4110040364518205000704000e01c1c010302451440740d0300c005820400380c0d240c56021700d1148c0c4c4401685217540d198104441c200e02d65100d014008a40c590180d980ca100c144103115004e50310703520204c82500d0758103a091003180d1008129099030402c4034a04004c0e02c0f180b121901c0400c410800543c00346c1c215090004102441d800c110b928030054030207008010544401c4800c0301c00202c0c044010410400004880c28502c2c3d01c4140d00c00b000c01d100800689001c0602000c0341c5454100d40003038644c1c1001c0403070034580005548005002c851010b001c1d5400c0c1440244a6000600000d0280748a4054130a9990060181a101d8841d441c2c00300b02d40c4900c0c02c01d42c220b0403020300c01a4000c150000e155000e504200900d8130300c45802c40100610703502c80701e4080718038110319041008015522040070070607075a140152410036009100900100035108103035414592143d2095a0240c0304110102d4180c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 341140944 1250 341139694 341139707
    0x160801080c061e040803040f08070e07030b030109062d200708041e030605090102030f0c031f1517091902040f1b02011a1c03090807060201020c1b01 65
    0xc0300c00d0b144a40c90748151440600f129002c0308403000f455002040c0442d41042c00009070048603004100b403180c0960b101c1e8603546030b1259014441d15200c13480c0020b04528003a030000c500c1c000002d0000a0454a61b48445d030882d01102404002030300d840d10202d07148001c1540d407102812004408000030604100702001007100c2e10402c1c0c0c180c1c0000300740b510500c49101c00703030307401003000890364100100e410783c01c000300c0ba03000e0204464040c9040d02080c00041c0500c01d591082403000340d8401745d9210a01801420b80008100e1450002443c2301000420180074200300107028a0341000482d150b02c8601030106c110100c1d14507400d03000b203400c11688200024154641c04518040390083d031a0600104d00501848944108130300c1c200f040c51049000510800318003015682e00070881209070010349036551002080c03169114a80700c08050104800079403544005101741069503180da0390741800c0f41021070030760080340542d5000c11129003040080c44090103c5000a6860012240c85030000c0e041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 341142194 1250 341140944 341140963
    0xb09090c030c120111160c0902180904140d02100c030507051605100c020a0201020f162c0c0310050105030601120f0f0e2d150901090807060516080108 66
    0x30f000b42c011450300d1101c0a40c003110111500d2401ca03565020155000340c2864446041143d004400500001daa2001442039940d03594400068000308040752007007141010000d40b054900507410000d4901a640400c00741808111b41e8010f043c05206101c461002c0714180e07040c8109060030002013000460b4090100c4014100b0010501d16140d4242841440c181c2c013141c486100f82c1c03510701ea968090340c00059000c26035101340d0031501c0c02900601c1c00c640720103001c41146202040c090050016008010303401c00c000174038840e020984c5091405542d00410141c441c0d21011900105010101f181440746801034842030800d140b440c200080000c1c00381d0311150314140702c1c960360303141c0103d401d0050300a030326500280002445116a0013900c5620b0791706070b0b0110800314107980c04c6110035400404075400c1c6c6443c0540075050080c92070341c802802e101c0060007007409550340c0c4580c4000803a490054070109000d0b020014480c130300749480c0300b0700d60204d0359101c013405080c42c0100b041c3c0c04002009040e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 341143444 1250 341142194 341142199
    0x7121a0303040b071e11030d0e090a0905030d1112010b090105180d05070b0a02010609060f0e040503070c03080306131811060906040b090405100f050f1c060b09090c030c 74
    0x6039015242002d1790840d56068030f0015030940001000203000c0400a05004403d08409841d00c1d480d40c0d400564012450001041e0881034090010710b41c048554031030407456020b80b054a1415130481100c41c12105d001644618550001c144a546c03500d00311102c1d400341c1f40703802020345080320410001e040f600440307614010619551545c0d48142d01ea0080c1989000d038401c048841464903603100c4103498100210520040d1320f0f0540019032044140620004c965400348080e0f0740500b0700c00701e0000300d10024010b40d00751104124410000b20030440307000041d8000d4986c1600c0303007006003c00c41000c407210964051349003440c0c440f0194080044804d0403a640c00405000581060000b0541d18092148019444613020800180c90144076008208015041f00d0800c0155a207400c07840b07150043d03016071000d18508070010b00880c2001e0001c6059060000c0c03640020700204218410303003d403400760884480e80c0381d100000700e40c20201c81c016000150307003010704145080301010940c1c0d156811516032 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 341144694 1250 341143444 341143447
    0x705061c0203040c080109060c080a09020f04110408030f07060f06030b130302070506070506060406080601030c0e0a020f0a0e04050601231608030103050601140d0309180b0301020307121a0303040b 86
    0x1000c04c0b8502208100a01c070140090107403c889050810040424240c3c480126100c500056a07169140c46111880365008141d240410400d83c180001007c0c024141c200b541d104000109800e030080000d040303412072050804d41e80707410b146440002d1303640903046006d034542440c401b4070004401400c9103910072541d440712a0081410b08040345405120390000d41c0102e8001031990a010000c50468801d10003a24140143c9a50303000e85681c6410074030014000b01100c070b409002920a190307109400c924141405410f200039451107200550041d82140c4c040b41019002078010f003401c1c05100ea005030242003401d0f8402c0c0040b134009804429a10306044c50800042c901d8024102135502050280c00015468596840740b83c040e54070750080c080d81e040c82d80008248d86191501d90041d900ca1076040d6184581c0c1e0f80b8010380143c1c08071614104480031b0b40c813851110002d403002d2010f503200d0442562a49690300003074801d40101c550900d03031050819148222101d054400008075021104c0042495 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 341145944 1250 341144694 341144701
    0x50f0f09030a0b07090f053a0b0705040305010b090411190b341101110a05010504050d03150b040b03040f05060406020a1103210a1401170705061c0203 66
    0x42d040042460707000341005810000c1c05400c80d40406064240c4d1a90000e0309146915042044018803150784145a11642900c1c2001c1c070782c54801c44404a031780c604c114001207050b284d5440d100d0076801c80f05440010808101041488400d0140c00010041981e22030054201600c640a0034004100e89500640c80c8003034400c881420308040100400c4444241905c0b80007160001c005222080c0069026180940b98400c04108010301c10000030b5100c8041c40301410303085c00648a420352004080494026480c6090101d402070095171310442c03082c00a0405680082c2d0064201c0b6600c20300c800141c541840d040c451040d030f41c0c00306e8041d40c47d6030700000d849580d603180080850b5409a80107003140074100611081181c07903000b034064089913850306a044401c80304950ba99003d070f41d401044503407a035140a51001e8200020a411944005010030301040f601c00108002c5001c0e0f201545141c1400c62003c0e0f40f030760a0120030050b0004440c0301d89070000e50700c2c600c1c03d0060848040507089a001022 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 341147194 1250 341145944 341145949
    0x8070f0905011d030715030b01090b0909040204062606070c0f0b060f0d0f0b01050603040b0a050402031006120506010f03050d0e01050d0c0c14010204060c080c011d061006050f0f09 79
    0x7003e810030001011115040d840c1c200800c46120280d10110100f8100302e402152980035104080964001601e841d09081c41c040c100002580094005d90704182e40350340114030240b030b131107800c0c8860a5a900041241030103807061440c040006104201b041400e00340880007880c0c1d05200e0f004a82c0115400185072150000610b07280c0a05010036401070035203844074100600d6000440c24103009100c608410ba98074400d00065110031900100244020000112002c4581d480584c009001034121884014118440340441c0c140fa004402000c0041c000c41c420014100059030140c903150076a84006480d66543da540e442d110485034080c000091000821a4440c4058800d9007000d103409000010081c000a0030f0b180642a0036036903008842c0c141c03400080305000701c0302111455600c141c4000b040307459000c03940c2c014404203040e035503c0f0f035144040707d0080c108800c1c585900e031000d014581010141d03241c1607080c42e4403941c18440305024280c00b01f03115006541002650b4401c40f030740c03038001100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 341148444 1250 341147194 341147237
    0x30b0a060e062d121005040204180203040c050a0b18100f1b050715110a02030709090c0b0705010e0f0601050d0f02030139031b1b0c060f08070f090501 66
    0xc03240050f03001180e41031100321600c1400e401091040580c050081d29075003848144d1055004200d03080310800045010155180e00039540075000f240c0100e4a1502c0d0750000f445049146d000e0710224038040344003441b4042c04000055443c4045900041001012a0182103c02085030400510685e0440c8000450407003c0b0050519481000e44605c583c030380c00c441040c10002c2c5220030004811030b20705990035400080c0b0098043e0000c0090200e0b924140480c4041d002541d005c80f02d034400c50000090b04004c003c0903062461064001180c028540d80000d0700e00300d0304214140e05948070030700400554031850307803203051181c0114210303111a80c10f0011a0250020724259100707d802d000c503d060340d50f0358060640340e0b11508030302c800141c45030803400c4040e03c13a11891001141d146000c3d04601c18000d11020030001e802c804d48800300801500c692010002590088021410b12444040d01790340c45a80603a03c91210b04200ca05821180801440700150340034a90500ca09000ca49010450108 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 341149694 1250 341148444 341148517
    0x50307060c02060a0b0319080d150f03020325090507170a1a060408100e1f061d010602030318071203050c0d0206070212160b07030b0a060e06 62
    0x400034010200c1d00325009569400c215101c000746071806041d4845803902165102480c0d110201c6008100c0460301c41c212903500c800d940d01141d551301e0440000d1402003001100c01030203e0040092514998014181043c9401c034043c1d035144009500e0401d00307030902040310252000300200140039524440c050b200008050b070082c01400840c000c00c15144020340180b11002c0c2c269041d217064801880c10301c5200d000314040e260320303508648080422040d0681c090100c2a006c02d003111001c440c1d140104403d4080f2501045003a134076050280841c0c0305040201414521117180280d940d03141c04802502c07804050300c1c09545500303401d14005802020040300d80a80034060081130800618640980366038083d018426030341c003c400f10320000c0c4d80081904c9104060640240a054000700404a502e601045006400f880d0b0040200c0c0490780000301c681c4039004a440000b0644911004c0059881d03040c1d00c010100f00d840c8841200588070f11081e10620015121182d5090900485a000103004103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 341150944 1250 341149694 341149703
    0x705310e04050a05010b040b011d0f060a090e06030319031a0405070c0203150402010f08040302011401060e120607051c020702060a050a120e0c010f021507050901020c090121050307 79
    0x1410700c42841404a42d148455100708003c01400c280c041c2407009884901c08403c0c00700d02242c11801e15142100480e54860340020002c2c5203140303e0700300107a0140c0080d034441d00051980c14050005001c450300b044e070041c000300c1c0114104441c900841c5d40025010000004040d00d88289542e801110165160003101c02130050045143c0344000429035442c200069100348101034840b81100880d000b01070046070107940f08641c03080c0075081a101c40c03102500803421590390320003030740c2d510a440b605140a482d0300d5540d02c0701140e02c54200701e4401901d52650146402c601c042c0005640c11504840314802c2c10864054807081d0448140000d00400030003a402100000b040b42e1003603403200042c207056280d074071080d44a1241c05840c0c42141c03c0801003c8050b4060386501c152507004403006148000148103d60a003244028007201c4c58500303440d0440800c20100d49914950b805008240a415050b00c030074000f5850500d040140c40c1ca0003405070700041128031140280b080a00448a819410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 341152194 1250 341150944 341150969
    0x30f102907140d09172805030a08060a0506360603040b04170a0801030f30020f010209060313080f071b060305010e0412020f24070531 59
    0x1000e00d40b40c880c00714200b4030001901d0001c0108400d0280c0700c5d00c00d00740100320010b0100912011400c1c143c2c3c20b010202403000340f0b00486003030004a013000140004c058559420714107040c86414080341c41025040541300740d5043c09a03105c501c1c100f110101880344036070f80e0030004040c04024600c5116542e4030781c03030b04140000100414003009040160003203106602d0304030b8241a542c5154828010310a1070340001e0180ba0041005c80c20884003421036900950003c4541c01d0712451900e0503020072242d61907140000012890000e030148131240a44184200942c5424a0580010310070304c4000c0520900102104050341409044803e48074080d20070f01d20183d8034102418441004507452201150010240f60080740441c031900503141240e031054254442d9031030742e58500c800c180c6841c0003c0110f210340101c40281301d81c100605100e00c41e0030039031181c5890702c08000f444000c000078021428000204440d2210260b59012640c200140d6071a41e80c140d018800c0e1481c07083d030980d0141402185 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 341153444 1250 341152194 341152223
    0x61e0301090320030c0d0305101d0f090309010c03050d0204150801031b050906011b0b0c13090c050a0c061119030f050103080f0c070902070503030f102907 68
    0x8020150107115054580c0304101e20a99056096403441580d08101d07041e04206d100c1402140030750081c6410948060450201c2c944408100c02c000d2002c1462040304d200e2030044c0858182c40001890700090694090742c540041e401c0040c009684140e0300500b040000507504081b80059810766000e00460140380250009900300201602400c0c04241c80104202078007034280c0748202d44483c11a01e01614000141d59810b0041d180b2440960748030480440021012000503034080302c01d8418080300c02019261034034103807001c4090583c0e4215041d110315019402200c04c0d003000039581701902d40d2500d50321301d040070325000b0302514002d02c0ba14980e20010850005410030010400580141650300700030300f000c0d4000c41c4003070395820320020302489000c00c003140c003650924005110252600007251141c594a280031000c0f6404042c0548064001106004c1e250f00c4024107550010708403042c6007405810401c10030b5101c00c012140301d110041410b40c5480c90803005082c0d58445400c585218840755 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 341154694 1250 341153444 341153447
    0x929090a060c051606140904021323031f1107050a0b04060c081005060a05090d14150906130314030f010305011815050403020a020a14130203040506061e03010903 71
    0x1444020031100d5000e03490030144c44d94402c002d61012030310740d944e0f01d2040c0c2c50703003200d144050703400550615041034080042604030007144003081c00801038096041300c8050117600da100c400070420800c40c03080d00803110411040c040081d4120084011010000300714135102d0b4842e1462140c61030041141c028520b426061002484200c2d00c9180204010b10040d080004221405207049945411000104806001a04044026017140307a8982031a0b032030a0007040000c0c844100d10070341240c0c10140605030100c2c8410500065001a55030005030340f950500c100f519480750030040c43c089620302c40002200501d8854a05180141004025a81e80c3e040c081407584410000340001e03900340d0700304800402c595481c5203918481ca90410381040e9a03c41000840b03003e400090070a40442c4541c180c13100c05690b5207003400009101d118608902d82c0003000c14001c0b402403142c46020424410320801008c1600800c4d05a1300160856488228096507464803528010301d04400ea003546c60320071600b0415 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 341155944 1250 341154694 341154707
    0x20d0816050d081b040e0f0714040b090a090209031908090a03080903011b020a170c060c040e090111030a0b03010e010e0109030801050f1f03020403020d0b07030c0929090a06 76
    0x41e0500514164021003042482c4070361711540c07141c0b080031540200003811401c0340805254000c0054030784807030290040c82d01d4003ca50000d801000e031980e000100e440941c40d041082c1c1c4001c02d240c40e015428000b0700000244c81b80076039024075040074603a14443e401c200155080f2400c0100c0104111422a100e050402c065000041500c1c0658030b40402d40001001c5c8a504140e40b43d0b140d402031a00ca0040d0356104030b24800302c4400e407440f074018032141e906001d00340701051260b0040d40106846900d0203075600401c03000038000512036454844005a03038030300c0f10100c03548400c5191020400c46000d50200f40100049084140954039005514284c0c02d0706402c4080302d58020703912150a0b03601c490401c000911003150f5580d009048030b0f07421550340038013010007940400600380141455170303c1d0045008455140421074480c003000041200c04c0c0d40600ca07048600115203801074041e07041200c1c4801c0c10111a00791004031001001007527041c880e000c212403908070007030045c802c25648c4501c0500310703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 341157194 1250 341155944 341155951
    0x1b08070e03070f050117010e0705280503040b0c0a08040305450a05090412090e040807030f0f09030209130606080c09060d030203070b070903061505090c0403020d0816050d08 76
    0x7803103103c0ca0314001d180304400c607059232007514102590303031030350401a1031a07805821103600907801c0208a10b01c41c01400c0f401404102d80f500c40e40d65908d018904003202e450014201140000d0501c4494009680059115405640b6007060f956484902c0403425060245049180007002d007442c00301428054440741d00e01c1041c6d81030503e0542408001042104411350158680000e807241c000b6020650722240c00c0b000c0c071800c0c1000c0c2401c07500c403240d504140304110b03800d85d0004400a5448101640066118800c01d4140f80590000e4244070000b48812036500c8003034407d078010303000306801c04c440604906419910030800c1010540e9201180d4803510b40c010f9a0740304143c424002410381c00c299084a40c01980740c3e010310710700884c61b91601c03400200038100c2810000039100c08400140c01d440350400c2d8004030315040c0c6900d4a000b040054101008141d1150040103100400c01a12401c4c00d07200c01c507070702078403448c0c94807907551501c0c07401c00c10381d00090a544960f582c03011815030019640ca00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 341158444 1250 341157194 341157197
    0xe06070e01030e19060b0d12051201050108060d06051f08010b0f03030f070b070507150e070f08030d0506240a0e010c0c12020f04150e0603011b08070e03070f0501 71
    0x402c0d040011841d103070781300c801010b1112003410f80e0707101c00100780f0b5018094240c00200000042400d9880307000c130b0340c80c031031402502007040003030f08007003140ca6460b12500410092a014855107400f4010940c02818608000c02d0541c48101007114901290100085400d44601d5410701a98440496028060fa100b500740149200383e0b04044505000c412101004007600a4600d012250b43d144108100024000c008001090090100007041c007900e4240141102002058000c01c290f234040c1400d03a0342d07004a4039aa0100000c01ca58840401070b140380b1910a4400141076940002181d41c051034107080500208000c071001718028000301c00351001d002c0d140d4440140811010054642c00705181018010703120065003040300000c0b43d00001441d80c4003030100c030640212000400c054802100f8a5904990780b0314060205903020102a648903208070004d0140b010005038402101200910080810244d103000940d49400b0b42540402144c0280c120b41540f6921010342e114064240103150 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 341159694 1250 341158444 341158451
    0x2802031305120a18050a060c261207030c02120a09080604030804030207060201020c031905120c04050102010b034b03090a050d0c091505031912180e0a0e06070e0103 72
    0x42c5130300f909400c248240d4101802c02e180d070324200f1509445000000f40d0403103d10000041c0204854200c8160083c160100700141e5140d000000b08041e80240040c6403804051a245403949143d50001b10f08040cac204a60403280c0e5812401c004032400b60072600000510710480c014441059403004195100e1070195081c3d035006a11108100d0a03807148617101d40942d80300340807011680c03180012482131000300d420080e1401c180e1400340f400c4c1100491f0801b051080100d4100401c6d60280503801188500710050500703001102c3c00080400c551064019a8501c819030250307240386450240b04940381c05940c0054580706a40249035243c0c0000c46040c0681034220b000106401c02d031b000141055800989207000900304800b85000b0010100c1820124050840025403510113201480325001590800c021010f001d0070581201041e001020081040302e60ba12242c800000b451481507a00c1240f546050b80c4131914014003420910120070100d004203414070000541000d401240c002081c1c8003032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 341160944 1250 341159694 341159717
    0x31602010509070b0a080c280323010e0402030a1b061e021e0304090c0c0b130209010b031b0a020d090501020d020c0607050f15010e2802031305120a 65
    0x21911410700d0b106506010200340008000c0601407104947d105002d191f18504060300406505003010b0300304001780f8900d00f198502266103926001c0c0103141207024010b2400701c810340c0386050090348144502e21b0820511004201159414007841e030005411081d003c0b20944641401400c1d5041881860041a140902e650025500c8010030b552500550041c010701403005042401e03ca8882c818013925000400011500800b01d2103000801002c940d03400100c0b48880c5000140c41e84040c041c43c24000303002c00a1030040c8c3d0340311620360640d202036440395203a07121072055048807900c0a20003032540001090b01c2e440f0703030b60025181030300600980d18001c0c0036541c0d40c010398071075140754514001a00805007900050406000030541c080c4107504589408010404880c10421541c4171000d041e104140100200380780030b2101600401580004031411001c11001d00f0700b105000d0201e40421380100004a60040071901a070302190400c00761401107116216981c00c0b03a000181c440c012034102d0011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 341162194 1250 341160944 341160961
    0x50c190c0807020409060905101409030705070618030213090302010f0e1009050309060a08010509090d0f0c140a03090513020c0a021212040f0504141315020705030316020105 76
    0x81030321aa0092141850600c0680074800a8002d00c1c009850680c1c031a540ca00000d0801c01001030025020b0800244e02d10220322031556012340035082c0007a81d0320030b004982c00300e40d001c901c8004460b81400c00c00320b02c401144810340c82001540c0084e51080180ca06001004800c0d00403084e540e100ea8001c00060001c40782410803200c0e0307203200500540c081203000c8004141544022145809034044034242140000020541d510501c028000184600c00400007030415200c41500280300710701500b0f40f0344a202009109515080c00c40c02004185460103051004d14031003d001281404140d07800213801d81805803401d01c240c412240a2101c03220a0801c0305024401d992402c5000000f800c41c45520ba0200403041d81401c058600340c0c02032410711650241c0d5a8000d0000300360445040344201d1030a4100b00072104a420ba1444a441000400110719045803800d01210343c0030041d4201ca0041003c40f00090040100c0180a13100010910101c1880b514a036000c16089500074002c1e50f4400e00c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 341163444 1250 341162194 341162207
    0x501060207050f0904031e030b0d0c050a06020d020604034406060906040e061807020c3105040606150801050f04061a1c05250504140d02060904050c19 66
    0x1400746c00a42c0045444914410000e0104c2d112041403501050341d603e42c40002e4200c0c0d0644501b100c0c40c10000038100150300301010b241000301200e0000d4007006003403400294440000400040400420720700902402c10900b282d580b80c0004200000c841c0704a5409903003851510703e20885009000200103801031402c0c0044441043c0043c1c02d042c10145002146041c0c100041d00e0154492544904c3c032071522400351030f02c0e2207080c5d66401414200180c03800c3c0305613800c5129540485a028402c0c0704134500145044000d1603010410001741a90343c1d00b804c00003404150821644060304442c0102019031003074203d81a035400b01c8582610b98500f40030841221580d1043c0303141ca08451804150220b13412000c0c000034100008005d200c0d2040c4202441141d000300c0740119400682c10602e41c9910301c20400c507130b000805082161800e81851202122121140340c2d55100782c188192401c115101c82d01a10303c6100c000c5c3c814030050804003500000c0e50803d001c04c0303c103200b64044204250340300e500e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 341164694 1250 341163444 341163451
    0x110303090c09060414040506040606232e05040f080a050a23100e010506030601050a05060f041d0402100f0507080c150f100801060b03060607150501060207050f09 71
    0x400400c528240c41c0d007030140002009100c29030181d60f4099500100651494862050344a9400303030825103440d240803c122000e0350003c205c0c021011042b0f050101e100381e100f40740e90400300c800300c0c141d01000c041c5001a0200c00004200c5050102d400454160414040c20540302e02d44900700080b0740302c4240c107640d03128901c40504107901450901c0301091506003200c1c0c0e05d8658119544250028014062074001148510100c4c10703540c0c0702c206403150081c07285075008082100502007551502002070b0401100f07000700c078070408000a801c0b0070410390388201d030000d1040c0d00d4569440b0301d0f201d4250480b1441200c050b030041d00300d200071001e29403040300d49081c03200d8140c480c2400e048541d00c52a003160441d0401400b14410b003a40355403807407038000742180720305080c140c00503191600c04401d01d80000c2640c040741030341c1c1c1481c8092020220003000c0d2980140700f0350b001500c5440d1400c003150141030030002c02848034034010010425950201d5a036065907407c0d100e02411140b40e4051014000084 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 341165944 1250 341164694 341164711
    0x30a060209010f0206042102030f040e0415051911071407031403040312140403050f010f060504021c0b030307140706030507140304020d08040513060f05010203030403170601140712110303 82
    0x40d031900ea00c844800301007c00b9003042e8812641099051030141e5590b03441600405000300c0c0d050100b2041000003480c1042c05020990140321b0303414254200c422240c0c80c225604032503500c5002036100c400742c21041c0c03074902d90884540c0900f407501c1e1114903210401d50006652444c00b10030300701c40180c0008200e6040343e2703001c4548000b01c0d045001c21514120410315150441808103c000041001080301881c0d80724044000110000208002c0c41260b400e603100b280114018410082507001d81c02c015090381c100088049200c0d074000300040e007948030703c100040a000c2d40038a10a00319030005140303005e4503c0c5071410041c13a00c0703c0c1002e580300c0201c2c1c84c504061110410010b401420201c600803180c0e4401c0300d1050419440c0c01c0080e01c086101c0c06903c807490754540003082940701ca84d03041c000914083c0003070740c514141524014a41d00740e9889541c001c90a10002c503440b64416420134100308070810a4580351105490900c44000034800317408000381c42e5812004e110708010085a01941d0305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 341167194 1250 341165944 341165963
    0x1c15060807120c0c0f060b030d0e1c020f03012307180b0a03140903070201090f0f0506030c0904020d020c0d03050c030a1d0a121b03080a020d0902030a060209010f020604 74
    0x900e451040a0300b00c43d0300000c00c200b0480e00b508001001e400d401c1c4c0d40e061061001295110400c0281407034030f91001c07210020030540303000c0b2541c280c0320004245050f1500000301480b110310b42c00810403800118100c580c0543c03900b0026200c51112032583e0686008030702c007464060b281d005044405850601016290700a9144100072584440005080d0740001d4200410783c5080a01e4800010078212240800f0b50000500d07942150f0b4030034950030113041d060407106540341c103042c04000c2c8003285010b014060b030000008100e05404060945020b004010000c1d0f60701c5403112410006034104907410422803046200d03044400e4028081c0f01d1248081c0f4510b1415585c54403803a901a0041140301c0d041c00180003900e80d0554028480000c8135801209100302000500b14001d02000c070850443e902d0034a000d01210000f98003410403500024162000350f2a1002c140355800101100c43d070080d0716205088401c01045202d802a14491200340c0300c40c681d1180702ca070241d844040c120ba008008c81c59 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 341168444 1250 341167194 341167217
    0x30504080a21050412090803070c0b07081e0405010e1e010f03020403061407180e0a110415120b0307030f02120c0901030804150e010c12051c15060807 66
    0x10030711030620210710100000980204000c84207085070400d81d13094030183d070101030070541a9000030042d4000d001440081d494890140c9560200c210076014403c0341c4000015100144451030058482d0340090546a180b8141c6641c11200d1607805449584c0c08542c44000400061501071601c2c10030801030f030b00e01010440034070300440d06094480c040350149035090001101261207841405841c8098451000203420044c0020741900800c4d0b00000b01d5000a200078400444080d034103503006444183d0104e40d0b5650111307c00c0d00c9000b00e400c42151108407160410b00944d1003444c44c1820500f0311001c1283c621410245a1507d00300e00001e04440c02c0a00454014100038404c0951007032848240e030004030300307980010740440302a0700954070000042000e004042c410340002203240d40c1c0d4140321551041840020384241c0540c80c02514420101c1852074405004004660b50202c2c1c5003e010200801d19a10000914140185d00001d440384400424010f0242546600488a607112180300c40c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 341169694 1250 341168444 341168447
    0x80a02070603050a0c0806130f090c090e0610060c020409061103041202030307210207060c0c060e060f04060f060e0c0c06010506090603041e050a03110c030d0f05160f030c02030607030504080a 84
    0xc0888c0045072059880390341c0c52a950042c0b00d1064010301c228440c8041c0c61400644105907550408880081e400c1601400345c0041424120811200c05003481d039204150303400041e0040c00140c0b0041c0c022410021009100c940b114000c42c07041d4443c140702d80d440010000c00700e9990000b211a03002041440600c4141c14160741e0010501021404015140244030b0355202c065442000c072203c003183c20904040100031160042d403100f50001001842035150599584590400c040e002402c4243d03560200e50704a5841d4016401600c017400c1100c100c0e051804151105074403008038441107009900000ca058a08030303084400d50000144143d003145c4580e15001707410501c0d0030803d180034519040e60780006070184442da01490080d21501d804d610840310741428608490780f0740d4426049107111440494229888108a010074a0020388525000400c10301c14517020002500611604810408165216110400092003074040c0d03170700b03078903034803019010ba482c160380060204c00c0c141308000c11306 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 341170944 1250 341169694 341169709
    0x1221090109390902030403080f06060a0c03180b04051003020f04090b030a171b150426030103150605010c0305040b0f0f07380121080a02070603050a0c0806 68
    0x40c02c408441c0c0031912031240804220368507a90002c076181c2d80220800050540082041d540412440c030a4034031490000005203840c41500c07201d0b42408110407030f280605106020756858105c0564082c04815107488820718a90064441c0764460b0300080c201030515446030013030305e01d51400c00f2080c0f4105070411590101038944c0034401c0e0781502c85d05040c080855040820841c50f121103052103560740908054101c0711045403220114981d110b1507164107074410441109501c00e403c24900800c0209481010980544440000d00d8440e8080300210502c0a00e010340901c02e02045000c000341c90b0368400655860403550300207000b0400a100400900d0258802070016124464606142c042000559600c5800500c0152001c80514800d030100b03810b84401c80c26a01206034110744101144c2c508442144414001d41500e44103581c052285028403e541900703890b440703610a5111030f40b130346000b03550310f01074410f02000a041030301142010078144610743c0d126001c2d60302c103003440c0c0d100801d01189 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 341172194 1250 341170944 341171003
    0x5101811061b030a030209041a010f0c152406170103060c021608010e0105010515090609030309060703180e1b09010c06110903160b0405010804051221090109 69
    0x448000d140c01103007000140f0082180c400d4940700145c595802200780002c076200040b610103000d41c1900c0010440c2e8000c44424a0954070b490300070300c0b0b40c0b514640364040e0070b00217001708072840c00e0684120101034004c85640e406200000f40500d07913a07407654201c4400103d043d150441c082c20400500104001d03401c002c4030b490b82030044a00010b600310b0103840791405503001921a0755980030381e070040030081c02004d0040a0458102c42c420000d190483d249102d0020030740c0c8500c000050b065607503103043c4242c40000030001c2c02552195401c4c100501100c403003003031002c60700746c4061002c950304d00c41800140c040c03500e52155500e21320b905a100006640060034550500003a01044400104140109940300301c12260700341e2a003c9a000741407800002c003413545001c84d40c951090044603104400d0f142101d01c00d1911048548490070418188180c0054118820000085125900702164901c0d5501c4c2d200c101e00307012598a050045003241c0c505e200041a0507080e411b001040303111024160b98 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 341173444 1250 341172194 341172217
    0x131e17040f17070312080402030f07080d05090a05030105040c0302120303070e010c03020f0f01150501020606031005040309030f0c030c0803030f010302040b0f03100606230f0307031103040510181106 87
    0x6081c0d440780c0711140040f000c088403400240d411b40401003182014400003040140540040180509201240d601c1e91740d46400c0c02c0c00c0100200d0030f45107a503102840c8200404001e0020001400c01d828102a103003c1400160f0181381c1154642800034000405c882c03150000c3c1c3d55140ba990070712401150300040c02312060301184122a04220128401e006504440c00740c9800001e10140e83c07040072800302016800315040d504014104041620041242034442440d480009040d603507519069600f441141c0015204126104e850410091380e0a160400d6038002e100140c801b40e034407c40580c0c0e170300c000c4842c0079600c800b50004200600342a002580924001054014105140c1000c64030304444040c0d80039403e9110441049140d0b000b15501803082625455400690120001c0c01038510900385400d816078000000a402e0314800e80c0034501d141c10070410140d4034181410990341e5078034146180740c03026291603801044446e002d41c0401c55581c0c000c030b0035500040340400b0050740d90841c0c2d09185 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 341174694 1250 341173444 341173453
    0x902040204090c0804020111010606020c1201020f0309011e0b061225080a0c0e0303032212020303060301050106030e070b1c02030115021903080c03131e17040f17 71
    0x3402c90003d004000e601005581c543c10b040c6014000140620003640d01c03003000b645440c0c03041c000b85602140d50202d042080e1001d14064080d00905030081c440c04140c2400040040b052091728001900104501c1101c0e901c00d07501c280002c82e1510407510a00b800a038400c1080040e1503080040a4205901500d034115400110011080201e1034156203110a4006103108041103150302c114400c4601089140c50608220103001c004079550b4800608a1034024904002d00e100d4400f040400c1b81d04146d024601c034081c0030b50b042d4040c2d901d401c01d40e0254130039400c0c070300040b58a521a01c01d8040e5580d107007009000142c98284049000d030b018282c6404415040b4108881703502d00c5000860080c415604401016500c2950003070500c0607049016045072902001c03c2d0100f540108103c0d0001c80c800d10040d07494888402034002c001c0c030000024162002981414081e10b514a940d10085025403d0011400c1504541400e00d100318003034a02d0186036680c050010521000a01203c013045004a5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 341175944 1250 341174694 341174699
    0x3020901092003042d1707060e0d0219060f0509031b0a050a110f0306010306021b0309130b060d02120627010b0c15091c020303070806040902040204 65
    0x420000090704190051501c0c0d0021040440900b038425200c042007185040c194101655502144201c03803c0303852403491800d841a4108104140301c204c0aa0f00c03400c03151480c14034031403194540c0c2040d00d06680b030710320306404424242d102040c400040c0d01c8580c0a401e8540b40d00c2c0404000c50301403441a25525a60703140005004128810b46006110100c01141ca601d410b400c0207a40c5042915290081d801201d15040006d4000a240b00102d0740807102c2e0030030864a001041a00034401621176040c4a840000010f100c0d40768024851030205c2050113a02502940c1c0303660340ca10a12410f15013120f10410f280340a500640d008001c0c2500007459035180c01f0500313030b80c0400c2c1d030002000c500041c0d0690f403d112a6180004880c0141c0c0c0e05400c3e00740616500d00e04454081c04144510507482c0300014070b4028020050002c2e20001d10034072128109400c004600b182d03075103004054092403070115610070f1940c0d8000400e60b4403503903140da640e0019070f40c0d41c42400082c2c003040200b01d03041a001c3c00302 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 341177194 1250 341175944 341175949
    0x703060801020c0a1b0b0d0c0c0803041b060215040803090c060c070f0e1909020f040c2f03041e0b0304050d03060f14060304150905030c1203220204060302 68
    0x703100a070f40e20002004501e840b4108035102400340740383c055036030703444403003c104101c11203040c1d5803016540100040d80b4810340009481c0701c98000401001c90300300104110412089044a000d000b199008040c50700d0303114141a0380e82c0042052466800340c00800140001d600d540065a00601c00c00958058502c45004036040350072004a0000b9500134210600203210f0300c0b000100104540403102d9200c0c00c0040c0d207058410100764503a0450b84c0c550036100150345034000060301e2443c01400400c0603940c3d00000400c41520b94034500354180101c00f20080b02c43c07a901280000103842da028629051501c1e1644040c10a1580c84038000d00303d074240052180d03400405144694003540c00340641000401c0d0080440d0080d400c541d0a05504501c18441c002c034800800c10580c41c2038031303219a252150708000c0510710300324011400890400480c18200040030003d4856880c688045a6030300c0303102e40348140c2030300003140d01c0040145c0c802c1c005c00061a204000350000c41c0003420004859459402 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 341178444 1250 341177194 341177197
    0x40602100e0a0c17100c0507020d1a01122306060910081b0f150a140702030d020a051507020604020f010c0b090618010212060f130e0109110102011e05070306080102 72
    0x1104461450300c0543e41d1409409000403010081217000402044181c2c0d4030140c068040d01c00041c0c0101c003210304220400c40d405d0303001ca007640100c2c00c040c1c40c03d681d900390741d10381000d081000b250410004038255000e04c00d003840c0522182207007030283c80c0b10394406003070090034240148056085881500002010a01480781c00302031250074194007001100181402992082c1111260044610354004800301c5220015030344003a05518140c2d028040000b400301190203260390103941030250b900b80b042d900e070300080c0300c03002140302d001a11400c001c0c107400b540c08004122404400368211800203001894102c440c5041e0700d03c14102000103c1d4691a0700311680d0003240c004005134814010301c100460415001c007030344014a802585040b0f040040c042084502500460164400039200c6006546103600541c9204140c00200300c4a66900f0303816020f4032041500303440240d4603010b1209254810b000e59a180e02c00e070f1f07105e1050700c0c801800300c2c0028200103020404160ba00c26011401c42401e00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 341179694 1250 341178444 341178449
    0x611040e0a060603140613020d060807091406120604080306270711030a0e0904030e031207211704140f031209150103060b04110a08040b0c040602100e0a0c 68
    0x1c00590a410800082e04649440310700c2c609400145040241c80c0d40c0c3c07980940d06180110307038050b8540300414080c001400503a000b00b403460103803c801003414030003a4494048220030903168041a141c1c4c40c24001e000d000001c2030040381d00000d00080201c2d600c1c00085402c00d0000d4051861039060b040c49040c0480720602010504a040e014841e515902642140c07100c80420091803420300400b4001e400c0805200d255406071016800007810f04d4050b030880c1d2110130b0080d0540319000c120310010042030380b080300121003056003261010103c0c280380c00d400c04a10301e26110b02441503100068204500401001164050140850307164040020303c144241a10840004c5031030301151124103c01000007885009036038000c05540b40c0c0d10000c012140d0449801600000700664010042005030510302111408400300145541145a010700800c0c411405150810060f884000422003039204901c1a04010f900000c0c1c95081105c00c0c1d80001100415801107400015040e0b480380103906155 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 341180944 1250 341179694 341179711
    0x308060d140a1110020a02040b0a0302060c07090c090509060607060615050405090a02071106130306060f17010c08150402040f0603052e12030e031e0106080304030c030611040e 77
    0x2100c1d00c074100000d1101800c14183c040711342554900f03070500025070300d0180344c001a1040381c80300c080c03d2417603e841c0c0c1450061030b009040581da84014007403865a540c030501c039a400c0f045c1780048498600380304490f5982540e800410868050b25801c0400c181a000382c6820b544c0c4030746c0d4030f00001d820f040b030160001e901190350300da41c0d844603d40800c0000001d401450780d49070303d0041000c0c1000450710307545888a0390046400684861201d40243c408010130b070401040c035403a0040205d80c1d45502070b60041101e000c0c00c5448950440d0680040c262171400c512003022410003004228031064520f41500c1c008009400103003041d54580c1d50000e500140c3e4419070210b50394100303000c00020080d0010380205a04c0e50307a070b01d50036950240300c0500f0071144210701038403060120740000c05102d0150283c11410013021502036029141882e42042101034800201e50320341040040c002078040151400c80c0e4120380b100402e2841c1da1601070151031281d038140045003041002040d6080350f00e881d280138001c038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 341182194 1250 341180944 341180953
    0x210608060a150e0103030f1e0816021501141819051303020c01031e09050c120d020a0210090e0a0204051309020607060e1609051b030408070308060d14 66
    0x60701e6411900c0d040111030b036201c8101070512070b007421400914110790341482c11030217040040d40d0441d40c0e06900814294041101c044403400903500184990060300841080d4a010a0422060f60f0354a21468003501c9c01031088010045031031051000c2102c05005040c14072140010300d0f142241410440d1505004001091004c4030310209120301503001c20005403030038440c0c6407038902070b540350000c0f110303e81055155204400381c0020101c01e031a40040054085c0609500e82c0b600640700c202e1844c6a9000386c803814802603c00307500042c5240c4401d16500034201416158080c41071341ca030140407010a01c60b03c100c00140f0759951045180c031409000000680f52414513041105c003800081ca03075181241030407500005a605c0300111040603901c014002850076010300d010341864010242c030752103107401d903000045410740c071b03007105200e4000300c100308446d080f400e0445019070000b07a40c050700b1320200303100c480c0009001e980c01a4006100803e103e001100e2a541e1301c0d01645440d410311082d400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 341183444 1250 341182194 341182201
    0xc05030a0c0e060d1a10030e060c160b06040e070806090d0e010e1e0a060f02010b190b070602090a060e031b010e0d0204140405030705060f0c030721060806 68
    0x40c41d1140307038442102868044405054100095001d001c1c019448540355a5035011100409404445140c090005000407500c01040440070b001003050000303140390390154400240c45c0b808030004032420040589112100c41c07040c0c0d2203c40f2407207070081141b0b0700aa507402402e2064001000401c0080a0303041c000c3c4107510b044502c030307802c140c8429013100500514a8100400344c0e04071800b1600c205003a00d141384a484030615040344200030080381034211a0f130a03c00b095155101c02c0c03400a000d0a41c00a10295900340c0c2400b0500074040c0350300342ca8031140ca0050120707004d0b1000074064180175444c090309105e40703400000c24513903c0d039000b24041812007010341020304043c800040c06085100560320009c0000300007811198a1442c0544141002c0d51034000310765030341c1c0c4501e00f081c06e00110698146005d06d07185a89500c040750599246c840d074800102e4441510714000c0c40b600340b540030741d82035880300308040d64102250010b4030007030501143c88203145210f5200b01c100604480006200504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 341184694 1250 341183444 341183461
    0x9180a0518010e060601080402030a02121b0f0607020409141903030e011e020f0c01090b0901110c0d050315090a050117030403020d080a0c02130507020601090207030804060b010908010c0503 83
    0x14041a03002c0e4184034008009010104405502803402c2c249030309140d480d407000900307040181900952007070742d900a8040705280010b03419848001c02c01d03030040c44401e0034100100c0c0e02c0240280c940c0500200000740040c20647c001d45d840c070744600c0c148480003e107440c2c0c4074203004100d1003460300c44445109030010700d6491b020f0a00700c0c401d441b008111400c100310310403c890f0320742c0b000c00982540005282040d4542c1d4000c80d40b81001d620006c1056409525006181d840155008d0744103600f0011810303015504003088410030301d8080e00501940b1807990003a130b01c54100414515280e41e00391203000e800c1d268204054443c401f8600001040d6040c1140300300640031000102400768230500040c07005032543e681c503e07205500101d056488824410048420803203040e0000e40005040886001c904025040180169113503005d0307990300da80b074158003801c0f40503100c8040d0000351200041400305030254005880382206141140486890f0130b00075003035400c0860a6000100000100401907 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 341185944 1250 341184694 341184721
    0x207110a0b0d0b060301120f03050d020a08150a060503041b150503040b07081605030a0204090c200316120228110d02060301031b0312080f061f0509180a05 68
    0xd0030490b130b203e080d5418005050310125011a000b08910100002203040c5030080c415550b602c40800c000f0b6582c0c40e072080d0000c0c000d0302e00743c0d414451034070a06680000ca280441c03c0d241601e20603510f4604640d50b07529421419900042a0004e0204c4988040ba40207002140310744445c8440d120150b803400e0501d00818044401003e0a08000c50617041c408041c0507540d95140d0303403c2500e4043e4894031501a064000d10940e440300540500e440d540f029600e402c019214068900c0840c04060a4900c44010742c5900c12030341a1031010048000b684c1c00501a500c0c91580c800492044480d50110300c0d601c0c0e91980e1031074028080d0501080006402c110544000840b80f220a4507040803070642940490b00c680010b000007420b64151440b03071608192013172030307001c01141c101c2802503120f140100060002841501c90105500d030403400100030342008202d00c8000102082c0c100c1000d04c014200f01d42c0d80e081183c005902800c001c3d1021300010304005114050b2003071000c009110b007000032019500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 341187050 1106 341185944 341185961
    0x6040915091a240d0906020c2b053c07030915211a0d230a05030d110c1b1002070e0a0207110a0b0d 44
    0x1210b04020403100d065100741c07400308403000d616404407841003142e00407124000e02003005150f40549a4000e031100c6004107801400c21001007003040c01e120103a844001030f01d40002034031103002c80111f421942404d19084c40c526004640600c0030582942c002c07603607103d040150004510000250001080f03145c80e0000359aa00c40c6898003030035420040c010f4101032031406043c0345541b0302500c05070f42101401c140055407503c2800108019010030f18075042c6000c600d0120020319141c4d00c803004c080e54841e441290030381c000440401009009a5490300c56540582d420601186000c01101c501d10112500841c1c0380c016081c403c1d000740f0810350380004600c5103111b21000c7c200c82d800084502c240031180c200100c0d900345030403a5169954015a800070180b00c1c0030030721442540d030040c0412032081e0900c420300e8600c080092124015540301200b00200010710390a02503103481580341 = true := by decide +kernel

theorem cover : BRFrame.Cov 341007194 341187050 := by
  have h0 := BRFrame.cov_init 341007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 341007194 ≤ n) (h2 : n < 341187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
