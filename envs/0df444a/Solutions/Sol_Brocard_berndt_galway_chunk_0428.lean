-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0428
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:45:36.587578+00:00
-- url     : https://prove2.me/submissions/092138c0-e9d4-4765-8bfc-5a598bbc251c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 76798563 ≤ n < 76978419 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 76799813 1250 76798563 76798577
    0x501181502033c06060901090b070507030c0305011a0d0201051e0f12011403031905070c09020d05070206101d1b040b0403030e0405040b01050607020f10170901060e0412 74
    0x40c51030350301e003965440a194030520f1501648515400c502e800040c000d14012131042086031a1030344d000f02c00303d050762018541d0366512007081c034005280403001d81c4060810704440001108200043d0404408140220720701c03190a00c08032b0400c0328100a60300e00a020500400014007402c815104001c40d81c4510200c05040810a070381030501a80000c25120402848200606ca4201c80707080421030410140c0c003c40c1440071640c1405940480d4200e40e0080c400c1c00b0410400300401501c8dc1e01c003618920506545401e07071041c170003018120503550440503000700b40000d10f511b201c0da41990201c2d21710040301d000c102d04c00100c40c40c1a80e00509103854a141c80303882c85c0782c0216440c009200400000808554403403031401c004bc1010131010b54584218100400d01001c80e14581030030341174801c22a205a40c0e002d852001460440607000c03815040403030362204a61681e080685040079503511500d040195403400d0f1410300301c4103d07008105500a02ca00464040340003001010303a882c070380e420440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 76801063 1250 76799813 76799851
    0x12090708010e031b0d020a230109060501091a060307030e0c1804020a0807081c02030705100605010e0906030d05070c0e100315330506030f04050118150203 68
    0x303402d4503005041e4080310f51001424244070800c943e40b114000714450091303c801020a000291244454103000e09040441d070350998000c84148880c00381540c50000070000d090f51481e01c3c0b0050300302440703a8245103140007007890440c1c00300c10b01c000c0f2580c40208464174680e140c88080d4010000000350203150301c0349227550a4162602600a42103c40e41b0180703041928042c810803100b0314a903000848590490707841005010f00004882050b9066402a05008421020220714500038a0000381552040a040c055501d10607448038080d12400e83c0c40520780c1d05c01c81c080c49560751042d601c0c5501644000301c3c43c004c26200c1d001901d00c8034401d00754001c1c5259602088100004203441c0020a400f2032a020410072580c2000e80007a030340303001d000380b00e20445c0b001603d8003102011114483d00f400c840061201559002c001d1010b0600240941c0d100e040c12400c01d12188002c45c5c04590641ca01510841d1550205405c0c0a405520a4088000e0b854500402e4040d420203000c1c03024070441c1030000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 76802313 1250 76801063 76801079
    0x30f050409090606032102030414010e030a0606090b030a03020c040209040b09090106080d0306080c01120f020d06080d0e0303041a09090a05040b01140604030b0411030102040605120a0203010b120907 87
    0x40c01c03040d8010f0b4008114a421414444009101101000362400c520490030070503e401105a600311280980f05035045070f014001a50301c4410707005010341c10302404420504201e6254004070503940d4020082104042003024180c0e51080b0303200c05405a4400b07404140e441c80c2c150000d0900034009800403441e0384140011404418098500e500703035075100c0a0503c1620300800c0308482c3d0060520781407041902c0e2030a01515031003d1a01d150400641c0c4002010180c0c80750801c012030806600c04658510260032024020415030103614118010401c4403e0718510409181940841c02006145410310b42240080e00200b03601d5428020202071140b40d003540e0b16000c0309841071010100c041918940762404507400d010580085c001851910b035003003800d07201c2e6410348054039130111070030b480303620789003005000303a0031b42100c1c00d5140d030000034042581540301002d030046501c0c2e007448800a03121646200180d0000740907044d00c0010030711000b11800b522070003840d042000402901c03006a00c8080d8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 76803563 1250 76802313 76802321
    0x140f07170705060c3004030201080603011b020109020307080303071e0219060504021309030e0111070f060f02070806010803090409080c2a09041a041407030309140405040f030f050409 80
    0x405180c1c0d08802141d89059004201c0d00c40203a0080074100701c1d40f05117001c0b0403141c0c002c6010190400010a0002c1c1003034500354070440460400c034480e812000c410b90302c020302900c1010f07000c074080d00400000240302100042628007a0259807500309041a00002003010801c3c039480c02004c500c1070382c0c0717140503a0078070700b0480300c1c0d0038010307a40414146842d00600c0382101505134003802c40b41ca009205000301364444001c1307401420900e000014150400a06858100c06412036044218000000100c2d0781c0c010313480388650007054081c0c90300d0720303a24402561a00024812000a40c00c100700c000c5032807800358000301e09544104462814a6036940b101403808140004070000e04202504040700b0800c103152218100300d040700c0501c0c1c20f00c0d140d914100c2c0c14207142c2140d0081d00c1403901040400c05c00410304001550341c0e00c202c1307642d5a52030900410090031841060404806185a4046400c060044910560300305800000c00d650302d603421601d042c4143c020800300310087c00045020085401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 76804813 1250 76803563 76803577
    0x40c03120215040c0905090d09150306031a09010c230313050d0c020a0801090510110f03090a0b0610051c02090303182b080a030204090f0504140f0717070506 69
    0x248044c13801d003000c0d070700e00861710060058419030380220555203c01c5e034445110801d440fa6515144040c0f25000c2058015003090b030401012041ca4954100580c00003680003403103682014024405330106a03c141d40d240005641c0d203e1000c04a240b01c4000d40e049030066810072007412580540804e95140d40f81850714010b1240002140d144130307041545860000f4202601410008000c1c0f01c5440e501d1f1a07980900c0340104013007a480e00d02c460800301d402030940e412258640c6855503645004040c150300c80d444200129442150f107070115090303042c250380e000d00b581d80319101c0768640f14100c0884030a40e81c3c1140009802c03502041070b1402c1f038400740007038010025000c030082854803408040042c1c0440d68148288030150300c4440740030410001c207003480065040480b41e65120000b580840280c443c42d004848402d003041d00d0002e01c11035076403105100e00d000d4140c0c9280e030062101059114a0000350a071180d6016038400e00c481f0743c0c01030030305880200f40b904649007507940d60701250386a08444 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 76806063 1250 76804813 76804823
    0x12050c060d05060108400f03020d030e0102131202030705120309120111090d050307020d11040506040c050f0a0201090506040302030403051006030f030815040504140d08040c0312021504 81
    0x42c06100d02960880da41079004002c04840e0075040802c1c24042c00c0e0003070b4181800301880740c0c02d0540005030241803c414200c03600700f450703004074202c01d0070b000e950b0b0702e6203242c424002890714484040512061003505c096481c040b0084800e40e1500304071421280c1901e070245d0703150280e41c0c40001c4681d1150021441d022010025540314440b1000700045c0240c0300d24401a1a410004420050001c450494100003412140425403071503c1c04d16501e18041c900001707400010b149508402c0c000c040404055081007120103200ca0754543e800d00081e034030000c100c003001c04c80601850a0300f010041c0a03042c0010503200004060441c0c0d152240f61441c1944d040d805a0400503040c4207000c8140705c09011400301c080140f005e1495503840c03035000320321844041e00304008440407560b80408500400d003424070051083c07080341081d040106480c80c0000d03400380284a140d240a60300c0740960f84c2c051007a900051880304a51440d1034000082c001c06407103a085000e0140c104507a05511012039020b0b038020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 76807313 1250 76806063 76806071
    0x2131d010501081b030c090f090a06020a0804022d1c080f0702180f0408031510030f05010603150b0702030102041805060a0b0906071202120a050c16080712050c060d 72
    0x11a504c030700440c0c24040d90782d00980101e5000d40d201e4540e0034a05400a0544228041ca03940c0c601c100343c14180040780040a070741c00010b4803801c1070746c0102024042d9008440ca51891400003012a003030102c2032094000c8800c1003000501549042100c020062a00c2e90f0010071508183d5581c10441c1d0140d40d8183c2106408559a801d5042c42001030210750140c2590300141d003002c542044007c100148005c0801d040080041c130000d401c01411030f207044014110400e510382000c005000360198441c0221414941000011284c2c0301e400340741c1a000612035110710090034400250341d04e500511003603030150740812000411401754020715441d010003910004880c04c1c8081040560107450b404180b40500038054040c540e540e0008980c025070f4814038202c844a4640016800c00010703ea0001c4902000709042408a030060001c280d100105016901c00243c01840c130f0044d00708070f02410782d407035121410078841f200c010004030050340d0169080b0f4002820203c0050380607030000495611103621 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 76808563 1250 76807313 76807333
    0xd0302040306051b0d020d02040f1502010e010501050d0f0f022d09040b13230109060b0303030106050405060f04090203011203030506030a050303060f0d02061306080108030702131d01050108 83
    0x1a038403e607034100032036812410f081c40300e00c1030f40c041a0180b1622220515400a8000140415a81228014484d101d00c4250141d55552103006540c6c00389510005075081003060406000103100e5241030b030b50700803c2c52503420b94a0321441401180b0540444641c5161f06050000d030342d504141300e8001c800d1301c3d44900c0074040000030740113880c0b4940303c1c00d00900c03e98003408000740d121031455130b01000c50400b2041100f0306081c20307507001c140480d0061765603654200d011440780b07064000c2c0703921034042e0005010611a0000b4555a880248107160009206000910051800d4001050052501c450032410681c490203614200d91084c0d0045c0e04c99001e8101103400c054042c052542d214000314090001c3c00c00d280c852a840c1e1000074000c034820342c0849135410721550340030214540b03150061321b0345455094815220400c28180d01940c00464207000000400c283c0000032103c0c4142c3c06401d206040c601c070940c41c405080071856520404040548903c0402401d1154074020b0070460020302061803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 76809813 1250 76808563 76808573
    0x20a0201091208130e1e1e0a0b0a08010506031605150c0f070b0a0806060a09030204020307020f060a05060906061e2b090c050109080a02240a031a0a150f0201020c0d03020403 76
    0x100d12015a4442c46d5400100021a600d114001496484640c0401c5682d40ea41900c6d0380108860b050795036102504c0c030303004690a0815032101d81314200c1903048236615003140b1b02e0320b0391140051085030743c0000003107501c1040b00d200c100609480c1039040d08130b07a8104003003c1c00b20308107203850308000140c8002050700d600ca258425400307600110203560045c90b141d00314800038541c104600010340a103400002040d42c5a10801016036172406190a880c0319003000443c14024090590380319200700c03404808100c03d4a0a8012560b400c456a001251454441003640c03101d50004580b141d0b5500d0900441c200030503400360703100191081c8040000e81c0c000346180c003030072014068014070f04100001d1402c1c04107520014900f100141c049501c0301008490018545039100380024071072403c240803078034015907a0141c001000c1c00d100c0c3d09600d0130b840d902070140600c20803544500c0407010100c51002d1101e9000d07000e0001181ca4030300c0058a02100240c10916114003018008006a40001c0800900c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 76811063 1250 76809813 76809841
    0xb0c0909070302040602190305040f0b04091d0303190b06070525080a020d3002010605030303070903030813020a140909010b060306130b0310060303030507020a0201091208130e 77
    0x7600a050450515042c442c00030b69030740406a01100c20215200e10340c083c1802942910300030404610501e200903100c0f941700200303411601c203044050b400d080801c02c0151126940901910b1000025415950b5550212800c1c0c4100c3c100288026030300d02d0b240200b82c642d0704c02041c16074040c400030040d0020400d4624903204002d507010350f280c00c2d2030500344075034103010400c00000da40481d00c109142c403041c1801410b000d080a010700000740d1b6820410700c00e5101d0b040c0507004445c5a0000c004017640c2d00d051545900c01120303404001381070b95805200107401030f100c4c135400003901c007801d5005d82c0455000c204142c2d403580005420140340c0d05540c00e0b83c60401005640070310800000d02401c1440008100c141c000500042d200303800c20101d86566030082d5101100341c8800408481041f00140760500c001d2200f40010f40000c1d0903e03000881c00e9000040c0303d01d480d030713041c0c1d5080522450428030280300c100d500030440300000100040c1d81890300701400b0b240034007440408502c0b01d04040c00b1040d490 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 76812313 1250 76811063 76811071
    0x1021207020f07030201140a02011506030605090106080c120406200d0c0504030f03081b070b04200f0f01030f020705010c020d020607020601060c030908011505040e07080c060c07030b0c0909 83
    0x683d01046007400185d80c0881c810200f80100c84a0340c0d2604621481a4007604980482c1c0c0c2141d1141c440029049915070440c104448041e21240d281da6200c0b40200c0d0b8500741164481e600040401c60310100300c64118a41d6441402000001500b43c210454800101d40c00f42d43c0d200050400300300001c0c1400e183c0702d8081c01d0b4080f402e080d03180528645d19100c4898000340c01171b00740441d003000a204883c513002c60b030b0a00c01800c81038580c0c40d03980e8030780a0340e030080a0720b05550000c0301c0016040038845400c200303030240900520714000c007251502048024410703001a141015140c200f00400e80f00070340043d118040c0329400200705c0b0000030314000e250034480c0301c1c102c086610036005e0040064001c0f8849064850900d8404e040900605040e80c00076030340e600245840d031800030f090b5204805144848251142120300340805491160364a54034401c0703000b0b050031034101c501c800d54036140006c01003020300b00020a8032011662501e0386400020202c83c41080c41200007400729092402c00301950384 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 76813563 1250 76812313 76812343
    0xc08040504022809080c0402030414070b0a09060f0e10021204030f02030606040b0105030f1b0705030a02070503030a021005060f09010608011503060e041509140a0501060b0c1f0207050102120702 85
    0x104e46032484041c0d45086480480e4015640080810240517181c0840c0035101a0070041b10002079403503400115942c000701c0f440c000542440c03000b0544900c1850188200f41d4103542e480d1007400322030104049809092541400c2d48950707445c460010405401820003540954540c000e40110743c014103080c900010100b41c4141d2401c0e0060345036030703040b40950340c00c940003065102c110354812112190380d441d034000240c0f900c100803410504100c0c0000040010700382c654281e42d01c0c25520010f06599004241c142c40240e0480100102100d41c194480e42c0d119200820401a144001d804224050b20a8019034005003c0301c00600c4680c074960501d01e4070601d1403800704025440d02e03580c0c2941c001c0c05400200007000008012a80c01c4a0b908030240301c50f0408118040304105c110003079641e11003003508880c194204200001e42017500c07000e0712031082e24070001d4200b84120030312180702d0b0101d01c0d448c3c07884654240050804500c0900c05000030b03d401c6200d80c2074904040c00040d140c01000316034055 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 76814813 1250 76813563 76813577
    0xc0215010b1e250f020301090c0603230a0b01030207021005030106090f05060403060504020612070206100e0907090c11010509010f0b030309010906080a0e060f010501230a0c080405040228 82
    0x704160030120302c51400c0e90582040c1a40c5210f525000d45010030410001e5410343c02e2000c50340510140b04418002c494841c4c500304010084024180040385020641001c2c0b81c0c0c2030800a07000148982000c0e002e83c0c014580146420300980c001b4a90384c032110740c81070009001000621180ea0040008000340c06091050306030a80b6290000e00c051003240401005c0c1500d58001c1030840d121707903081e170f908000c2440c441a6103280010b0000d50740e61044581c1c14803100c1c0c010000429403032000c40c003400b03100403202030b01c046424400d0600c042c09000c0c0007503042080c0c04c00a00a01c050070301c5441d019109400000c1940b0400c0d000220640c1d9001c0d002c54441e0300f04024429881c1c0c0c01c0300c034140488005090140450f40c400e0340940040000040c1c55405005600402100c02a10042103059072826261784e0114070320190f0300d00191900038099003601d8020040c00308040c0c0a07039005240144200c0ca0145015192004103082c1e0b08160460b42074a4100344200f02b00c02c41c84040403c20203054505a4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 76816063 1250 76814813 76814827
    0x50702030403050319050f0d0e06060d080403060c0504050a090e06070504060c0609110d0b090d0503060a14030a081b010c031806150504020307020a030e0d0804090c0215010b1e 77
    0x5481e48a45000760707031740390f51410b410700d07650740180180d43c2d1041820745442d0302c910210391450080c1a0101c81401503001e0702c0000f45191402c0350f826012241c121680034100350855841038014040740b04c5c0001442401e000000d85a075440038200080c0050746001700d615021401100d01e0600302600c041c09201c0144010312595a0101c5420a21a0001d40114414990b821300390500031030b048070281c104109146e000107210121552078000c90344102141e19002069501704c0f07643c0029207029500c40210b0308104010f540d1052070800303184c40201510a1584103580e05602540118000c0401c49008001215010002c0c414800c1c1c81070903003801d0087c0c00403d000115480c90024000701016526100d800d100003140051202604000d8400c640c1c9050200b00655202d5588031b04030000744c01406013003030904180020b4000e442d404510113050508200c3c0c4c25024210040100c1c045206240003030f07a40e080940c015030b0080481d480f82c95907602d0310b1200c02c0d003074840c00ca0240da00700b0400c01642e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 76817313 1250 76816063 76816073
    0x50105010e011d151603121a1302090301050103060c1b230109020301020c0c0913080306100c050d0503060112050108071205070806010f05090603010c0c06050a09080408010f050702030403 82
    0x580300f0342c0d0303040500b0110034114800a9000720513124001d5019502084600d0225296900401403078000e481c2d00c1009407045054a043d280384511454101c682880290441e040c15400e0812015030b20101505080c00318000c42d02f103610990040e074030309460b0f000740c110854025071000d80500040c0c1d081032f1a440d0544071900c418500d4a10303c15107140320b2500c100c8100f029801601d1243d40140203568603188145e150f0f0707544000360050344c441c0076420041181d81c5040d1800c4100c0d43d074810802802c45d610081080310b0340323a0710b251030014804543c3d405000140d0510116034001615250a520780c14410300061850f488601401001c500d0000140031212000400c00101d505147c84d40c0095061450440d0614900390f0103c81d880c421200003090840e4034128403800d0364016501c0382036503a500c1042501b81c0c1c00f50b1714002c0c049000540c48201050254001540c004551000403505103603603510740300305038007540c81962244d5464079103032221402401226084084e600c02142001c0c00c0d6112 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 76818563 1250 76817313 76817327
    0x3010509070e090309031203010602010c051603080403050d050a0903030b030a2301110a050d0c030b0f0d02040e03070302010f0e07030218071803060914160b13150f03050105010e01 79
    0xd1042c5a00c0854006224804200210f07003d644000d426561060780341e04e9a500d040d0820b004d09400365080c480400e00381c5210300e050722441c84241c651300b2020345160300d0940302240701030f00950400c41c2c10000e04400490301c1c060b0700d0050f05845400074400089040040465180c5c00446120b030b0030180c150030105e03a045c0c804101c0d820005444030807000d41030448030f0041400418000f444807011840780300d00d5412002500007400080e10034800f034450b8507030450803030b4018000d55510400980c0c00386101d0410520b403451440c030240c00001c03e000e4907000385140d60808102100140c3d100c0f94500ba01c80c01078081c2e841e02401410050010034115030008940c12414802c1603441c0258200048225108000d41c0080401c41518484200d45130704110020300405101552907003c0350b0083e60800c180001c108000880c0e031803201581d50305003108031056600035002200601096100071071075400e035111304210010385841d074581c42072030b82102400b56038050340301c030341404201d031043c20181c0d0300030794 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 76819813 1250 76818563 76818569
    0x210141e060d031d0901120311070e0f190203011e1401020606060307030603120c020316060e01030b03070810020316030504030509060c0f060c0a0201060f1206020310240e0301050907 80
    0x1030081e428855030514051403a0514130281d8010407040001500c505840c1075000746074040c2e560f441c0300d05d15403c0d5156840704c240c41055050120900002c180c0340441c0040c40d0440640c9520051007241042000180d03082a009155170580e502c03010082e01d8100f04203500106240c000f0405035694101c0080e442e100c0003000c4e54011000040080c000301e100383d000304003445e0b10001e954105d40c80c005004020340c01400003280244910460001c00000d0b440710302c4111200c981d40d01e80200180300044010700b5120b202e1039010f210300d241c0890350034000e1090841c006020000140c0b03d00d00901c10703c6160201d01403120a240c90b201c14000802d90100c11502143c80c151403090b9644507101c0d101e0b1030001c054041a1460080c03505100c255400304000340300b044c079241d0003480003c0e00c9140321701c0d0b900c540f40314102ca45051150101c1c005800c036005141e00202425103011110b41c7c8080d00c545190b20006019000f900820b5080c00543e006007106001c1c0b14154004c01561400e00101662094980 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 76821063 1250 76819813 76819817
    0x9050607061805060a0902012604030f05130b0304020a050a080d180b0d0b040501210609050309090a0621020d020f030304170c1f02030a08070210141e060d03 69
    0x280c101c2c1c0080709501803060203a841000c440ca640f030081e07403410050101c0365049000800d40200e120300e003010808030300a120142c1d049060183c0343d035601540c5c881000030780d0340107000c001d0004100c5041c0146000006040d034000e415941e1419104001c411242a0080b034464030f42020240b00c64400082da81511840d00d081461301c2c209514481d100302d55039a409812042400200762010042e03542000c41d418206840500c01641c0352404036a0742c589942c2801c1541c440f4100c0440800c05942003242524005c0041e285031850b040b002c181e00c0c900480d09001425100c041c00c01042001e60030024070040e00b80728042c11f901d0707103600040b00e09030324040283c400c0748410013600c0c2d1541c040c01124010700c0400700461100d0560540180c84c2c055050000f88200c120b40d06540f003030540c83c08680d252a05990140d49040c54000f019240c149018000c0000c40c803950410107007108052007460910010b079456500070341b41006840202004040c81d0041c8045c1800500402e0b407581c6941030800d039418 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 76822313 1250 76821063 76821071
    0x10c08060901051014130e04080a12020c0309011202042105060127020703030e0102040f031407030206030402010c050a0c0e040b0601110c010309030302070209130512161202030c07060315060905060706 88
    0x7110b159006c00200e60856005421502d09002c10803206100501d03500d070042c2c4a03034000a5900d442d8204900500004160741e420800c180d03d0a5841a001c210740001c03402001801c1945070302e03641c2c4d54801c00001030041855496944000d200e401c200b1140184081d4104640392150110000100781e80d0059050509401040540405010303420030555200004004c5403259980c12111f980f50300c01d40300507900c0102d41c0500103503920002c0b0b0614142c03900a03001600e103460719401101c0020f0744001c1981d00d80140c0005000090741d40c444000240f121503107154450809080c446040040074000d64140a280a0840c08040c2c005c00c070310015001c01d090024451401f400c0a90184c4604003009500c882c3c07030800c22807050124006841c0403406841251039012064525540700d100760510100004211010303240010344198611400003e80d105036401e140360300201914000301d582220010949400c400e031180702ea00603030400208040d180c02c420389450040440c14500c11218003400440d15 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 76823563 1250 76822313 76822327
    0x8070302030717041a03040f03050f16030804020a1d0406020a02010e03030a02180904080301050405060a030f030e0f0a0303050706020307050403020a03030503010602120301050315090c03010c08060901051014 91
    0x81c000e54440e6500450784048280d0380e42c800c00b0040e4024060b011152140c2d0180b085051144000d072171180b58010030444105000c6c0c1c400b9100d60300020300c05406a1000c200d10101c0621221a000005120303450b0040a41407a1040061091541d044032034613074a0b4020200a070045101c1050b00315401004c0107940d8002103170124003600a0324040d080c1440000140300d41042240c0c000c10071001d2243c0d003403603912a01300c10480146000c3c0c13000350002d0f805000520013442c0690090f070700b1010080c44c48000b075550b80d58030090079818503401d40c04074503085011042030070581c0c1d00c003002c4001242d014444504580e4050454043c000c0081d003a25404400294614083d134100c8001e940c0041c440203020340d403458020101d51003405800014007808031000290010314040c0c81c140c0d0700080152814030b0780100c0c0b0b41700408008244420501c03415903c6c14180c1c80030302c00c0c2e05202c14141e8800d065464205c05120a048041e4032823801144500400ea0741c0c02d030310800004100050750300e0207a072112 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 76824813 1250 76823563 76823567
    0xf06230412050c0109030207050405070519050f040e011d0601050322020a030506100609050406031203020a23070b160206040b1b04060806040e010b0a05040b0105041706011701021303080703 83
    0x307200514100c3d076107019562000c1c9500061013004440781154240403d943c2c0040c1200ca1b40034414090003002c8601c864103240e0f0b40030b000a00081900e4111950030155100e901c401a8902a405024450203003100090700114110805500131820300340140740d802d010100c2217130b000c10742c501d4011060169400c03a04642d41c0c9050f0000458009049404a08110781440b80d814001d01c50301c00403c0c03964100007124141802018100c03a000300b00303002c1840c80c011003540a544a880540100300b001d40649a20704841751000410301c1b40d5404040c1c5075045450140705892028001e440761104d904d604d41314240d400505070794455480400b40445480e26107044cc6180304510700c2600303d803008100814404c1c0d01000d228032804040710103100e84e0b2001d251840c200d85080c500b160708810800c0701030140d4102500034203d0614103240407450540d80c1c03659085122003c40c6c006a81d600110010030020340c1069038450f99100d50402103240082d8880240c000b40d51500c0014001c00300400c24005042c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 76826063 1250 76824813 76824817
    0x121505240a0e0406090504030807080108060603030301030f2a050a060518061b15041e0b070318020409050c042405150f0a030e060a020c03090d050703020d0f0623041205 74
    0x4080301d85c0500581c1003500c1d000c1c001c41b0040703403500300041c3c200c2d00002e459000000d01502981c0c000d00510302d940d01b1515080c3d40008050b10964403980d01b1441145442400400c440340056240c0c802d00c40d150074042004a8000d50340c2c082e004102c8180400d03006002c048145c440c605500b200c00701e90f2607040d200b054400c200c1503088480107018020502104190f9040c48c03900c02c511070f0030f00724001e0101c1d400c2644001080080a40820b100600150003503000307038841d1201c001890949010f102c140e034006026114802003ca5803030300191030171045401c26001c1d4444103446495544000703030410150044000c006c0c41202d210300d148402d00d015064521088070140740038028202da84001040016000d0b1a840c400035130b080c07080d0400242505224800c0c4c0303010f8030100000c2c510301801041000907401412409403441d01803c0000001030b1b80c3d46a01c602d405106408941180c042810040211851b110080010400c07a0000030890796909415541c4194446001c082442048008845074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 76827313 1250 76826063 76826069
    0x1060503070b1804020301080d0c030e030f03070b060405040302030d050a02070605090a0c0801180605060604080a03090f05030c150a09030605010f0503100624121505240a0e0406 78
    0x6004092001c5403a074240b00040c80040c140b10300042c5241e40b8502408100e02c8240b05921080d00480d00c0b691280b03104012070f0036614080e2030a500d025603100b0010382031881203411400503501c0020404e040000900c11a90302040c201e90411003450b1588021b500c03481480000c03211140e45800040c22010f403031341030340c0d045904a80c3c02c111615140d1a06c550b100550070341512030300d51088002801030b105008a041c0d0703490007000f481810031143c3d42c00b0003401020703000c20303440b480500000c00c0301c420800615000c18066561680071600c1c0c481d0842ca0215550410b9000e50050b07010f403403041c3c80d800f02c29818a2a9814016510100c003003044501c0701e51030304010285400d100000880c07503184100b030b40a5407800c50070703988480700b45410842180c0c50751240d10390a0380424650070307644d90540349500b6941d2807070400c0082110103d50500881d420001d03507040380b40380c0000030302103410901d4041000860f0404540300c0c18503905040091400345803076071420040740caa03001a00b500c40303400072802 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 76828563 1250 76827313 76827319
    0x170a02010f1b0c05090a051b070302070305030c03070209010812031501030b1306210c12080f0a031a062701020708070e010501180f180905061906080d09050d020102010605 75
    0x84004500c1c0c00d0b07000c00c0c114401ca5101d002c10170081816860180b03e410f0207404d003030b940c13040360b0140381c0051a01170f00111019810360080314070020100d00d00340010a00710180700c029583c0c40003184104501c200c1c041e04400519445550f0003029012038038112904502508125410710040c80012005071000a0300306070445124048034600d07070b0040e00518142c0c0c0c0b4101104000e03168140c141c401180800c44040c103c803501c858104103920701080d9501c1400e0142140034034100900c45d003a405540520356000000755211044140c115480040c24080701d8126419454107001c0c40310124100302c1c1c9185600511140300c44012540e00800146008007400c1099500c82551020f445214071400d1240da0301050302c3d43c600d55201021002c08106032080250303409401420f0000c4182c09080d131010107005950b4682c6c0d51000f00b2000c01c0328034866203100222022000215400b00d00b80c401300d034004e00e010f50141c100a020941c206001000b80c843c1070301c140100311482d00040707024120725800160 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 76829813 1250 76828563 76828607
    0x60518041a030a0c080601140307030f0c0e04050a0201090b09180c040906030b0a180201050a14040306090807030210020a021e01020d02030108070906060503150d060e10090309170a02010f 82
    0x204104130b11300040f0440c0e20f50025100241e90b01d06505504200882c215170b803503008100180b0001d40900f1084104034000e640740002103480382010a0004c00903241900e15070b00c01c9806104640c0e02c086c00300c010b0007420803c0c0d81030a02ca1400701d08680150802080c1e2a140300000980d1001d440007903400401c941c2d50140035031984d90820002030a415540181000e05140c00300030310841070201d0210440e41039650034600818401e00b16600e184150505040c58010407002020070b07000c3c01118040c0d030056900903a51900d82ca4007900d00391040b08940c400702e00500c50390582179004500300d44100351044242050791042105180240724043d01000910310110000c00c02080000b5410192005002c04020641c1c131002c0566080c0404c5800d090f80c442c00e0289004241070980003200401c2c8500c1021840841040300607003003030403000305030111a60b00c87c021030916500042c404002c040310003460200c918200c0a10b9140e05602c1c2000c1c0c1445000003c0c07074041845101a041c10300210b0030044 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 76831063 1250 76829813 76829833
    0x1918030b071116060305060603040b010308031b040e010e060a0b0301090e030d0905060115050408210702100e130e0706140c070303090302090a050601020c0f040f051503010501060518041a03 83
    0x11490703c5a02590000031300c0c2c0b900013001ca040c2001103174080d541201001070980c3ca0356a8121082e8002001c007221048008440c0c00c034004500007500c041d2180c1d440d1048590b040c0000f60301594030040c22188501c1c1a50402c0140000c840116419a40e801c0c1010440c00000c1c11140c3c40e610079120480261441c01400c4002d110010481c079050f11381d40380c001e088280f40000304403054050303070040301d02c1c80e0018440c0380003110b030780d10f40b075a600c1d45000003e0b400c0100680009001540080c886808500008581e90f8680382c10b4040c00c8400c0d48000d001c10000100c40c40341c1d9a88c13809801443c061045140004554050100c26603d000f8071180403180416128500105030800ea880704a00409041020a1802c03d8502a03640320f5481a4020b003040141842000500903541038a150440da5903000d404d044034903400f41d03a10910710701202c6c42c101c0200700149821580141d0003c0101300d420b000c80e14a10000d5900e2102d0030000b1140404c00e031034100360340c46204012046690303040c869a0860 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 76832313 1250 76831063 76831093
    0x308030f04121403070e01090e07020f01060501230a030b09090703060507091518080f01061401050c0613050c060a0804050106050a050d0f050705151918030b0711 71
    0x881c46584103600008039151501d0066461040240707100440100030300028007050301c03822010641c580b05150240000740d541910000c80c0310266108401604040c00240c07501d0024000c140092200b8a0f0010040c041a04102d400030407100c000700051074000303026841248243c0203808512402402c4880038140100c1c5256190f81ca48021150a030070440050005805011110120341e02d5003006080340c03401f08000c03610113404031078001c2003038030b00e1201068828013000010401c0c401e4034000210b15040084014146400743d0311241000400c218030070290381c0c00b041090704107a181d072504001e04114600f03203003040344125546400080116a00050380c0d40710305007074051401b030300013000070540f64814014003010f24041c00340c03c9240807101c98005401d400d00403103180d0245082d07803107050315200000c0701610008110740e41340401040015441d0a104042032403141182041080c0c4c0041d04030076013586600d88000360000c80824001000280902e03040c10741c07014207805444504e0311446903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 76833563 1250 76832313 76832341
    0x31803040b0706050604150b07030c05010c170a110a080717070c150e0303150604050d0305040503070f05010f120f050f1902030603060c070302240a0509011a04020c0106030803 77
    0x190f806500b0703c4007182460400d481052018491200425046030404008a180f0352203074a04600300050143d100c0c0104000703100fa00441c06031a07540c1b0487c40c075000c902c02080180507000e42c50f11807401158044038480b680031500004064107240c091595040d00075503c00c000741401c1e010002aa40407c10029842005c000e01e682c46040e5410310000c1c81d81407003080740d810090701040340d0700410119921902d0700e904140101c500034030091415403035001040c01103c54441c110041840030a0a1200e0701d020b10036080500403040106415030325050000f007050200c54008c1c8144035041c0075250103803140e908104218003018a05100c14100403640282c2100111200084211105540515140180201c1c2e0056100500600b0542c441041d041c10720341c00b50304103c2c1944110a4240c0e810843d075405081010803404a001040c0b80c24045642901c03070041481030983d251044099044201a0060205a605540068840401018107401020a40c03c09044040088204103150894580b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 76834813 1250 76833563 76833577
    0x308030a061d0a111308012304030f0c0201031112040312060e180328020105060d0201050703030f1d031902030702010503041b03061a0a06080702070605031803040b 72
    0x20100300079079403208003400c03075907541c0560040c412002d00480c00520031a044810b2401e8100092480c2004890544444c1206079000a0700c59440d0b43caa40e800303420400c0307011041c1c1140d216605031031625580080c82010301c03410081c240280702034040103691090f03004d5480f00014461550303880404c2d6480c800c08210888045002841c0c55104100d020010302801084500f40d00d034128440c0c56008200c0040c440031a050f0156100c184551103d158000441c502824104a6210420304603454003d081d504014800c90150301802110300040c1d07030002c111a409505490700149200010306480c015100042e400c0d01c2d1841210981a04944040300a010000302d10000c4840183c6040c0282e07100e011f0010040c2c08130700c05000080c0441c0c501c500b103210045030303010f600c9040c2d0784a503591403c40f485594140c0c2503411a180004103401c0401d01c0c08040c00640c06c12001c18648000000e5480c41140070380020060301001041038484441d0141b0031000f030f034100792601d03143c840e0f115124a030042e0f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 76836063 1250 76834813 76834831
    0x5061305090313091509020a09050d0206070503131701021c0b0a03120e0414010e010605130306060303050c210d09051608010903020d08060d08090315040b06010e091519090204030803 80
    0x5000070346d03007064070071901c03414415150f178200c841c44c020800c0381c45410308005a80010b000c205450000e2410b0000b0b00d002c25006170346140705400c0c400c140071800a03550100285030310401808242c0b1186506851400c5103420010804e140c0d5400410f000100039400140000c6111030b480b04d807290000c54807030412005480c1000030f01d040005507130441c0710038030a940101e441a801400898886c1d402030418800c280754400c1c0315a6a40d68a508071420f952058000460106480004580a01c40842c4054035080640309a2900e6111100303640701d9559504c000503520311400b0100442845012003500103c213210401c0c580d00c0c01d030350b8064180c00804a0050151500790200180185c2126000c3c050191120404021513030b6100d000381c4c003c0442c0c5030f05101d40c4100381c18401006030074034455446102c0c822080e0400000140241c1c20b166003840c85035540c0c4041081814014855040714003080381c034a0800b008002d1603115103103050f049504103600010b404028440c002005500a1206c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 76837313 1250 76836063 76836101
    0x140a02030c12071d0319110d0503040f150e01080606160605010b09120d0503190f0507030914030715110c0303070201020301051903020310050c1306080103150506130509031309 77
    0x4d108064855a145101e4056082d5040c90036011800040507191150806064002070081c02e8580c00d1a54101d544444465011408288429a0200c54210305404242082602d03040d01c0e80c0003a10082d0020241405494046291680409204000640650090400c0090b135840f024810010781c01500e401d4040c0c20010150314107180b0004109540d80010781d106411034540213200f480100ca070a083c69107094403690f551010714101e22520340038420707980300090701401d285040721128680b05c0405040b80c00c14800d42d0702207500c07551909a910710180d40020200c01c20303d4100e4080c0240040c918040c4004001c0050307203071701580154161070003182c0b0000c6640c1510980d600c0c03840e40d0301009405801621000300301241a0300620341004103901d003241441ba00c0051402e90461360760000c000100550010001e203c038802c10504107600100c0d0500c924034040002c9601410599441070036999100d000410000f024010b4440006001c0c0c45444071319503642d0303c0c0f40681701c1c03940216140c03044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 76838563 1250 76837313 76837367
    0x30209150c1002090f210f060112030c1a01060908160b09011101110c01020d050c071721010f0503060702010b03071205070b04032301140a02030c1207 66
    0x20030107441e03446944600410300e16902070700e414040d4010a00098100000140a00d8145d4a030b4489000540401c1e04c481c03120301192a90728034042964103040c00c5030f00143c0040c031001c0b11181141001ca509400d10800190b0a46048403a01110541095502c40c0403400440c8440d400304200f4112001d00044500c0203503c880001c00011042c85080924041089105040c2d40103040040020200800004400c0e084a8040030141c0c842d854405103a540000e0801038155280b2886d80c011143d4170007503043c04c6807980c40c00e00300c01202c014012001c002041c0d141c0348240040d0401441c17400031056910700d5a540e80d90058421242c02480c1c8a0f02400340026180f51052107158000403002b00100803051a0200100d54022208001c1c1d980d40215500403551441c1d4000420040d845494280d900520f4580e43d001303140e8101e50422821390609503010701380c00e40520302030b40004c95100c3c0140c1d070362180d000400b59072142082d118a1a40040100b00d5040d40020041103100000700402c026072103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 76839813 1250 76838563 76838599
    0x105100f0e01031a040509100e070305030301060309140f01021e0307080609060112090f03030c020718020a030e010f090501050606090901090504060908040e04020a0b030705160c0510030209 83
    0x900d820400150700701c03441c0d011561082c0c0000304003031003202840103a000303844007040c2924011a1856003d40c0308105140c68083c040c4a011100180e10003c4c040c61400d580e2440e0b100d2206202d48020103031184003540c24080740b8001604035000450860720b5041e041e01546000c0c1d0003e0b2aa107118202c00c0145140c150007510840384204016038803250659105c104001c1d05140c050910b9040003203205085041070201e03c00c01c8810fa001d840d030503003000d03818900241600d640c20516001c41d00100410485840e560240407031a5601da800940c442c1c001d000d04500070f1150101b000380f40d40c201615041140120790045681500600c0280a25504c58050050030b209114200350040024401000700c010b650f40500d030014402c1d000030646020940324850300303070481d4004955000c903000030710085142100e020001404022441c034250302c1c004001401e0ad01400c0c0355049071a000d41540310412003141c08400c007500004000e0711941040c0075000740207400144080c3e008203188440560f0042d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 76841063 1250 76839813 76839827
    0x2060f150102100e10060306020c0c0109030203100905160308070c050f0f1302090a030b0f1308030105010c05070801020a020c09100e04170d0f020c0d031b051b0303010806010510 78
    0x1060b001440a02d5100241800800005415951a001706101e5120302072590007a2001540103942c0507072a84052301c00c1d6820114020b01590510603103070030030001620301040075041031210010004640005050242c2000a07260300444c100720451004001c024103000034140280c0070300c001280c0103403900184403a007803054003c6640440700000954561601c044951340e4044443c1c0c0241c01c1804074808500000750b590030440d84880000d0400c10312000d882e4110707070300228829510600e00803607240c00300280b0060103120f040102848820003800000c00041006007680c4000711741c0d408400c0360007916100c103103070000d1041c1012000b248003422880040400d8a00340e03000e05d141c603100e030b40d50b01400400b16214440c1100080c4100580b0a600c0c0c81001800c8840c0d40001d640c40c544500d00c103042181030500e03842070500d003802424131841c0d038141e200d01c641040c0c1000c07a582c140c1000b0129000024800c0d041692100200110314070001080540c101d500a699100920040c1003090f1551 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 76842313 1250 76841063 76841101
    0x71d0f060102060609010b07260403020108160504050409050309090403020601080d0e0a06030c18120303230a0209010c05070f1a180108060612090d08150906040203100f0602060f 78
    0x4030072007038014400d08103810008c22031188035014415028800500c0703904042d107520801103001c44003103020400e558110706034540c0205130041c164a803031b241003405829409540106402070b941c0340c201404000c400c004031048405c0c0101b21382014a0549070081da034050900862302d0758082c4004000b0b045015043d241d081c81030050032000b203d41040c408074001c1c100007540c58200200c0c002c0f01248440c7c100902e0014155100003401100c1c0a070602034203980443c8405015000c08001003201400840b03110b40d0880200140581d886a1100c0121200503060b0406001d5000350900091040380c010200012520589244660a014000144d42e50f0045c03032501104848100306c1078400b50320030f40ca25030307104800801c2d060030820000c0851300f18440c101c43c01c600700e43c403505595000d1500200d84541c080c8000844000020064002c1000c60304060030701c6001e260003202140c1c038680c2d01003032030018229200503e4401513440134000d5544a064034204e0715030035032101056222110001201c0742d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 76843563 1250 76842313 76842319
    0xf02040b090405070905060c0a03080f0403050a03470301020c070314211201140112152c07031a0d15020d0f150521071d0f0601020606 59
    0x2007100507401e010180c00c008100004012084c5404100c540d40c55001d4041000d2200c024150320696181c0548801c50180c90103a21b14001c00410000030303840400c84404850700e10740819000c02d50748403421540080301003450345c00d1250240751070071959000c21582030042819000030401a82d42071500300c0c0306200d00301d9000d4020040a002052100c002d0b01c81c480d80000440d00e20f9040c58070407001d00c18000060100c1480002034500e40d110031150118050b00035003428018000c4118000fa00004101400d400002d4590303d00b84085034540c1f61604c010010b010529400044c031a060203d040045400d46c24031303600400114980a11030700c00c08900981c1244081c400030301c0c8000700010f4200418046414403c2d000d100c00c044400c0d4009480074428100c00440d40e61298801c04096440440840051a02c40c0100301301c65520420747c00104498501028103851301100c0da24100181a000440c803042400703e4a121035945100c01c80c448c01c001507480032581c45140049845200964600340c2c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 76844813 1250 76843563 76843567
    0x8010b07032111120a050f1803190306090c020f030d0f09080706020a020709060509040f022107081509030901050306130c090e0a091a07020c0307030506060a1a040b0a0c080d09060f02040b 82
    0x6550180c0340c41648190032200c003101c0c101000c032031010f20a5040d2020ac1000a07440307400421000d61540030340c1304040c1483c00500303121040603500680d6401011402c131401a22001d2a82849560f1f6002c4150303180c0141c416552240282071901c0654009005003005119640e030001c0c03800c6442c03050000380d0f98002e104080b5a00c407a03c964070342055080042c0d0740031000c2070030103035920000e0444100c0101900058218240341100c2c071030030074900c4c00d9170000c2000708004209035094040104d0b90401c10900f0800e840c2d807650f40101d5200b11a408900c10a030b4940b00184510541050310442169050408040c20740d8a6410f0324060381c01241c0010166407066060b070000c003a8641c40e5035030101c02c0344110341d03426600c4030010340750642039442542d8a0f00501d0034000b6506014800102415507510083e80006c510b5180d0b8041d88101c1c820880d10040115000710030714030650f0300c801416042601d983e1900b096910480c010548190110303861882c00301c0b4021014820300030b840441d044040b8640c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 76846063 1250 76844813 76844821
    0x705160509010803040303051e0c0c041b02060f0c0c100209040501090606020c01140919050306090c1c08070b070e190b0702011b0501061707050108010b07032111120a050f 75
    0x1440300d8005e001480b42750034000701c0910301d121f614801b501803000200300070320508080703c050104031124140080d0100001a403807640c2140c0008800303402c2400d0030441c805036501c0d407500141d00c1c01403124000b814060300c40450200003a40d001380c80324000480341041181d03620016031301118401e105481c0903802084403500b5641c01809546270b500d161640705483d03c2c40000c002620304140c4922500b9000700b2240c00d0009080420005030301c240c0301c0340209085490302001860408900d4440c540d0311140340920410400d0f000103030341e4155401410080c0c242041c1c00003904028076204143d0040400080380b0307a8180300901400e048404c5964400d1810100d500110340060b8100e1006c00004500140000001c0d0248100c00041c410344070581040c03040144a2814042d4551000d030402034042c0c018004504000c0413601c0442e41820174209803002004844008901c081e00322441c0303407501090031101c4132000010003100f21076072115061645c5003d080300468a05454544c9a07032100c1d0001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 76847313 1250 76846063 76846067
    0x606080402220b060a050403060b0a08120304060f14010e0f04030e010e04020c0304080d110607080105040e0a020a08030a0201060806010e04030e03072d0504020319020a090b0705160509010803040303 87
    0x81421554420700210310111043e0224015520840c008000240005801c0080c4080307071160441c2400101d0380070701c034240b616071103598803020090f441a149800001003410007450707038421000402000003d0040c0e0224800440020b20248501850754a0f8880041d103000102c0303202070702c6154192203103851382d5507a90045888100c81250346410139402c02c01ca00744501c08002400040800d400100000d4807100270007000150010700e250302e140d101600340300c113643c1c00c090f0007419a4801d640020700142d00c000c40c2458081e038501c01a42140c0c044601080d8440080020000b0034025002881442da0324881d0030f5880000341b0500120a40400118001078450a082c0c0384c01d03600242220003994951502d1590f02c41d0b040c04d0716000200b4416a0180c42140c9100e440085c20111001c42c107500d0301c0105840e182c5280540c0f181e9041d800180240c0c0301d030040c29244060810201000d8903803000d03181247d0345d40c2441511001d110b61300d10b400074030380c581003d40358180d4a502000e981020314503501 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 76848563 1250 76847313 76847359
    0x504050d110a0203060a06170a2a0302060d0506010e0a080c0f060f040e010311010309030c110a08030403050a02040612032102090d030e0414060f060309010b0303030903030702010606080402 83
    0x441403400740100950159404000c03c5001d000041e6000420918004a04e1f99080c100880601d8682084030180b021504a16412000300c030601a8031409d440090b0b442c6459100c1034000940c41880868ee10318480c106500481c820030b42a203503070040d031200c4000c01034409880d200318012a0300150a0a002c0c0c1003a1074801c0b07241c50041c0a990802d003002c0407501c5503070441d41000d582da0561f200100240b015070100782e05c80e01c5081c02c00300300d08115a10000c0c0b542404000c060003c031201c0e01c8204040d158900100001c0a90409481d1030b00d80313a2400c80d4440b0844041039200368206100440e00460300d80381c001c00a9819100c444c4402d45000710103001d002810b90410010360300380000c000b03603243e4110421449100e595034241314080c0f0010042103403c0320b0b9441c4040e4501c0000c0046c55141c00c004502102d0040310341c0d98482c0d443c014a80d000d45030700032030582c040c003001c41402000c001c00405940680e80700d800030300c812a140e1004441140b401c0314003a51124403d20038130551000c0b03140d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 76849813 1250 76848563 76848587
    0x302012715090b01150206100b160f05030309070512150105010807020307020409080a02011b090b0d0f060b07200d02010c0203011d10140103020a06110a0615030201030f0504050d 78
    0xa0102e901c904546407414201e000340d0198021050118900a0380c035818045a0341c80009000003426030b0381042440340d410300659030103c2070148007400e5241840035038913803503a51a40c081c0480b0f17524a0206006030700c1c1c44d00c0c0d100c2c0c94000c01d0300b05040710117040c020031024031740d666501c4211403581c600401125021000340c002d00550104003c1c0e030002d40c845005d094801d03030046039116660780103550024211000c02e000700c3c0c030040c0d00e0b03003905c050582e10540007801c441007186201e80300e86914402500820340c20704003421403481c00c03c00141c194070100242144c14040c0011100d003485a0140e09000803901400d00d0380075020011840066001c1d612250400e03001900020f082c10040443c03800441c5458010102c0b42c0c0440019000c9079140d016100000c10005c00c070502d5945158042480720203030b8040c21051104c0b4070081d00d007200c0100300d0994032076084403040c0051000e072800da02c120056408240c0c00039091031010250703d8414010301d03000b9030b480310081130106c00c402400c44050040403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 76851063 1250 76849813 76849853
    0x70815180109060b010e090702150a06080105011e0501020a05060a05040c0b1b0c0324150319120c02011e090902121509060916030204170a03020127 65
    0x110600c0404024850758050903c62180015101000d400152590200248030342c89000d466040219095000c00c00c01d501a0120713100d044142c45e1135025070f0150100b50001074041d864903000043c00c0150032280c01c0c0703d1001036000501c058490004a0329030310340c0c0c1c0c4040c0981c0c0c0b10001007600170b02151b01c80d41d40709019245801405484407032411072980244000c1c42110000d07112190024000e100c4800341a00480041c18076000a901e050718110039809506d106030440400103141d0b08002035502c00b41103008098074100c84a00002100400300e40e0810f503a0442c0b9518a40e4000b405040180705017070f0141c40e04070070f80c0c5400c1c8010030810100c10b51a800c00c030040303c0004d5054214000340c1005481d0906004140c5840075200401c0d190803007906118080140c1808540d44403c4c40194100705100c02200540400110640291103103511242e01420741010700d9503803240100d04d14050fa0f1080d402803060440b034504186142d0f085800c0910000c0081d102c000000310f5091400c0070f1240c1003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 76852313 1250 76851063 76851091
    0x9060221043503040201031104090c090f080d050304020f0a0f0915060504030809030703121d04180228060309140106060e010c03140c03130608100501030e0c030607030e0f070815 78
    0x241d6595082070b08958082b8030402c2d1103a040e401c9441e0042c071548041c2044440a0341d1691600441c5030f07480c107000e20380e90203102000010070103640301d0241601d070041002d0702c00d408045e500d03507070303445441c0c81d0f440749466091615000b5104440500c07006422646d03503648180c1800d0464441800c1607100d035144c00d90500c105203001000515a41c401e40460322503031108101c48030022107409110b070f41403040c0303072182c0c1c58841340080c001d002c05001a080c030380583d15180740303840500540c00c1e036164240804030301140541d00000c2e0300c0d602d0740050744682d1040c0810200081e6047d01c40b805e80e01b05029031000f21307411040c40b800b80c0d4421043d81940c540246401c0c0c030b00945440f2220010380c031550004600d03410004688915041d0640c128000f080329140a00243c03801140043c030441c0b450190300d04040c1c40b1011904005c20801c03070b64200c448000c040d40c80d142002d1034090000d004a2401d100d0a0140041d515501c140105102044450769406450a00c0d80116041c140c841c00612402c075101c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 76853563 1250 76852313 76852331
    0x21201020d0f0204090b060909070e120f0109060c0305070f030c020102091903020a050315010e041406100302030f07030305041401050f0408030301050108130f0201030906022104350304020103 84
    0x301d0140ca06070012036074006a544d8148120b100640d04007001642c02441d040140000c13984030088010b90007043c502c0c21100107565200021038294150702801c019104107041819994019446100064850841004500682c20054055400440303151012800700e00300c082806000c0d401c00f800c40340d4503100043c504600500029402c07840a01c0801c04c180031007000340210709010095801421040b00100146a40c0c0541c0b001c4000341401680704c949400d101040c01c002901c900708040c600c00c207054480c1450100d140c50554603031840242c0c860b00c00d840131a4030103035010400409483e00f40c1d941034901400e000c0c0c0e42202c1c00c1c140c103e4a04100e400c000e041d207455180409040038110200141da502e52501000518044003c0e00200c1e00d800e04e48288400601000c2d2000e000b41d80c2801c0101d0090000d04102c8024000d20400180e80404080055021000507540c030344518400c40b5440d092041245900211080814600c443e12035070008030f070001013180000d107030300c60300c145400b00715800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 76854813 1250 76853563 76853587
    0xb040302030d1a040c0206010806130501111c06060504050337080a09090209060a030507020a0c0b12010b0909180c04060b12092121250c0203060402120102 68
    0x45411510380a40c40f5900003540c0c0fa080c0111402d001c1c00c0d1000b0281941000301090300c2e80c80c0034100e0301075140d20343c85075070800400390404042c803482403800b01c1e20788100b4a00180c5800289a8840c051803601002254450240041d0b070161040a07000f00508039180c00c0600358a03503103120205400701203a00075111501d100582810300c512512516440d1048030030b01a012000317580040b02e5141c0188620040c0c3c1e141d220a480300141c06160120701e9494462040e8100080f400d00507045c81c5803a071000c5010b00079034000b0b020324403481c403054001e80e0382c40d600c945090042000a55020104801140300315460540100b8907440c1c3c42c050718880204040000c00300c4a5640c468800800c0104d03000200783c80800191f54040c010750081c045960522840003c1c0a5009860340c1407c0070204009011241500341042c4c0c1c40700c4190400100e081025440a041c0445c00e0810600c0b222643d480007542d00ca0080d00702046d030301030018000d030780703980d420021101e4059150000c150741c00e000403903c1d01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 76856063 1250 76854813 76854821
    0x120c05010f02041205060a09080720030d0201020c071a0906030c0d0507030b150309101e0f0504050105010501050705060402130216030f120606020c04050603070506030403020c2b0b040302030d 84
    0x3240d444e150103400301843c9007107030070720100078200f8588514115810010400c0001100c070401ea000b00035988032f0400302c464010b801081545560148204400014480c2d01540101080032050088402080c0e8894844240c1c4081008481038201e0074001d03490181002c0c0007039a004401d80c01010b042c004420b8a01c021258110354400000362184510002410f210480d000040110300e04c1c0792442c038201c104160740d2100310b4441e40c0417079074580600310b400d0310480441d048a0b0f400c180500100d149100030a02030070054809484551a1070000140c2d50300175811141010b0740040a4959641c0350303001c00542036050a80300e4074160b02004114992401c00352890090351003500c5200041c0c1203150000c0c501018030004100c000d203051030902c0301c6500002c44c0c0130441011540444d890343d844000c2400d1001c0c0740c0c4010742104010040c40704040e0003203844001c0390740036100c145100030404040115420b41102c0da1042181541841e80842d280009d183d50180c0a070040300d03d0685401c00c004103c1d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 76857313 1250 76856063 76856069
    0x20a2c03060f0a06050a0b090108060a05060f0c0708010b031009020612010b120f10090506030f06070801150c030801050103050414071403010f0207050c090901111201060f020703120c05010f0204 85
    0x4100c00c1c0411582d00f4181c070030b00000e010700780c41d000c80349400c1030310000551203418407150501a40000040d13281e07450515150243c9401b602540d105c1c0c0c169010001a078000c1440140b280c09000000309190310140300b4104014401401002220320b103c21120040c050414140c1c3c1102d02000340b000740c400314420030782c001c010f1100720360f5032101035041e010310040300038144081081020061101c0761880f80800741c2130396412440050680c0b2220002840d14051002070760550040b82d0400c141c4e02c5e0410b031894101c030090b02c6200c0740d1401c0400220307181255410001c0114926030018005035100c0e0b4040c50340a071080254000400c0f90002c480d2030028698810302800c03400d50324130031240c2030078040e814021100c40790960400c481d031354406407140c8607013900901076111900062407109094001c450249111022103135200f080d5031a00d02c2a0100340a110b0204d4100720038210003601c002034440c2281c2d046840802c0040e401d0a0440d03000043d04c80582d03441d9242d081e09510641c9610040000b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 76858563 1250 76857313 76857331
    0x1203050903120903010b0a06091a0702150301050307080a0b010308091909050a0b06030f01090c17040c050f03031810110114010905010e07050d0207080c0a0f06050a020a2c0306 77
    0x155843c0608260941c0c00300400305000b000c6003c0204a0b0503080403843d82a60340203410038602412507184a851809040406503000807008072003402d03a20700d940254180d8134194142d601c2c49454108440da1a81010002450064071200400201395000c0103000101d60091541c4210143c0d0343d0782000041c81600302521883d500c13014081c52020038820400e400308280e0342142145800100304403144c0d0144100382e049034441c40e884006500c20561880d900780d10300300110042c101410220203040c50f900030207010b101d210920200e103160000c2924200103c10341c10f1142840041c09100c0d05102c05d00f00002403080101070217400b4042800303450042c51041e1b0040c0115890502144141d400690041c8441c514180a02c01d03066030000072a500e100f2491405a51418a4581442c651086000c584414000d0024207020040d1408000c00c10341e0040e50248480c3d11584c549000720b110321410f845c0801d400e040394041300400e486d0344001100c4110202038240301c100001c24100103045030002d00b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 76859813 1250 76858563 76858567
    0x31510030b03030a020f2817070b010e010905061804061d1213060c08030c07031809021803070f0302010e0d1a1b040605030f1009020c1609050601020601120305090312 73
    0x845800f00503440c7c0c42c0902490074540154151071180c0c0c00c50b4102c41c044d02d120221115600c0300134841044814007544800c10901a40e528207204248000a02a25480a04000c0403d58914003112490b4100c008160003880ca902d80b07607a12001404280314074560300c000651445419101440110715800c0c0c4481c0e8507994981c0c4601c2544031f0305107900403500344a001d00400001c00d1442043e00c1e444082a041240d484009003030a68500804041842a442e00c0000110300044240c004c1d084541e120305d24440a412604109915000c2c41c1c09429410f00d448801000558440d0041114802e8050000303603040c551601c8004000c441c103900e0304d00840203001804036036624018080744041141003460304003424204000c0452001500e82090016a03038089143c480300d504c5104010304504104556482d40c3d19001500c8081c15445624000f40d682d200083c14101402024031408050703029098681c20500d84513508011075200b40c040000c248021119034404100301c409a1030961174844e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 76861063 1250 76859813 76859833
    0x70803030a060509060306040512160204020a090e060a050f040f0b10020706090f081504050118062903060a0c17070c0c080c0d02040c030207021908070b031510030b03030a02 76
    0x44c221005400280668008010800880c00102e0003407801c0c030701c0c02c8006680e43c00301c0c06020851000180040d500c98070001d04510302a0f0071180300c404681c41c0400751005075442400708803084880b44a407940003c40b0b0300c0604d040b4901540000e40107001d4a00000b07200344000e010034290700542d410700d030250744a0301052014640040d911402882c0c030102030349182e0305011b803503901c03580a403002c515003e20040115041201c01e4110010441d04d42c001014140218140000586400b00e059111036160304081010110307840400e4803150700c0940186890307221110004000c00c080b95000c0200308105641d81000084ac96a841c01040c0303907565103a114045051010004003190712544d15940030805161040c0c80c0c084404000c10f80407a40095020043d52058010b44107810000758850307a09a241da102010390f00c0090305940039030084401c82a260301881099200589030350f00b9962040f011004245081c0400340351900040c80c0c0850043c28401c0404d207190050a1000056003010712a2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 76862313 1250 76861063 76861069
    0x6020a020609280c03020d0605060a05060f07080d0b0303190f0f020a030807140a020604050d030207030801031b03080325020106060905120f07030f0c0e010b1209070803030a0605 78
    0x24a820201e03050180c843d01034240078200540015a00a03061142c107000c0400070320288003450001590042c124a092035030514100c0002c010031122207104180e5900c0106150501c08265129100b49428083c6050301350348402d6101c2d040948805501500e0705d01d410606d0303e0910203820b50020340314004c0300403200035002800c03903ea40032000341000015070401c2d00e03042d80040c0d171036400c0e90907042c4690951140107048510700b8035501c5028050f08001026641141c0c00280d00348034038012001e075410000c00c018114244e2184810241c00540c8120061012400d110045a10300341d0541c502d0a8444d5a6610080c40d50012a42c074039944814110044141c07601c00106004041c0c2c0c1d2000b0003405081280c0074102010902405002c0c0c10240a0062030600420110365154404c42c102c0d600a5680c4c688800008104602140c511b84030f800f0000e125600c0b00c41c41410b07150356078041802c0c05007100159080b40001400708a04d0b01c81c0e05000240c0c05803d00055026010704034012514038103000034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 76863563 1250 76862313 76862323
    0x3050619120506060d080706020309010f06061106010e011a1b01110304060f0606091202040b030109111306080a060b03031908060312040b1213080a0f0801060c0f1214040306020a02 79
    0x1000380265181c202c0b01c800a00446c0844901c03c3d4014401622034a810b81e40307900403c1285a981c000e10b00c0c00c4400300f0030039045040122480759540448119a0300c0e00d010304140c1a0a1145e00e0f0f02e0742d88480c00b40c405040c2040a000d0300d851082e02000c0d4582e0929041c0c2c01e40b0b510080340000a0700000a110611016005030000c2c0c000d01d00051109501d0a8001042142c080c030548080701d03418100c0104554880c3c010400040c0000c0082c000351070136082140000c0840c4203801d201d4004281c000a80390b8042c0100011180844094030800300a03440e0303d00a4030f50281ba00798940002c2140300141c461030100c8910030002c55640114600d00304081c98030300050500c004410328824401085046141421a1035145409004541c5034964004060182500003c0244206800f1814068099200700120b100e5a000d5a4184060340e882c001a1a00141e041c0040d000c8060003141c080030540b03554104403140c2032450708803806541700310703000b40300d40080d001110b4058000984004282d41084 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 76864813 1250 76863563 76863571
    0x120b0601031e230a090f03031a0a030501141807030f0c15030606020106050109050906122109030d093807030203070b0c040b030414010b180603120306030d03050619120506 75
    0x80000b17400c4d13512001e03002c01c0d40c0702d0020201603c902018042c16a864401011008081c0405d2441920382c42c10501a0902c081e18807403010500c4e000980300081c0c021407011402c20780020f80b0005086444000c0000d0410383d0656209030048800940640c804c01340c480444815500058124140307040207007911034981c0701c2d90410202410900065440c101c0300780c5c00420886512803400c0c80201810304002c0b110001c82001e01041087c082003102ea0390080601c0c0c0340840a0394840541e0407c19079002206000300c209003102200d031051700f03c5000c030b0440002075018000e9441c400c0101e01e500349590100404800581001c00e4103020040000ca6158009076819601410241011070007a05408000c1c006800344140040000c14100c0c20351040000070b001921a0240d044c652030400900f46090318514007a103d078090030943d500040c81500c3c080c010007005800c10001e081c1c1d08501900b000341640b540040344d040c444c80500c280403003d40050286541d0131501562904040d070034a00014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 76866063 1250 76864813 76864831
    0xa0c020a090e0d260403021605090712020702120706020709050114030a03050a0c05030301030b01051311090d0c050901030302011401060302040f05040522060b0307120b0601031e23 79
    0x800b0307203080c02c60100714801529894640240c44100029818684200300000c1065030840f080c1808145503002c203101424403440070004d2286a80c039420700c60980d8084404900280b08117030801d94400c034940003030408600051950a44000c0d0411042c01c040c8bd81d80710342c0169108803400c1140351014003d4a00401c80c4032440c80074000c420010075140c0610a100a04008000420240f000c5c002d140300b044285e00882181d0306e030340c0c4034540941e140c04203010b2544100d090141c000c1d003001c42c41c0542019011380869540c05c0901e903409001501c0c2941d94115959401c0620110b00d58070f0f00c00d032880c0218000c1d0b0001c201c520f8001800c66107814182c1001d0200b40c01000140310342c90503c0c0500c02112000e41340043c4550300c24030460041c0300c4081c408555140b841603141c09121a0f5002250302030030840035540301603a6040300070850a900da400424a0f200100010010340c000d0f40a01c031769403103a40c0c101c0c010200c0120404200e514214490512800c078404070340f2585079014400307511030201 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 76867313 1250 76866063 76866071
    0x100c0509030a030e0102070e01090b040b0301020910030b0301140906070e1c02060706020f13090e0a0b040602030c1c0e01050106171501020c040f05060301050c070804170307080a0c020a09 82
    0x2010120307031540c440c40c0700a01440104c202458040e482042440004c3c161113660440c0c035610b842c030000c0506600d1043d54466401c1ca0360288052134103100702e6000c3c140c001d00f049045010054241c01501418025944c155641c07850f80c40c11003c50340c4000c1c80b442c24032003e0210351800d048040c19684680b40010f01410301c5513030028144d208102002005501114250f440750168074211019114003c072181c1005c9010a0154914030403206039800e0710035101d0f05200c0c10080201c07503030327480b0800304004e05a0400342c004140070840541c000c5402400d042b51642c078210348282e070507e0350b603030f64481070414070343c0ca07050000609000c0c8146805000300f490440b0f100b00d150344501c07514500c081d1185e01c11014024044407035a000f0424050b131040007a20610071b5623104207148006010456155009500740740c0060060500c00c030032140000d0384240b180e800c19041c41a0a014400c000504403600e100410019000c14003103005007184150a0740ca20042089510500161040c254800c5207010700b8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 76868563 1250 76867313 76867327
    0x90e0303062b0326010b040b03091c120c02010216140102040f1d0f0112060209010201060323190f0f0602040317030412020105060a0501030c020312100618060903080d0e0d02100c05 79
    0xc81b01103404079002c3d00e01c00394407522255401c508241e54103000862035001c001600c0c0c1032907001071045542000d45441000355004100301a420f0780300b0488a21114071120600900190f120708062020b4044000014105500c40140c1c400171015908562040d030308030400718500d1040007801314ae0186441036001000d501d00480090310b00025440104442c0d000705080300303030742d200758003140c015600203400342c0c0014038440040009401907615a04c0e18000c60300310024800702810a41500c80d44050f1034050300c81151911070014086c6442156019000c21000000c0350743c840404805024030000c203075a03801c081c43c01841120745107000c1000d590400080040c00d07501e101c144012280c0078200404c160000c1101282144500312121340c01613401420310180d510000d48800691b0000d03200d8070526001400308280e800e82c01c0c0300700e030300241000005100152801340504510700c1000350214040850402d5503081030024015403006178000305040c1c50102c207038018818010641e081c038070314000d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 76869813 1250 76868563 76868579
    0x20702030309010305041e03030b120c0f19081b100c21030603020409110f150d0b0d060911190503070b16080307020c010207090e0303062b032601 64
    0x40c8481c041e041c995200001418000c0d500c40070031f18848001d49081943d4103910780a0010100f5004c0e0314042c0317000d800c54140c480e20024800707246c504004c18014081e1444010071490030300100703141c00e0620172050005400c0308204070416010300d1400090200600c0d850502120030040301c04103040200391a005c0021401900c2c500301d04107842c0003d0041d110301c0c0801607000d81041c3d8402500035107010320b890184a034800d20000184c00c01c45002030003100c42401c01000d40b400001110030604100080c005030a9960300010740726001400201c00034185448101c201c03440c030710303055075080002c05502c00c0034a8140d00c00004040116202e484040c2403101080d40c941890043c0e900c40880028549040c8040400e003055081c0c0c402c601c1741e42ca24090f80000e4039074001d90003090151054110100f1522002e0050150100c000307001982103a852004011015905201d4102468000c10300d2440c07243d03090003100c5045002e03444100e242c943c0480d14510203001a25028410401740005002c040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 76871063 1250 76869813 76869817
    0xe0907050a0b07170f03130303110706050906070309030f0e1807050a0f020d02070504050c040b040b0406020d0e18041401020a0906110703020603010b0f040807030f020310141803120a0b10030207020303 88
    0xb40080040d2120f47d80940b406a004003844ca5174455100e1380890b101c0100800d42c0c21442c03043c10308400380c43d410348900c034060701990040507008002c82c1d01074003000200c5200d401c00040e40c4d240100005811000c1c040c1d69a1035030701c203803181e500040001402c0021203821200900380400740d0700c002d0201d808d40c260000d490740c0c014000c440c4101d480c0d078041f962419025058502416241541640d680c7e80c40c45800203e6000d403048170f01501518103032401d0507002d805044c0342c243c005000080711506403460340e0103010006000701d4540c0c90440031002d0529007440944105001a110800024103105000e0503014541850810983c461801800140c6419060f641190030748035100d512500721100c2d040c00c0340070b640c10034441c1d840b0310a000014041c03070b203a200070f03464020303070948c2c42009040070017000b540d030040301c810840c00030745000c0b80070761f40e1107aa123203c0307145040203403410015290740382d800d100d03001d441003e445500c5100050107841c0046144a05030700c1c80c1404c42c6050000d50100b0303224 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 76872313 1250 76871063 76871071
    0x3030e120c1f050405040204061e0201050f0c03070201091a0108070f2303030408030f03190b0a060f050c0102030f2d0601030f020403020409030201060e0606070803010e0907050a0b07170f03 83
    0x6000042e10b6031a460041c001d0310058000100155190754840301c0040008650005101c500c050038042c07103903194010710855000d0030400d61703d2a2945da44880d140c109074400b411310b8007150b6803403100001080b4041216005e181100d46400711a500d800c4005140c41000d41040340c40c885420010058000700d100a40440600b0301c40e46200c800c0c0d400002030941c0641e5004080b6400b00090080c0c1040510b03004510900203c040c01c03440c0d4480c0c1c0a543c0449040f1054113400ca09400c4040c441d050161140700b030242d00ca850001d20307140c44c086800342a078000740d4006030000c50781c6d0184907840da01143d00480311660030f020845c14a4142c1034501c2c0d0307440040c0a40e41815510120850b02e00d030310b601160007554002e00140000502d40c500240200028481d403169101d804012030010700e4400201c466054101075664103503400c08102c034612078006400401c0c948980075001901d51141d4a00c40010002d0041154a544290610143c00c0c290786000c980c0c001c0d4100243c0321884540381c2501e0700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 76873563 1250 76872313 76872349
    0xf0b090d050f07030c030b07090b090409060f14060f150a03050c12070807020d030b0a0612091e110604031e0510020d060501090e0402010503010e0a090c03030e120c 72
    0x4904260500ea4100b8060501e18036080c05280d60101c280320080c030011040720322500807088159590302d8104d402903568015004800d03c00c104043c568a059004045024080c0340c00050001e021104201140c00041080001c1c5000c04200149850801c0f05000b00c94400d9649405044042041c10325610840c0d0f0b00c02d0a165071800070501a048d004166415055003501042e094101520081c03c02502200c46d40014841e917403200100e00c2c817a0180c0c6044c0740c405044944420306105040e514030055802da032580d5541e480c40c0401056032581800030001d80380141d0b180c2c41141d41409031030b0341d40c8446085e005483c00c01c420000141d40180751030030b80b0001005005036040c5841e002d42000440d844201c4454000b107900d0304c0e02c8200703030b2050302282d07001d889010619aa4800c11284084205c030003030b003c01c80030700c01080b540c00a10701c22035100821000014080585948041ca0a005a001039001442c080c145041904120842501d6102520700402d0030360141ea001510340900c43c40c0b8020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 76874813 1250 76873563 76873579
    0x1030209060d03020a050d0c060b010e0619030207150605180609010303080903070506040b09070504060f0608090304080f06100b120403110313120b0115050904180f0f05070f0b09 78
    0xc10f052081c80842840c0e940030003030310340b060341c5504010840c44c3d1403030781541c5841c50311050201c558001c1c404001e00c603030301800341800e0240c618010001e9903c02858141410f0f001c01005000985088480307002d6103540c400000d2181c01d01d0140150081c1c18100c201c408060603060046540e00e18008904495051820003ca0340c1c42101c1607046018003c2c0080c400e100361010700041001002401d0b01c034440c460105d880d426503410801c015101e80740b0558844020344034060201a10580c0304540c0146003004503498550303140304080c90410031000001081d0840700c144801c4800d00b190300c0300140340c803c40340b505220a00740b1444601d40c006c3d10080620410a981704010a418802c1e03e140c58940201c0e20080c40d510303170034024140070141007250458500301c004136120400c8941d090003210700c0e03503445091690702820700004001d442c007a92014150340843c400043d4940060188080c415001c8040d1419585059403424072903811100e0310741c110203424000382c240340c0c050721225801220660 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 76876063 1250 76874813 76874839
    0xa02030a0c080405300c0a1502270d020607050f0705010e01170a0e0f06010801150e1605040308030901020d060f08101a040c1d03010b010e01080411031f060902030103020906 76
    0x1038052078020000030303180001311300321900c0103000c01d02c7c041d450b0003848081d141802c1003211008a2013003141d040e4916410383c208542c6007818900120300c1800140210780008031940005526420041003291039134881c2c00c107600828018071098008110a0810300018407810001a00c1040206049030500c103140700090448401c2d45c001c4440c4410080980d08449615444e458a450f0300340284000c81d0309060001c0300c2058507000c20780441d0305228445103039441d95000c0c3c00b400901078010a0030000306100c044041524480190300545608000503038440f81d081901c415680e50b0780c000042d8025105041008120105c0c03041c41c1a00f41d022300040d14001201a11301503040c41954035041898044610180ea07080000d51450f9055551680010f1034104105805d071000141964006801c1081c42d48865000300c0c2400c1d0001d10440715804811041404246800d900b4108600160003801200c0705240003403140340003501c20080294030759811500031680c8a400501014001c0f20b28100fa5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 76877313 1250 76876063 76876123
    0x30b01022a0f0d0b0402060315130b011b03211506050a08011401020c010807030f090305130602010b0d080c1c030b040b01050c0606060307170a02030a0c080405 70
    0x501e203180d403181030410001d4010312000d20103002000d1107401442d1101000311949000800084900c1c0c0c0500c81000c0c1e66550f84c20302566410247c40b8084e01c1500c4d0a04100980d103030394440d0104121081c00180300c1c00614001003d401d400c0350b01030b426525000709040460f610003200b107041e02015094903a4a0701c0c2006a2000382640254a0b088446400c07012600c258402c0090221814590b200000e90740c81344c03240c485c0c0300380514490307015901134100417045500800f40c44d82e0081c92801c0000d036000c1d91120303080548240082c21070000d10009481c2a8815070290150080d081902c002c002114147c000b184c0705510031007025040c400e0100702c0c0880d08008000e00d400001180303074616007107510003602030042d1880056140c4103078100501070035554440c0081d9420344020341c0042c141a00e0721070030b0107066400a0f01603420000c1841408264002c100e00c0c4500a20506600599030b251038182c50003121482d141c5101044a142d043c0804200005078003810007075402c00086c0301000c04288 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 76878563 1250 76877313 76877323
    0x501030c08150a090f0c02010b12060a0c090302060d0c0f02010212040803090f03180423060111010605040207081305040903020a06050a0f09050309011e1b02030c09090609071202010906030b0102 85
    0x40501810107a8171890303402c80340c0194080000c150002d008000c002c608115001070514411107032540702400284a41d016608078055180385420600c00058494010400c29401800c01010050302c3c1e80c80d1022a44d44801c0450415a451000318142443c0a014070507046002c0d102034991a0301001003405088244401c800e078048840489540d610002d00c41450741084d409114440c0380f0301412051010103c01e03048010783c80f40d40000c0f2030340d642c14005645200c2406240c3e4029980d5086c04201502c80380b004101c180e00405015441d0b0505000d0600d52548a40000d07003e60b080c5203400002a400207440741007690300410215403941d030b0001a4006151a03220103000354100950302c0140400800200641c80342a07880c503062103003191a04402d8182d060350080054080c25078800b820903001c1c1c45c1c449140c402425076000c0c911000004901c420252040522600407506200c9501000c21240c2c00800340c40008681c00d040f04d80018066680a11503c0185621101c0740c030510303803080c4a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 76879813 1250 76878563 76878569
    0xc0309090106090e0705030124170108150903040506121f1205150601091e0e100807090e0d1b0b09030d180c092004080607090501030c08150a 62
    0x4101c0da9101001003a260307140c41808000c100750004551341c14480d00449060790003465094241c542420311050034008080701b1107007000348040c4440244030b25404003e0003440504020000c80c088a00d24408084004e429241c0c80c2d03100b01b0041089845030800c0d907201d80403820b00b50001d80d40d0070301c240403203204212200600d4002080c0214140303105c0400500d4060086007194110620001c2e5480c00c000242c42250201d502408208428803802180141d05103400080703209071681c81c01c81d02c8126070141c41e10f40310070000c11401e0140340410810710000b0001404103000407404020051344403001c04036187c00300800165502500051312510f43c1d019684044201d01919020900c0b549a80110b2203980009041210b01c070500f0807181018001c081d082000c105d0050315000c030f503200905900b040d074586120b040c80c2c2c500310460b90384043c2008051380000b4043da0300c0c02c4180140100c4054201c14141842c002014220950101d600c9a110605160b4034020000f00000189203240541c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 76881063 1250 76879813 76879819
    0x7080307020718090b04141608010903180b030103020d0f0f03020d0e0a0812030901060b040b0403050c0612060906060c19020a0807030203030d02030c070807060212010501110a080c0309 81
    0x109100440c0d40c0010400c04881c3e48201a0f144044890a41c405958541d030700640070107584000300e000b003a1b0981c80403212a140d00c00301e4074964403001d07402080c0c010320f510040c801e956414868090542141034104070085c4418011003903828003241001500040c00301a006601c03004888040115040311000010703003082c49400c0c403607101d1030025500d54000e1107041c001040d1070206101d80c02e01c2840b0100360b0300c0c0352003d09000c994100703032a0310316080105140038541d20340000207241c1c250382e00200050201d50010f90750f034038111300b030051420b005103000c035000f80020003c10700d0340148860203035004101141c41b801ca903110800028210701036140c0c3c50030a03000d104141004801d000604e030380780e540309551803080c4a56030140d007622040e81e0710002c0d405030410001111049440c0c1e00450380890038958040c1403650342c1c2c5a1600507080494101da030a81c1c00201031640c07801d81000e1a00511091903c103c0006600c480d00780c0315003c1c4413008150701004120681c070790006100f651800c00e00a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 76882313 1250 76881063 76881067
    0x4180c0507060f0914010501060903111f0507060e0c100f020f0105100906080c090f0703140112031209030203190909090b04020a080109080a11160308030a110418020f0708 75
    0xe0f0403400001c1c031000c4001c0360010080f240c803401200040c054a4100c40351910b40100092458490b100c250040894044e0700a18a41614103051189020400014070981d41c1da43c407140c0d1403800c10211412940c400c405a4489001c0340030996404c4903000a0410500d00b20990980004090746016202d900d140e00c25401c1c4010012806600000c00301140e51526041c4885079642d21403544840141a80e00c0c0c00100c1e0800107140d4000441e24203800c001c03036142c0002c2e0302c2601c0700f400640000030781184184003481000d141c140b40d4403103201543c543c80c500e03040010494940e0040d43d684690740400c584201100491821107014809880040c081101c041c095051140f400c0514000110340c1207111b5030219038041075494051240c403280030f074881d0b0406c0c54101c00340425110b50340c805403003070740500c18548500d00807008141001e00940c459500c4c031b5140d080c043c05003426622202d044e020036040500040254104003144034411121106005079182e0048000e04c40512880300042c200b4840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 76883563 1250 76882313 76882331
    0x18140114090f010f02030105061803030705030a08070906081e07020c030105130507060813020402090a08150105030d180e070903080a090801050105040902060702090601030b0a1d090304180c050706 86
    0x804950b25440b8012400200300c04210300b1181c0301280000e001d00750b00071805105040503c2c01503460194420f8008040b2030520103150b8400f032441c0c0c4002c1c06680050400700501484940042c5514043c000600700700c0450b1401d42c2c18500c6072040325101c1d406502000e4041400140280204591440040d0081c003036468080b00c0180342c407940443c11a041e02c104800060081c1c03003061030600600144000c07904194464080002a4115001d0254484207c41c80000d840a0400c4494074003840d0034106010740d85004101404c040003591500d091040c210460880904d08004100645001e07810707006094031207401c101d03526015a000142034580000758400403940004042089442540084c08039a0301c03001404282c40f5241c1000350485428451400140380410744654080010300d400200070b600c03440014024009036100142410691f601d0481d00c4680c900d07880e0780041840d00070b5161501c0c04014814075440742040440c0300d9036410482000c00d120710100c455007034109800307200c001d103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 76884813 1250 76883563 76883581
    0x80402060d18051b01080106030c03180b0406050f15011107050a060c05060108030711060c0a061503030314070804031803020405040303020309010e010e1b1305010303050415020118140114 82
    0x80102c06840e1481905020f000405030b401c0404e24100301a59a1016030b40f90140a4018000c155240402e1607140e4042060110014041c020054060000042581003e00f8490210b540281c41c0e080301900d44d40030801c51619000d001d5100d4075003842c000040d016a03250306804c0404c1a0061a4001c40003c1d0008480d03600110030505580164195041e80c1d80e03485010750b49114407400102152042c2e401c044842c64424090001e8178052020303201042000e58410040b5640b10704481d00044044a041c4141940344c800e9502c0f00504803071400392030a00703a1740504089001007004041103480320080c078101c0700c10006c00c2d00660b4007030410700190400e85005006900110b1703040c50030f90720b0241c5001e1059414001c01502401400140030914001c0803240c60724510301c0d10084d0083c0304032038031200c0490705201d2940254000d03580e003604d450805109500e50b00c1d4050455046a050825241140312083c071200283c43e03100d0590030400c000002c82c18094002a01c140c212041c4450030486401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 76886063 1250 76884813 76884851
    0xc07050c120303071707080406020c0f010507050d0b010302030c090f0d050f0109030f05091008090109020a0b0a020607090f0b03060d05100e0f1b06030601020f060703021c0207030e01080402060d 85
    0x28016145c43e110100b90310031200c0d81500c2220440001030403007011034003040055008200c0195108103a550254030b2182040c00d44001b60b62410008000203a05000008148a0030a08007024642076103941040b801e500041d024000c070981c807500d03002481c0101a42d0341a40a00440d500000340c42151100d01c030104c4c000c1114500c1a004190750109080381c8503c954201d8081c00c40090840001d82d5100c00110750003c002400e051180d941d92112802580da2060658020b02246032940d030340c1c044c1203030300a0a003080680b440d0300f441081c02c402c2c8034035a03a610022080d0f40301e51070301e0703502d90b900c020010340c0b01c880301c0c1005002e0340940c100c1c480c928812900411112200b560850b1441d079640d049295440c4803404007400301130139141c0c1070b02107458540001c5402c01d00500c110b030320400d140d00e009428403405031501001300b5800503807440c42008035200400801903000c000c5050007190344015102402d0f40351180c0c100070071200040e0840d41d40380140c0f032070420b00340d10401146e811900075034054 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 76887313 1250 76886063 76886071
    0x30f063f0b01080c01091203080402150f040305010b01050405031203040510140a1109010c0b0910020a020d0e06041d0a0603080406020f0c04151208040b160201031b02060c07050c120303 81
    0x1d07000c0e006000844d5401550f642c2c2c22111400a92070218039541c0b02140c2481c00501700f240d2009940001380c2103280305034050b0884014901d0190b58a0703285184c10b5007144c151a0360346060000522040003180c1c3d000c51802c810486a410082d900c0c1e846141203810000c4409001b12844e14118450035008040e810051081d40803010420108003103c1c0020034500424098900241c2d01008100008001d9800c864000075024200d4550b401300c5054101a6001540241c0050780601013048410750310054861141a003656180d00c1e0a0408003055106803512a02404031030401c1d02081e800040c50744548011034000007015100e9417a124000e4448840321001d021724070a0007000360306c0346068401c0d442104940328168000d43e10b0303d0300604544080500a5942c05410700000a642d502d020040015079582800808456440e20000d41102d01000780300220342c8040c103070380c1c4010341c000403540d0304840d2051005445580601c3c0c054034081031070200b2500064a042c082e8040c001c000051401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 76888563 1250 76887313 76887329
    0x21c14011503030e0a0b04090e07080303040311070605120103060b13110901090e13020108061c060b0918060601110a0f050a060b090702030703050d02070605070e01030f063f0b01 78
    0x1800604600300822609680961449900100000c112300301459105501150b24001a12a443d0703941c8856425904100c40507030101d16081240068941c050011901503c0a420100e043c150a03096240242c4414003000b07201c255030b1080802140c3c0d800c00302c10350a030036440c1f09201480e2000c407035480681041040707a020407603660b001b10f148484080b44900c03603140300d03580c2c10f500c200030340046a004002420594001541c0c5142c519414810a500d00c09503000c4c0c0c801217081201c070024010b0b00717a0003e1421590030285291120003a00102d04280c01a5003464040440745000c0071031400d10414140040c019010600588100240441d003001058044c160401130780b0041c02c00d02c0340710282181c4c2400180c200b0044400040d0089c07003e0040e20000c10f04c01405c0405943d104d4003116010f8030b4810109001501b02040c641e4940110f1084086405003804080d19100449805080761690301c070352151808108451300b00c16800040d030074601120001c95903191420320301c014201c02e00032800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 76889813 1250 76888563 76888577
    0xc030807050a020a0609030306030b0c121308030a0c05040b0408070f0b090a06140409050a1b020115031113020f1306020303010501090e091e0c040e0109021c1401150303 74
    0x300c054081e400b0380e84515000d070090320119070720343c2d80e01005000100044040c103613610b40200200d9084200d0f5485820a02d02250b9908040d52080232210740c024003007240d4544044024000a0300c0301c00303480c2c22180c1030b6000b045e4a110900c095600780580c0e00f007110000030120340003030039103400503a1004968000c00710800268640d0b0072403032184190000e881d003068149104100e4207128031003100d070000d5002e142c035040035140d8288006544003a03403000040381d2250041010b601072000343c2441c1403010700080001418005840008400c2840081c0203942c0001004600c0e445003841c42d0070b881d03580300c0211340e90f60b81c1003025106a04906400d0a400080120100d46680004101c81c1616016101c0014080c58030b40e60f4a441c1034020724900c0c0b240113480051600040c135040742d107400b2610074041c100e41c010640034401101c400e00744c203060303580c1403400d0400540c4455a050315840c41a500b900c4089050707041c91a680d245200010300c46610b001c0b0300e00d1030b03954000200010346e4800d031740f108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 76891063 1250 76889813 76889821
    0xb0109080c181003120807020c0f030d050a0216031a01060f020c10020a020d030f110109020f01050703020f060c070209011e0915080a0b04060605090f24030303070c0308 74
    0x6540c0c1c18200300282d0412070400c4800c2c1810900c108041e400b8400307400c1c20110a4503a40c80a02828001e0f5202c40402c4041060009a84e0140074101301c041c819242c5407445a50b8800180c2d99440012401c400c0c07040018105081c14400d000710001c0384400c400072a11299207241c44c9910400080b441c20400043c503001061040c030903004179164104e80c0c3e00a0035990b0340802040340502c5038809140c1544a5030400800584402c0700301440310f400f070348035403508a8541c2030103003480c0c01c1070340b07815120b0b45400e01113801030f0359000084424010070328040351921035500d400d9281200d00d00d0b840401e84221010131400c0b0311881300511400e44241e841c08142e90343c82d811030400380701e4400f01c0c0c4e40e01000e015080c4980d01056000c0d0340c881c8100800b8078031199403034a20500b41083e5080a4541c14207850401062101340c0c0034070001408265401190f91400e040300410aa4000d09110820590201822542614081000c2e600c0100406517a0f40e4281000e01501a5044070303401c50108400302e00003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 76892313 1250 76891063 76891079
    0xa0b0d0f0309080a1a0c0c15060307090b030a060c170411191d040206190306030203070e0c0406050d0603020402120a0b01030e0a0219080604080c1b010c080711060a030b0109 76
    0x40400554004184203100a405c517840e01000b00c010280100da000a1003100c200e07110801c146020013a504000d20b44a0078030340d083c14103001141e04030142103804c0c8602c405042d1400144c089113190005000624074044003000c42e0034100014551401199803401d000500030310300c40142120504076a14002d40d4080180b500710060356104414602071100c000340d00041c0c078602da40e544903100800c4140741000100116180500300100d20001030358540007801141010002040945808000b84086182401103901c00b48958080c14040005c081104107a10103075801400c05144d004006540300c3c01c69a0b15010000da085481d00011402d00d6808290b41d4042d11422501100480140130321404c60703001d01840e0202c2803002112088901c00008a003102031003958041d13845004000d540e01181d107891072605903910f409058201c5102c004611681c0c2080c04000c20980c09a81d09444004509090440791940c00da0143c02480006411054991681c0840e030500400d884862a40d0703118040c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 76893563 1250 76892313 76892323
    0xa1416030b01090e15090f07050301060b091309020d0602030601030b0906060409090c0302032506080f010303260c0415020c030606010c051905010f0b010203090a0b030a0b0d0f030908 80
    0x582039101d204014010909280c0000185101080450f107800650309101825444101d6600b4620f8012444004140d4014001030300246001c400906ca0281810b102032118440c601c40a132003228410403040c50b507509500404503140d001480703240003410341e05006019500854002e0f0000b8074000d8805105e02d03001140d2401694050101401d0030305040e4490020141d400c42601c03041f00c0403100000507a01000000c400c2c4055251001c005030124055505001403900010280312413001004010110118810704490300b501d41f0384601100450410000c0400000c000d420140440401070300e0032049004008460842c05114580004100300704d850b11000c5c0c640a134140c002034041602d0358070611250440d81d0184065441030b60301c1204012402000100803501317651610703020361604103107108420701c00e1020300240d8501074501000460010440c082c80e041150044040340a100c040e038045003003803102600301c0c91054591305054a03202504007040700041d0003404085000480070070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 76894813 1250 76893563 76893569
    0x250e0c070c05040f060b0c03070318030b0408090402040b12011715010b0c03040b12090c01030915091407030303020c0111040b0417010b090f0a0606050901050f03180a1416 75
    0x464441e145081a0400014111258481001075211203000c24500c2c04000100943c017582c03401569180c00030714000d084400102000900450300300c2007040072801e0b4008240d8816400717000250b441c00d0000018000b8011500160010700000c030340d003c001542407040c20706036100d0807203481c0b15510070741a05907a22500e085440d0305101c921300411900091f50050890008400190390402e9100c44602c24640c02c00c000c03000c08911030360148910354400340032800300c4007400c6c64240030101039601d40c011000103404515812030760b15000c3c03409000e90a4241d00030f036a0703040180d40b2003039503e00300100a50403201e07103d0070359460200300351110b40c00d040071681111102c00b48541850b00d013443c881d44d0000902881007055494024840d40e690354145107510501610b814501e984c1041a4603404075102600700405104042081206903a040015104000d2100b654541d481e0380b06203941005503120b02100cad40d20f2107174000c2142041130750300012084024280880c0d10441403a903503107640380c0543c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 76896063 1250 76894813 76894823
    0x112050f0d120b04020f0307080403030605030102070305030c0702031501060903060534050d020301060c20011209030212030108150f070516030216030804090e1203010e0603250e0c07 80
    0x7030b492030400000c5400800030003000034401802c00c803511000781e1603a03100b25000c1d000039400b801004201500b522070040a08010740c003c50170901180c0c2c0140480c80003500142d00c001000c160001199010441d2954200542a90316a19692040094940d0710350340821540710341440c0c0003e2980307440311034007001c80e4003c0c07010380040c10300001c141e04500e04c104468420464100160022040c80b40021030007001166614034001c400780c00c01d4200154072480f04140140c2950b00807501c2c1e80d10401c0d1031084907801c0400202040d8a240503440d01e0300703201c80190030003400701c000070301d0601c082000c2c5142c030340c5900001d0055450110b1005606022542040850002d1001d041e030140340440301031305588680100c58218524400601c4842d10907407040710305036000601400940b04c10b0003461107405855004101c1a501d07014914907900050240f40030b000d9490700010180da80401c05e00182c45c00006041c0c0c04101c40004101e10811070340140c0c07090700c200e480170915078101003040303a07038060b009 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 76897313 1250 76896063 76896077
    0x109020f0d02010c05070b13080a0201081f0801050f070807090303050a0309060b0306090a120f050702040b031510030b0c0301060c14071707051003140c071a0112050f0d 74
    0x41003280303444001c503050341000542c00b140000203504014800140002c48401511a803002d440c09410b20903d4005200d142c004600000050740c010142d03e0700808683c2e141e0415481c03601c2d1807240240030b94040040c0390308040a022444c1c01c1240b40502925031aa11600720355076811054882031700610005000410400c00c02c0581c910030341c048a141e070b100308004104e0300803190000c0e10b0488142c615418981004d4500d0081240251005465004604002110003480007001d0500c0c010880064021500d580c1d896885035002d100340300071201c03180c91800e0f2a0900f4218103160300c0c840d0004580d15060311000c80d215440303400549040300c9150b0748040b00d041c02c0355a2650103070507031200000720307101d4883d022600d5000c403034000c1d481c0c078203a0008142c030358038080c10410050a5010100185071509515001039941c00081581c4071070903030666030380c40685141c0403a49070100162001d00b09110000420404c800c5a140b5449034055403c8500500070f0802042d16001140140c06c0801c402c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 76898563 1250 76897313 76897339
    0x18160b04050901082b0e120c0108090d120915060b0403060f060e0a0e0a0c060c05070f03030c0f05030d020706050105040506150409090c090203010b0406021c1d13060803030612010902 80
    0x400c0003c1c090303440c1d07031800802c01076088000c5609247c00700c2c0a21001c1d08180c0c0d02150550344000d40303640c0920100001c0c4408818220003500714000030100007843ea40b039103514818854550341e00412901031010802056a585103030200c190040d000c01c44900382490103000081100d806101c05a03592030007990401d0300c3c3c11150100a102c0c1c08040441c42c00f4071902e4401091000c00392000610741e98407040781c0d03901c0b6440e06600f00301d0360360440071030b0420158083c004a50b0104040c001241d11000c09400c40d0007904080e0b245008895100b40c8a03030001900c1c2e801c00607507030031070f504940701524107004035182d0008101400303440501e203c0c2c0090040c03004205101c7e50b6002500030502618444c100c039600da5031a4000c2c0d9100740c00081c203180c000542040050380c100503100b07030580354030141348034213000c503c0003015a1500e14202107940f4281c80074042d2682c844c00e001c40100180715040014950310000d00e07480e50011101c1c5440b800c10a1b698409200041c0a0600481d03070041260401c400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 76899813 1250 76898563 76898623
    0x81605060d1803030b03010e120409150b04151103120402100e09160e010507080f0a200616050c060f0403030b090723040b0318160b0405090108 63
    0x2854600001c80d441e860703031000418960550000d00c1c2c0c000c0ea804515014290309040c29100c0d645600d8140f0b03481100180403078006201a50241e6503100070124584e08105519001d46006410510f0090301c001070009602013001c1403401502c5aa8803601108092513089030340f43c0c0100c05102c11000012400540146068544a000c1c28054246076030701004240109240002c1112415420402005164038958200c02c002004407002d11302580ba11180ea42c4004003030003024540c400888001c2031540100d4010740a070000d0f800013003998416961504200e540d1440c0907680c41e40c40c000030007508070b00e01d84140111482940e8100003045107440700649541017010052054003003540e9614600e0003540c1d002109400b8000c6580c2c0d807841844440100d40c529a5019000044140108001c0204001d8001500e40c0300359212443c011640740c19001c14100840120084903000c49000c2c08107a43c10384d80e000c3c0043c0c1c2c10958a0b00d00581e22104059591200f6650303071040032a52046080c0614 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 76901063 1250 76899813 76899817
    0x516030f03150306052403030f03040609080a020d030b09150108040501090b09070e0105010201050f0601180506031006030b040902030a12050702100f0806030a031e0302070b0703050601020708160506 87
    0x1481c900000c248182181584940d505074200722855916070061200859690410721300c8a6400408841c0001c681e42c00280d8900c100090f85d0301609000c030000d01408280d0380b0031420544c01500c1030307aa036080420000d4031441009504000300b440c2c0540303501141820440503110320965811105020344e0b400064402c8500100111a00e43d00c0d2070322000041c0c03603034503144e028a0050000f811040d04002039580c41c140140c0009046a1402d010091400664109290840028201414200c65210098080c0f020a800590700903c0c00130511080ca589001711104031041550100a465088002c010aa0b003041c680a54035a01c940d49100c00b260320101000c45001c00c40c24400d19052003540441c0350240d040340380201189400018000d01d603009500c15030b001d071040b80506045001340d90042c045a285010381b12900b1700d90190350b000c403400396045800300d030f03000210620346d49400e0b0b80041c0a40011120303036006019030300c40066080400a0502c04000c8102080c20b800c0e03042c1801c0c40300c16 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 76902313 1250 76901063 76901087
    0x51b091f121b060302130603090c030803150405070221040510030b0a0f03060501060806060c0a03080c0c0304080d0906020a0308010506030c04120f0b1e0a020a0302090a0e0f0106051603 81
    0x10041841d141d1400400a8140002c3c052600c02507100c44050307410038800c0c0f020350310070400d00d400c03d001100004c400180101c2500e034810505a101c0d101c0d4441e1042c0d6020b07218000f41c00c540341c8014407850300c1d00000c0540302e900a1038061070f071861301c191116480340160b12a00e50400448034101c101140250010843d104001c0c00000281d50340f0b0800b545070711001d90054a840e99910010301010354810303800d40e4008000e4800c507140c8010107400c0307607560100a00c083c04205c00e0002058008180304c04aa420000d0002101d4a4070b41f41c049498030384586140c3c80000c81d443e12030019030780b0b00109009134000c0e01500c2e15150380c1c1c42c10083c8140d661005141400e001810800840c03101d0300741d10035502150180080d41c40ca11301d01c0c40c0801001c50041c03d2500155201c803155450118500d07600e69001280640150316100c560f01c1c140d000e409100041da52141c40300c04086042c066044119204403e04005403040b42d98903001511548501c2c82140c11040e0503c00702d0002c20300481d41c40f002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 76903563 1250 76902313 76902323
    0x6070807060e010e03030412020c0a05030a02040b0307050d0501020409061a0a1b020a081020090105130803070308160302070c0302010c0203120a020c0102011d0a0b13051b091f12 78
    0x4c482c9901003460b0466004403411902030000f0319103028000d03070402c143e0400c140e055803210420390414002a40e00d42d0b100078005d105d9920785031820110786003448400018034004d441c1c403403c0e210030302e81b46020f90400d00440d1116894080c000031811441c95961483d0828480901c1c580320459100312502e068500c0804040f80d8510500f00050b11281c02c140020140140a4034030140f600001c0019a01c500405502244254994840102444044034090700e024200281c0e00c0c000c1080800407001e85600000d540d00001c6000024150000c081e58031072081d54a070303200654110281607089004000000d40388003202c42040c0019402480c0c002000c0340014200c492042031a070b40c0683d168440c2500c280184c0083d4800c003040e580902070318918080c04c1120048001019201d941e641c0810280903041f48035040104910b070440ca00940c5003381c1241c01e55500200c1d103218891140c20140c034403400740c0100000030328200c41041c0d1981c0b0442030310b5588c0e4400740c075060b091008401a1082a94 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 76904813 1250 76903563 76903571
    0x10302150405031c030c0801032d020604060519050c060a111308010c0207080303010b090907230403030806030a0201020a020603060109170a030f0513050d0f2f06070807060e01 77
    0x35042d501006102581c010003a00101036852942d00241650440e030800400d101c031f14401880000d0754501c41e142000b1200b12940d100c0218110984010007403c880603403c83d900041c082030706a8001c008140020072014142c0f0012414101102d851040340204000b0f9040315010404081c81d0703401011441640c1018581409204100381e041c2c490680d000c50f030240c2d52001d441a050350103124460040048202075411907140102045161241c0c07601c442c45418a6400a03000c03501554181c020715610b4a076640196035030503804141d036841400143c010030701b07050018999180000e03500121990680c040e0610300b80e1542070000d80c1c0c0014181e41c3c10b1081c8a040880c4158011300d26071603661090004040c0c1c0801070401401c1c501d07188130124200b210400258030001ea210503540c048407002e40b5810713511201c5040c00310f040b03854410024103608060414495800c1e0201e1b1640300f0100400e014000007001400308400e922400500501e0707a507050141e4804036009500c01c2c0b80d0118804c001003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 76906063 1250 76904813 76904819
    0x1502031302090a0609050a2702120703030e01021c050a080402060c0109030206010e09010b09010b0d09060f0203100f06022d01060621050105060403120201060e0709081209090103021504 81
    0x5042e012040325440d0000399500002c10042045014442c0c01c1050b0f03420402210b00d2418010003014129580e52a1351a4003484800440d1a4144c01140c90300d0390303005807250f09459140003441800108081342c018890700c0c2603550380c19001040490114000d0302c8035460b241c1c0c1c40d02d003135403900001082a07074000400c1c440c44c90f0451080c002c141c480340c840d80c068400340d0704108424054a0016140c4951a890524110000c2c3c4a07107401d076041d183c2180078242c840c107441c0001c801030110040014034403070410548103071114180d0081c0d80200d000c044110440ea4851b030030036039510300502c6910010781c000075088030455034440c0490118030b100e50400311a07482c0c0c41801801d481050f0f111400181000b1326000102e010201e03009003101c1c41400510031949050005032031405940400740c003441341c0150300d1030514000d601050080c07080c0015202903150030400541060140d22450301207000c0c3c50160741c0762484070030481c1e4030035000500c543c8090f400d40d001d0105040004101c2c04009034104004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 76907313 1250 76906063 76906069
    0x406080703150b04120614100e0a091a0117060f0705071406040f03090e0c030a11190e0a0b0c120903030d0f061403010b1e010e06030c0406020c0d1502031302 69
    0x51000e001d05140105c141d408629001046400e2400810f10030701c200380c1031020a00090140e003088482032201c0c1c40031616542c1d03042c0014108a040148480000421000080c00c00c8408a0480e09100008008121000a55502c0305805c80c0c0b0096001203481c0011180d82c02600900321442c0503040c0500140600c0c1c105502c2d01c54190340582d114010642e006c400c16030f1040340d900241c0303442d0206550a04200e00c1c0c902d031502000d00031070401521030501d8400c0c100d6036412b44074080500c1e0004a01c0c02c004c600082c2c07040b031b800c424890040f0405080030803440401d004851460f01854018117050001c10b104441c1600281a202d6040c0010001203c40440c180a40c8a1078002c0d620001003051800341c0003400c00c0340588001c0c6c0240d05101c8801041e41e20003c03241d12008030f0303907000364500c408100100c502e0569112440d07807004010040c40410382407800076000303840343c580845143d031000c2410003d4801002c90004c201c845103178442454101c3d99000340d03402461480c101d1411000b1a800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 76908563 1250 76907313 76907317
    0x30513020301060e010f050a030b01050409060b060d05091204050307141908010c0e0901082104050604090209040f0509191509050c090c04060c06020306030c1c03140406080703150b 79
    0x121013001d0b002c01d0700500c910030302010300600400080300c007a100b00f49035959504003000148110751080b6514020f4034140801a0420000040003d01c0355a8691855440310001e040544210320680300c1d40e190544000030040464096450041c020013129141c02c3c0030f03103081e14070101c450360020900c1c004010001c40080514010b0203506001080010550000400c01303450384003070324410401440100030035600032619000071881c5a03040e0059034094010b9101d2480765600440c3c02040000c0c00045500d6140d01074050342c407088070140140617a041c40c00060b0b94045d151407040303030858450095105546407100b003803a0302c10031b0f00c111100010581c0c80c040791901c032015181a00704070b001740020703c0d025414607800500607070102d0a00c2d0600390010a199034040780100165030000215040790750400c010304c00f64000901c400145a80c0d00160701c40305000c0c100441c0828400d4180821018080c01501d05032001e0317a0b901c58403130361451822009010b6050b06800d2010203840085444518940 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 76909813 1250 76908563 76908569
    0x90d030c030806031b040b120f03070b01150f050d0b0d0b0a0507140906130819150507050a050d09021201061502011107060e0732031c03051302030106 66
    0x40c0c0148901041c01c015021660041070984250040000700780303019000300d01d1603074640b400d80e070000b01003040201082d41e48149148254440c810364030038090481000000709056845448014240d076a40c2070001404145048240d010a0450146c1e40c4060b1240000d4140c8400e40c0c4004548401d00c0c0b00440c0030f10248180540c0c1c2142c2c0f550421140c05e11500901b50002d2583c60495142c10040301402e0303d50040009040c0f054100050009104c556000b40d140039144030070a503262100c00551807000c00182160841d00710000c584141107401d17103485a1449801c0c96102d40f8506982384804803496440f61114054042d5507048880240c2c0303a80c0181049000320070f000240440c200440301c4548040c240c000021607050424455a0b80c01201c1030710b48803540302c000490b42110440703007942003e4164001044081080e031035514034082107200d1000072508601400310040c5442c040c592900e1044c808800d1a0940c0d02003580110311270752149512500c018408020141698006400e40d42294 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 76911063 1250 76909813 76909817
    0xa1203050a05120a021e0c120c010e0102030a0905120f03070309020a0b070506090c030f070b0304080405060d060e070306120f0c121518020a1e09090602030901060b0c07050d0602090d03 81
    0x2003400481084c00c1c8214004071b2a500308842d0a00b00441c1500ba500e40312200480b124050200e5400507000c000d4100c81041c0d015100255204d14105031000c00a040b0701c041600c1500c2401c901c900300515100840c0e45070304105180a103950707540c1c0c0d0107034003600314214101e800503841800050032200d840045c02441c3d1040c8d01900490418145042c0b034452010300e03031171103038212031500528000c000507007000f102d22031030182e81c9a42d5542040f6034640078650110780c100000081c0d10100070a568018810341e84040c038401e4650b11640412000c6485501800541c070703002c0c10100c00031034111411580c2c014884c0c50f841055640b0b41c1c905001c0203400313001c1126040e903800c0818680f0500350207250782850040805c400444119000100d0602d00c42c468220088403e24000492411a0881c480a000100400c0c0807400045c07500d040290300465200d8855468030102107244c607081400c642014070900000e00c68941040100100c0011043c8115142a404c00807681141c47e441c0355260081d0080d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 76912313 1250 76911063 76911067
    0x80307030216081602090f06100e1801060203030405010c080708040201121506110f0303041a0907050306010e0f09070321271502011e0903110a050706030b0a1203050a05120a02 77
    0xe841449032001000d842d01051f601d44074104107254542c80764508800a8510340800640b04200c041b801c035440307400f140e2900709004000440c070550000000d50090307115600801c9905d203207640880d0545000da07202030014107540c01080256120382c113500c8100d007000d13400062500883c20508502011948010085840d01e8074002d02c211040c42641200302d0888003642c5180343c25a182210445200700c0c00990b840c0100110714486020840c4001030039001d0100d07412542c41b2500c0c112112000c0703c051021ba045a00011404000400e400040b20b502030210200d400481d20340034000035624a083c41048401d04844411040001c000b802088415080071070300d0b41021400320010301641175410139603042220420003803600c00c0c0c1d86080c42c0300c116000034100d0b09610301100c542c400c00211071480d1150310825030911002003000000c603982c84d01c0400106413400148054942076124805070061000d20110219005100a104822a9241c21850701080030b81007000400140d40c4c0419140d40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 76913563 1250 76912313 76912357
    0xa171f0f062007030b0415020309010f2406030e0f1f2403020907030e030a02010e06010f0303050d0203100503070308040306110c0d0309020f040c0c11040908030703021608 75
    0x41440e00d00954001410a0312441619446a40355082e04c0000c108180a0300001c3c203000c0c0540c0505628220403900b550b1702e04005040d603020f01003a9091040b40b6242c9944d40b41c401c01d400d900c41101c0c1c00340f40404207040703180000c281c00404416917040c1c40c50141609035807000300d0602020410340002e8000185110f204400f030001c584410141011900070303002d01d042c041036030030318101c2200d078111110f01701507440c400110042c101a60420b2520302c008140807111325019044517444850010484070f460ba65422840e032841d000344405804101c0c1000440490300d002c0c1c00642e031188412102101c2c2590315030201c0d15010496100380c45040c40410180108003e40c02118296441d050a283c102120f040506440c1e8810501284c2415030300c0c0010070454440e41c60504580f00000e104000e2250104c502405036401c06c1812a0505801d0104c2856450144a90070302c143c0c018410a080d5900d000058000b580320f000c007112802c6c142c1500d04001103082d002042c0350400341c0f03040f00d56500307 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 76914813 1250 76913563 76913567
    0x190302060a061401020a062007111003020a05071103010b032401080304050a090507020106090f0605010905090915100506030106030b1e0618060415030905120a171f0f06 74
    0x3041d600868200081943d04000c1c583e4000703212500c00703411100018900c42250002080c8400b00c501d0384002002c08a03803201446045150f42c00341702000d039250040c95100d64030031422480340c0700014012401c01e204d1f080c082800791030200c0c58030340b020380001007811614002914014003042c1c50300d140800d404450401d00b40049080780181413600043d4113007400c0c0400141d40d0503081c01601d8841d0f585400084007940b00f500172400070100030908004005c02141418040d02440c0078150208040301c4000996041403008284601c0c00c000c06060210300c01241e045401c00c01811090005001d510041103594505008500030140c60304c0c00501041c20700c00740180d1032210984840c014440402218054407848210342c03c451000308211140c146103400260140102e400946c3c042c1883c400540301140c0540c84040014080c0c3c3c01c844c0c1c40621201c15024070320a400144000400c820f6003881e000f40550301c1c0b5034004480b1090030002112210042070b003600141e006610b41010700300304220003a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 76916063 1250 76914813 76914821
    0xc0a050d090509070f02010f050403052d180102030f1c0513020a0303050c01020417070e0c070f020d061107061401080304080c0d0606030507060801030c05040203071b05190302060a 79
    0x82918280441218034080000b000050002c1c01c2d0380a0182d02c50b80b81c245c2c24801e521070103002e0002c5808019905180c10020301503084070380b668041a03181010381c2c040c04d2001c2060180c03003008068092500004240380c401c0c0603c10700c0f0040c1544000c0c841866804401000f9041130342040720080c0214020300030140c1a1034000c3c8c0182c01080c1413000440c0941c071107a01c0c2d001601d815013480c540d10b0703410f102030300c0c02441660300c80d5541c40c0500e559485099004260b0030115039001f4000103481d203030b0380340300055441212401030000000e10750f400014200403c240c1031103402004000780d0201d04415064080c0d11401c03003100c00550b690700111140d2100700c009405090700c0b90066040c1402c0003c4543e0b00c5469a500900c54803c8030302142c2004240e8102001542e8424195408156280c4002d40200803e0104543c04245454080303003a040620990784108100d99690841805000078210f02055101050303909015100b40c0b00b41e5950740c0c13800e180040303100740c0c000c1000d480d09011304803c80e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 76917313 1250 76916063 76916083
    0xd1506030b06090d020a12061d0102130e100b0f03090601060503070e0d050a05010207050f010b030c010507030f12020a0c020117070801030201081f06050a0f0c0506150301020d020c0a05 81
    0x105103400c907108901c0d00c1d903009503069424160b07000183d110075030000400b007200030340c41880c010000b9850141003000503001465014410002c0b410300c5905050741ea400c1c1d0040103075401c0703903001459040000b40d155103552a04900d00c0701c1c0f021100b41d207403e10b24481ea400080a0713001d18400200740201960200422401002985012401c60500660042209041a60040c403078142c000d040f80c14003030140a50311056900c88021903444580d8034041d0740360005900c1d203448a510300300202905060105031f1403505681650b980e0318017001c590381a140e010100016a041064011811041a0032031005141d00315141c1c440303203030702d1800e480010029890ba00107080e5244224090150040c0c001c503505042d640d0900302140c2558400e1190440300007001e501691010580c14005a10740d044002045500520b542d44075445080150549100f0344610006050364080d00c001a540041c0020f000c601c15001000940341501e5a0a100d050784c100d10a550000d0704080305900c20400c00304042215 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 76918563 1250 76917313 76917317
    0xe010305060108060409050c040c0e0307170a03050a0c02151801050f0a0c08070c06030c0905060703120e030f031905010806130f02120a0f060c09120f05010b03030d1506 74
    0x41403400e41e00092541c00007404080c0103548510300312040003001c0c01000f1810002800421a100c05400000c0c001e17104504014000d020b005c9011810b8800410501c54046071440109541c4559070340450310b17507210703400460412500d468510010703558541c00106040301c80700c1094860080207200d4040030042c965043c1801000c010141d20072400c10103440c0707111040c1c1041045000340d41030865541c410000001c195280456000c244035405520401020380180e6518507000d489209100b0342e442010400b402040680c4100c801d43c5a080c1c010241c0c04003103070166420800d444c901e0701400d400c00d036010040c82c56800c1c001c0d80e0390344140c4100360050481c440140b01600b040d084541503030704181030140c25048e02ca80080199100c450540c12484c40300401c96881003090304044040101000d01205e5085c28a05802e004a2054410505480385040e58216881a5540d1154a003194005c115815500c90710019966982400645146002c14001045140780e1040c0750304540025040310341 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 76919813 1250 76918563 76918571
    0x60705092b240c090315200c010c0e030a141f05010509090a0b0103030c03090b040306090b060108101205010905120d0606090b0702011206030204050a09050c091302090406020409051005010e0103 85
    0x11283c0c88500b801c1240e0308001c2c0031300340409071b0410308003400e0495403000d5044880c501d11042c0c0560342000704480c441c420000c0007444040c80c012601190701d41c40036a410303840a8010000b05240081300a004c1a4107021035400340a41d40303814a2505c20a403c01701c001344c2d40c9004010b241003048242da88514020081c01c18258241c1d00d0702e102071010b0101904010b82e00d5010300c10940110308204c00303040091a01d54880d50740e80340050103018501000c885400840020441c154041d00516025041403d10140401d052070020b0794040c0b00075200703850542d210b06035940400e80500108088051105003555603d0740810440c0607580c0c00c0d4451410000031180c108240c101e43c0d01641e0100340e092820071754004040031a40f02038441600003a40c02031070320f4144050100300c1d07030001090921440c20b560301803040008101c02a2001c4400c0031000718120042d000528080d4440d40e805486040010308041e21640800100c4008881c00060205420000d00c219070300103940e40e10218091070288 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 76921063 1250 76919813 76919831
    0x8060609060a05160c0306050103050d030b0a050411090925080903040611030c060f070306080a0c05040203070c0f030206061206060d03030b0a091a040e060705092b24 73
    0x2189441921a260b040107000710782496103c0708014808074030390700301e602c110820b6100c1c28a00010402880121010707c80d80541d42c50203070080c0500b0b00820001070090001d1450502488003400c840340c6500c0381c031502081124070035615040c400303000d034400044686a1800300e0105104000d008a54801403101880070011115000812903090303e80516018540c9031501901714590701480f0340d00da074240550800c000c541006040000d2041c095540e00707016030b13981e8145442d1644070718440600710303409818060140781841d40045401580600c0d04041c1c802e15501c84000c0c91610703010840058201c030303051180524291203080b410000c4c4401400450501000080382141c0c003510050601d034907068003000a940e400b0121006210082043c8012110151780c51503141f440f504440c400c500d003103400c103141040010000c0c840c000c3c80d11407d241c212801c08115110000c245030318001d402843ca01051461b0b4980071a520900c14160403007041e08480c032424030340d070000d008203003900e262202038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 76922313 1250 76921063 76921069
    0x4140901180b01050418051b041a032a030607050d050a0b011e03020c0115170f0a1b05060f0a080702010b060a110f03071a0106030902060d020c0a02040c020d08060609 73
    0x2c03e0440310308480014100503011900d000300403c002d009031490042c0d40b0940e26000c50000740d502e0991049a080041c000240581404190b107040259050b60100703a0820742034064080040c004d81044260704545200f550000f860160100c0318000004c0011a55029000f21390158940148504005010310282c000009040311075807080e0003440c0b003070401208155400f0303034103d80c051380302400240048250031501038400000d07032280e00b05000208218800c1003a0200e000ba00c48903082d80680000c1c5800d0b22401010415800000f5840c0d4604500150710381c0e03090002d001400d4036503c05911030740080e0340a068a00000c0800040d64100104902141d444008484c0ca600b0035050510548540c2d00980345444048a05070105120018000c002e00101c0050382428410300311548050360b80b0b40408809854031860b00a4108000740310366126501c0701e80290003891001002c69031001c26540024060f100c0322000e41002d0b0700301e50311100d6040d1b440081c0960120302541c1692a1030810004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 76923563 1250 76922313 76922333
    0x70204020726041d06130c210603030906050d11041d06120c04020d0f0504050a020a06020c01141b0105070503090c0a120b060a08070b12010e040512090a03020414090118 74
    0x144d40e00c0040d507800260b0741e640b54105001078488546c400c100d42c28010501401c1c0c1d0314090f02c010816614050386a2034541640164420f030390f81951200303440b0b40307400e90554460700252502e1100588403000030b041e00c814070000d000104840600030030b202e03860896070000c3c048003401c07503406021644065000c2c0100001e031030040b00c40c141d50040e0786081c4258a0001400d84020380c40400c0c1c01c103814002481000200d001d44035000b282d042c84d02c00d544100a995590300c805499011030004d806801008004030046c100d00c260002ca400c0350404c0038044182103407011501a0042030010003404491002080036840c0700b401030303a5204866082c41441c00b114285d040d8000c103981d503d0400510343c2d031100403c1400600c4080100e825098980c0e8400740760782c01c082d2450380c1004c0c2c1030000050448107071091900494020002d40a020006410300519511102d980f0341c20812000c0000010703150303403150100901d8480c884213910b0500748106400e6a00c01c1e1100c034070b031118042e0500041880045 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 76924813 1250 76923563 76923599
    0x4030512070302210a06090516030b0303250305122802090f06130e010303050702030129010f0908070906090b090f0a0504020312030406050603062505030c07020402072604 75
    0x100822156450480441c05010b25811847e89282003200780407203410ba008400c201c1444a40b000c0c440c94128000381540c03405482d1304102460816400100414030506001d400e441c003074a412454414401d0390740030313041c2042d507000c0901c40d1410700d60107041051000e40000d01240354000d40c40e00841c040002c58000741140d80a10458002412405000d00491108024105910114a50b6a4a05000e02190812a02a0b020394200340c41090103400c4440306903000c6090074202c000d103a801800445008144203610780a001c1c43e02c201050311541004054000c000356500031801605081280c0300352402d0703514550140d4800c8003404209002883c2c003940c08041c881e800a10795841e40000b81c9441c50b1612003500c2c5040c00001d11050000940017144a0035058080300c0850b00c504000111502c5c1d0000c800c10301c850600382d0a02440c0c42500110380003a45200c2450500e1100c0d00094101c1e44120b0085626002c1000d010300c1c45000b05c0c030320a0100401842c941d0900385804600b00092411382 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 76926063 1250 76924813 76924867
    0x70f0807170a0c0e190b011e121a030f15010b070c0b04030317070206010819051f0204170304050307050607061401090e010e030f040509040201140304030512070302 72
    0x15481151000c00002d18815004050484895520b140320112003400765010341d41a11240141c0064110501425200c10810380d1500103181c40c547c00039801078542c1d1820b05c10003000200041000180c3c0c0292080c2d40c80c402c0003104401003210405280c50b05403c40600550000000e894409a4071f000e8581160807100e10130b43d8582c00f92501d603c41001c04d030400380081102103004000c2c160702510702600c80c0c801204884841d202e4540a03a9903110034402e5602980c0000f1241030003a5841003113a8043c0c0c881e400b10394900c948111090344052400716001152640490700b004200c0c190b901c0c101c0c00655040240d4070b442d0509010079110075050094030300480000600c8000c010b520790080d070324208986081203480d40c543c250803000e0304450080925035800c10b0840c0c10450341c04011a4151408003a6940c64a0b10740028040ca244c00248103a050120065000030f5805401d0000c522452090b0f0310696500c20074014600c20440c080e0422082600c140008821414001d0392000340003120307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 76927313 1250 76926063 76926089
    0x1181109040201021f060306060b03040506040305090d021305161b020d0c0b0c0708010b0402090a140604150503011d09060a050901020904060803030a050c09101103070b040b09070f0807 81
    0x282c00181e02e00700026180d00074800c0314441d40710340c500840d07011300c00303980c030955092151642d40d40c1311203124001510060b0043c0c0000d004140024002c900030500c0d01e03005407144045566070303000903203002c66110b80b410384191038904000c110280320094460b08101801c00c4038020210031130300c00f03503401c50400003401001040103450901a011101200810002500b551780380103880070380c0e4944d9080c0c40b07806d160f9820314040d1000340c60f050003680d444500c0500041c03100c81c036107880d00c101d2500c4107801503000b0500700004216244081c0d480300500d002500d07480d569500d0040c1c1039125080e0f00c1309034402000418103100340c403180070441d5074101caa86140400d940d00c804e8031884c028461103210680c86454414001445400800918400d1040c46401c000c0c65480300d4258001c1e2240345151607105034031441030f10803030303008040707100400581608032400e240e03c40c0d650480102c0c080d1400e8521200751001c0121040c810003101d006800082061b41ca11840c0003581e0380d9408c01e0b4091504d01c03100b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 76928563 1250 76927313 76927321
    0x5101e0b060f1603050922110322080c060718050f0603041101030b0901170f0c010c1202030d050406090b0a0e07051002031c0b0910140609040e010e010b010201181109 73
    0x4900c05440010000070712401c0e00355000c41c1100c400382050f07e0030700c5a560070240c40807a0f8100d42010740c0e100703003005d0005080a400300e140181c011800e60000300c4600d1001d0045510488040203218483d0489464003010003412009040c03c051450340440e110b041c045074a01d009490b04401c4d660020303071020246488403031030780c0107034040e014540304260440741c0d840c000a1400e001c1d48100900481c01410766401045125515031a0070070030500300d0104819580d103000080d41844043c0c1110a41d2043d28200800c0d4201c46055030303000e40342500d081c0c1d19111190140a8403460103900481030603c1084048403846071181c540040f4864113100c8c0040f6124000c2907402030080381e6120030001d000782c0e8400c400340034000051206145490043c50248009214a403502118006172000311405410410b41031040060315802586440d030410b84400007000800d81c24001c00000030317404030002c1000c2c5800d0f4002401c46258100d82d05d0040707248090034010500c5a1240b00d1092410307181d00a075648c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 76929813 1250 76928563 76928567
    0xc010509030f010c050a11010515060a0909020a030c0f02030310030b060f0d05030409060503070b1215220c030207020612040807140109020108071e0c05101e0b060f1603 74
    0xc2c0e0304880804075400d010310190b107158800300915202596440300900e9000c141c034000d0880d40110f41000c03000e0b940d001c0840b540d00d465005000b4601480c641203c000303854000700c00690700f05030318010119480e90b2041d18040d411403034060102015100541c21442c1051001070440803500c009019080c01e940445d80300d40b6000000381b04500041d00e00c007441807407450300315a2030340544030b0700410500d08040411796103004100c1d00120b5213885040340c1421802e03003402e2461b032005060851000f83d00c0303000158030744405403441d190300c491920394111064848490010750b50141d203d501014410056000140c0d902e20586a2610f1074521340c403c166034900e070080305032280400103890320400d002e0200c81c1110540102c4c1b0a9031003a0b8070b401981d02d07509000d076480f50301c001405040c4002038542940c41d62140e01d014800b2801901110841a4080c41d14000c4030203400c075640460001100006c40f0761458010781001740301c00d41d680c5280042c144000542401100d45540c102c20740b56070b0540500d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 76931063 1250 76929813 76929823
    0x1406011209020102010b0301090b100509010b030f1005100c03030c030e0304030809030a3003020307080a09050a021f03110a0206040b1308030109020c160305060c07020307030c09060815090c01050903 87
    0x41d01c0900200419803860134032110711542222f03445000c18000030080344500b40301d90414101c079541400c075030a5031540582c000d1107880040440c9509048000c00042c103903500441040e444031207480c4e41180c0e0034076090003000e403058400c12f0028181080059103048400004a500f217070f4001e0319140c0c882d0662030000f410802d44480c003804d41c02d8100d01c100390902e1051a91a201402021050b000010025003901640012070f00c48003ca88601c2c00500c8002207034001030b4a080c403500980d1380c0400c05e940090408a001d0b43d059107030ba001c856104240d02d4240c821045a04511601c4034189a1020350003991244002c000405d9503052070003140c4000065410307203902c1c6278024001e03070300d0b0342e12200030800035048040500c08170301c10441000810042c022900c8180c0f034001020740f9042e40d9400100c1c2e00c6a008000c100d80512820314004003241401925001030280650042500c03403070030711441e1400500450b00b01510300e1981c140300e0140400140bd174910380082c00c050f41c442000100007400d01c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 76932313 1250 76931063 76931081
    0xa0309081201150f030506060306040e1f022104020d06021309020d020904050f13080912060405010b100503240103060510030914030f0d1d190501140601120902010201 73
    0xc560900000c1840308030b03120400081d5030f0a030b0742c140800d000c0600480549805640040e0011400c102080b03071410640c000b0030884040701d0498942104864220026031140340c4a4411140c0c003045034584000005d0501c0281c020300c10082d01f01342003c1c0c0000d2803812000c0d600a107280d0340001e80b481c070742d1940d20090780101001c00e000c41d20b489051905030065070003007460030702c2185402d0001c0d010200191400b40901084601d81400c0100b640c0c64500507405400207562152688803200704c541010400140305d184100300125491542a060003405513032540d00c0402d010041c4200a54051420440025040041d80601c07028072900c00690040460b07421560b003052503071045043c4180c154002001c203602c908110060700e006645016140d024990000b602184200b1103440c2890058004d12070102d41c40513600d51000d05508038525003915100c04030340801c02c00303518205015080c0308011030104504d6901c246450568002001c82c44203440208086039a002a042564400d602460030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 76933563 1250 76932313 76932337
    0x80a0b120303010612060b0a020c0108040615090225051c0903020409060209030709020a2709060e070e09041106031b030702030d0608070503060712090b040b0415110a030908 76
    0x15070f507142c010042c8100c1c10b501000d8182c600344a40001c5031070f0f0302001c40e040340446502070031a00e8108801151806805002030303441c291124150b0040c0500303145224000c00c8075101c0140c2c0c45120581c01c4420015040644808001002184003c280003242c0c90f803100c602550303000110903100801741c1d18200182c20107074205141840c1c21042100c15401019558811412240d0050341d070142c0c8001c1c1e1240030b0807075000450102c2c141e070040d94004410040d81e180e0030449000c054440e0b108004443d0264481d000c0f400c200c1303080c8896a5000f0f48540c5408006031629011464030b41c5501070388404101409008075000800038002c04100d01d50350369240820040160f0328108010001d40c0e03134001e010300da469a460000e0009401100107038030000c0751809005060542e5641c10103440000e8103102e00d1800702d40f241c44031800104030300052403103a4440c0c140c51007d4242743c20007450807407138814844500c034078055000301555034070380c15203207042c0491801082c1400e103403401e104540126208848 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 76934813 1250 76933563 76933567
    0x41e060203061806030706031805011b0801090203012103050c0f0106060e060c1915050c18030a030207090b06130308040302012c240307080103020901090c080a0b1203 73
    0x108004240c0c00030342c090881240c1c4010900455540c4086002003920ba41da8180d10040b41000100d0203a0424034165815001410b152a031644502d429030b50340171140340014180181100e20150003003440c0d4058504803c00b1421036041081c1100c070710340d0f4011140c2183c4002c000203c10184038500325072400d81008140d8440e0703800c03140710a0203806180605004913030b14034081501d42c28404142d8003203482d4400180312610340c50b27024100c3c5d00000d5400b178988910031000901618450f01841c1d0081d940707098100d654612442101844030301780105e0074829041b4410030000309500140308000e0f0350f49100c1c0001c414a4000010b6241c0c8291100d081c0e0140032080f000080c408141d01601c1101e000fa00e0f11181401000e80d03010602000404152026021800c3d11225003415441d1208514440d101c4c0703201059088880c05540d00200c914000180000d001401141442c03c1c03503500400340007009210300c076918600a000842c0080401d843c481d616000046560784d26801206050100c0061302c1d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 76936063 1250 76934813 76934873
    0x103171c0e06070806010c0302300a0203300402010e0a1809020301110304020307031e14010b012003040e04050733020c010903020402070311030a0c02011805060405060304 75
    0xc1d00d0326411200c800211302554006501075000f41001c40c251a8541d002d0308031080d0960201c03050402d0001003c50b07041e083c0489081e0f02c000e5500821080d8030340d400454072964030601030300040451800c080c510039410050110003202035503015401c01d5090070001040c8401c0d4020803211202d076400700c3c03415404010340840b0a0b0299101031102030003513000303000001c02c400c0c488c0a80d01c02540e000790546e110380810004039105002e0502c942c0e90400c0b0011000c415900c1c0c1e0340340c412201301440700a0359100c81c6042d656800c0b5200408820300c0322401d49105841851076602ea008078030400007070000e11000902048014030102c000341c0340a1901e803080344010044800b07266102014031160002480d0307586030441c000620815001c005a41d035060300c90450b424000650070110044040c852251340e035100100051000e4040c407002581c3d00220802e007800018000c5c215040c518500c4036a031482800140c0b545412501a10401c3c1c5080350703251502e00e0403460170f059002002c2040c1500c00065 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 76937313 1250 76936063 76936091
    0x1809021b0106150e0a0b0405100c020904030e030c0108010e070302090f060f12010e01081b030f1c1404051c080d0f020310060807020c091503070b04080111030103171c 73
    0x3824441550746034040804104203005c44907455000326100384100b400100907501d0500c100514039a01e0703141c07d18001c45254045180c401d000d030b600702c001c12280c60302d60801d420104444640e0390000d180c00240c551410403030000350749000c0c002c0010950006840300090720795801142e40c03174002504c625943e9805480368071454012441c0802125442000041c7e804000f0600d1416525803030054035441e81c1a0204413190613681c0b031095090301401080100c4004144002e4600710744200305020800c840440c01811081c3d01148600030704c1c0144410301540c0c0b520100318044201400b01c40140c0801c0c0c1c181900039000c1d01400c00d502c00d0a020501d00601c841781c002c1c1d80910600c00300e00704996150314017031310080411148a40140d0042800800c0c03490600f40b078a030403102c0b00039114414881940440c2c00e0030455041041030312000a020440c2d480309208984807841c510b90b0103810b44d41155201c028000c089440020040c1c0702003007408100c403151032203408020398280b003003040305016511b13 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 76938563 1250 76937313 76937339
    0x6010e10050c070e0a0501050303180904060b04021305040e0703030801050f041b03020711040c0512040c05040608010504050f0a030909020708190e010807050f040e0411040c0203030a0c1809021b0106 87
    0x17510b680ea5040100008241c00d002040d04d500e0078490b02e00200710f5545506020300200010020b483c0b0310b072034444d6a100d41c0c45500c01000417a4a01c26540b440074202000d010640342075945048003a40401030810109a0100b180750640c0c20444010290189510019001d000d188924130400103034000701c0c03041c031501540100f1311507200741c0241134007c40341d4040108443d2100070a40204e44200805007018070182e94070b66100f403042d010ba0702c0003078840c804601201d03519000f141c41a1344d11420701c824410100316141d094043c600081c00d002d03007540d900400c000440c0c444c00300116008150117080042a07806e98405915084203104660400386000340001c482c20b040380c1c041203058000c02d203100d101d18221180c00042c4007880740351174034105141d540710304018803d54000004051103690741e40c1b5070062800010103035005688900b0010900002c03500711f10403000c00e0020050442e204860080f81e802c044a42405c00103860f000b1000d6008902611031521151030351800101084119030020303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 76939813 1250 76938563 76938571
    0x602130e0403120204030320011d0106170102030c04051c050610030b07080f011809120302190507051506042a021624020a0f05060703110306010e10050c070e 69
    0x41e441080c000503c3c2d032041284603501002c1c002500085240c0d11341000d0903d441c054a40740b00c000940c0341d070b4501e146551117409100c40390840c3d4448000300011821070044001c036850550085282d41030060040075244074521496000700c400c00c103d0b5400e0710300301d03c4402500c0c3d000400e030703001440c289907041c0f281c2446000844e8000c00e030f040030a80345e91040708160311078807035104031402ca82d08114881589080344036115143c0c507140c0503417000041c120100c1c900000b1640c0c402607150824110924041c4000c40c543d0b40c20042d09004090115800050300c880380104211f51109984644000c503019240e2050a500d21000c0c402ca03405c4010100c0c0a44204036640c2e5007541c4410b5843c0203d455159004e12600245100404020345089105858404841140d004035080c061480c4d0701e514440042240507100782d0400003c01c05890f416002d29106070f01c6016000346189091000a012410301880707141c02485102c00e64401a030040d03048a0200501e00d00300c4404544c2c41080a010030303c100c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 76941063 1250 76939813 76939817
    0x1103250c0e16050a09060806030a1406010501090501081e15030a030c020301060501090506040314191203050106090b1b0705030a06020304020f01050702060f090118090510050108010515070602130e0403 88
    0x500c900118801c409865811804e961099041440c00400302c0c1c405001814081c2d040c00703030003001400110400403c54040c0f515a000e40304a41c5800c00141000d00d26030300280c10310403da802c12642c2045080b040325860080a00500e0648801c58203a401c01c8000242c0d580500c541031524081c0764000f51461910340c802c50081c0240c40c2c60701e004507030184c1c80d8418150804400d01c0180005000a005010034050751000c031254070100d040340c0b00e84071a81c00016070701d0120220a00c00920381c50300440380500550f041100a0610b08400c85a0324414020583e03c104d841c060116900f106c00d000c4003008110003411212032000314100b131030003503109442c00c901c03c80151032440c80f01d50003001610b01040d0003c12150600c0d605880d15150f80d4081d1a84c030b8100080c04290446400b00404030f00040c0204440008261401580e0001c078060700b90000d0381805080340c0104150b550b0380856222803180d04071003503110f007140c7c54000064052802811000c0c0074803c00807406800514220f8403c900036 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 76942313 1250 76941063 76941091
    0x605062109010216060906020903010603030807020105010603020f070305090a0510050d0b0a0501200c030d090e090c0f0d0213090501021e070503030703050403020a060603140d1103250c0e 82
    0x80c0021030b00301e1145440c03282d601148411038501040300303584060640f40c0240c00152802d00c041c800a421110381e9003040707000c1080f0b08280840554244200c9002d801d040c1801c42c0b40800703558a01c2650301580c540207003042400100328a4030380b1402c0c030600052002400c051103940c41001c0240154001d4105020740c20b01d0030254a050b80f60407440d0380c1c21a04182c590080d00c1c2500c1c00081c405c0304552564000611415034000501e840402c01c5040e8100b0341e6980d80c3e80360341060ba150410a0010f042408140d012a48040315036940c4042418180c80440d45c5009082203803001c100f0030230f500303000300240c00c0c50658003000380101034005242001080b0a20440c0400d0711400c2c00b514000e800018059601c180300140850b80640d010740e03006402401212041400c90362000c4c00d580782900b08488034950401d1090039140b0400c601c07048520b0f10b0800c000b034140d8885885a49000c0c540325103080c2003104159070944804141070590b6a80c10010006450703031106199108400142c5070b0040d80012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 76943563 1250 76942313 76942321
    0x9040b03010b10030e070e15040b030d12020d0e06010801060e130c120206190207080f030a0c0b0601030b120a0201170402030618190c0305060105010206100902070606050621 76
    0x610842c05190401010310072030080d420b00403802070941001c030490304d2151200100c2c0c0c554480888500c5060010072007402c0304800014030056a200010280c000d911120810741d0035504500a400c0080c0b44050050711160820311600203460040220400c900881e8000702d080e4006401c40e4007038030020103a281d0552110041c0c0c442401821101802880c002d075014420011100e2130411041e000510280c1480d0b000c0040c9071f001040b944411001d40d0081e1010880ea21050041060012100d80030314145500307504068134201d4001c41c001c08050501d00003400580c0a507005415016014007840e1442d40d0f45501c155444040340030680c045192109007642900718034020324070456015015080c551640c1011403030700781c3c0c5080120000d0194480010b52545e0305c8402c1c540c800e0251034040b10b400d00d9810100d0511a060704041d04640040b42001402406030300740c40e00715103401d40300599584940c113040c030051803103400c46540031000180c9800b10000c00e00c3d035008060180c85218a40b0b4071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 76944813 1250 76943563 76943569
    0x60303090e070906050403080c03090a0b090906040612020f030f030301030b040b0f01030c03320106030b010b090916020705060f09120c15130506040303051209150c22060509040b 78
    0x81140f25120000320104003c0c0700244000000c0c003009d404c00c0040380d007000181c40004085c81c1c080d801c00e8441041c08036004c5880d01c0e2504000d03410440a43d402c021090505001c1c0754400c1d11140d001c1e002d4400308a40d410161402c00404003d002c1e030505403900d03942c591500d0028124152019102c030003160020941580d42000c05034101c0e640900301c881160b10b0b50369044400e504904450b250a01c8500da14460800c000165586034801070f40005413040c11440c20750880702c41a0003081018800b4050000070f92600100307180c024014690860041f44400782c124502019034000c50b4000c000030a120484005c41d01c0601244482111000c1e07190402848041d9103504100300203034026a14100620500000300080c9840b0805201c2c002801751a0170101d1b8403580940c3c41203000410016240109910320b4040b1500080e259001c2d0454003204610031461140c05402c80d0840680000d00202205141e2012001c1000404a592101d0f68030b41020b1b050307070420101d240c051410080e287c00035103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 76946063 1250 76944813 76944827
    0x8040902090306071707030c0203120a1d060c430201030606050a0212030a0b1c03020d170103060b061204050a0302060105181b09150304060f060b0304060509030d060303090e07 77
    0x130170004000d2401d0385e140b8000700c003d00714080c0340d501503010070800c14482440503c441071007415600703004205d0040e290344100502e10100000c241ea5005a0140000401c0f100219128500350848400d514481120703800c059144c4c61141c00404018102c107201500b01124452018034000d8a08012584d0b9540041c0d4042c81007241203801a003100610340401d078048005140c2222007907000081d03c004010102c0c1c01c1c20641c0d20031030031203841a00b484e001c040e0304201c45000390100c1d18102d11000100c1855881c0e80d80c2c180801480c0540b109140081501c9500c05e6034203020440d590b41000c1d06041c1080c913140c5a8040c8154014001c007000411a42401c164440000043c0003491065907a03004e141450040d40d14440b1000380307070800c004080c90750f4004062501984007054180e90382400d1a1440840320710113038282c202802d10108000d010307280400d40e94419000b0b1000b00c2c1f01d580c0c0300c0d601402c52007003150310a8481c0c5464800b00c00d065000c900c1c3c200340c6903c82d5003151161108407040d03a0003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 76947313 1250 76946063 76946087
    0x10c03050403120c030e070602010e1b0114180913051225020d020d0b0a0b0f060301050f04060e01080706031118240a0807020d090810020c03070804090209030607 71
    0x120b01c14203c40300708041c16500c490089801d5140000311800390080041c01d10b0560340c80b02c0f0040c1c1d1030340c000402502003404040001205c034015452540c24500002e09151031403001005464004500907403401c00038100b003500b03e64000c0c403046541c500990344050f91040c4d003405568500c540640e61402e4800f99080b04e2010301c801100c040300340d1043c5182220520007480032a003000d00c0c031a400c4010380703402549040e030b288035480310a042d10703007c1443c0b07045070300c40c1d20114800c0808500e0f5a055440e0042202e0540c0c00554034018803495000106010300703460307070050030038000e0100001a6030802080d030a058a4055600380300c9540c9088506201d40100f000a820602c14001400140c0c5844002d0144424181c1500c4420719000040348502e6000302084401080d24a81001784255043c0a045203600007824242007403030901103a56070783c80c910001c010303d950340010a95290701c420400d50300410361003802c1c80d40e0782d1b4403414a01c000c0d400204c81c407030003489141c010a90050180c40c440f885 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 76948563 1250 76947313 76947317
    0xc170a0903081b090405040f0317040f030503090a0f03050406120b030c0603070c1b030309080d0210020d020d020309010f050c070506070f0507060c0e09100803040519050a060e03010c03050403 84
    0x10079100d0720210303101d070011007000c0601c0744810003050394035460300d0141c6d610643c05295005000265420042c02103889049a023210000b10820000020303101d10103000b19070b0705032505903101c3da94004030514040803010040c09210040300d85c5070825034444003e00030741d1500c0c1d03110101d105050810100351040c0c42d006540c160080540e042c0c642c141400034581c00b816a1510b000e100e540c03a16010f0000b0100d040040d4107666001041c418142c03c60440c8001f0704600009128040542100a44034000201280440740d00020400c140003043d4056901c0441080011175890528800040c02800700c040c405407005d04200000e8003404191054807842c82d04070002d800c0d155258442200c58451000c03c10052010900040020409611401e010110b9589511108140060401c03019040040203000408031840742440411004016241224015520144d6000c40a044000c6c8052241c00081d00603015090005a81380d00c05a015480d020550081140f80e4034000d0032415204100d0300540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 76949813 1250 76948563 76948577
    0x501060807050d0f060222050102060c0a0512041112010506091501020615041509020304050115150507050709050c030412020a0b06010e0f030105090a0308090106030314030a020408010c170a0903 85
    0x4544141340618840c0d10404005140000f801030550301d080a90083c003e965210002c03d00070765804014a9810400c1c140d00d56003004c0b1104001492817042c0310196611b41683d0000c1800c000310041000c82e5802d00070010300803281c0c5112464001c0100312021032240307203003102141003090f542c1100c44040b030701a0302900f03455a8101d81c1500402a4017142600950b903050b000100032140d15101020380110000540d0300d01302410540c0c2581d00c01030001c10341d04505141000f000340c01c0e4406043d0041d16061068481502d030911a040c43c62b650700c4624a142042c0c02c100d81640807a0045104500c5600c50701c0608610b00003c80c0d8407100e10170011704488509021070025806032038003800c0d0010041603001c8660b11000880c2c09d5410564003111250300c019145000c0581140c0c2c0c896000105400800c44149142c41c01003102048080c800082d0034000b002c1365055130300380c044a0280c021540280a0100b0342c910003003000380b4004409610009030004501c1100d00740c000c01d00300030b0b05076503255 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 76951063 1250 76949813 76949839
    0xb040602031b0a050304090509011505130f09050105070905030715021203090a1403090a080a02130c0513030b0f070216050f030f0105010f0f0602060915071407060603050106080705 79
    0x40711824449405900b644190449040090700420083c000390031040d0380031801d41006900e4a00f50341e81040c101c6090b03d2522018061620b502501d210307900702d04040031030380d061040903200050502007000360540d42001d003080000d81e0003d2229044640036411585015503900692940e0780060101c000181c00c03103003420b01426243c030081c1d80c001c244402903410004880d641c00e010b9207c0100039140c40e4202003100d50381c0b4603008044500903d0702c10040d1041903100c0d800200134049100400c0f1020303035100640c10415102e801a9640d440912042d00501d54403400d0030514032a0449200501c0c0c4006800950906d1000c50410322603450204215130b42c504241c100604014850001d98040c890501c1c0c8840c0601d0901840b8020000c03068030101840c103180b1104110b064903001041554800381c14000c44960024101140700b8070302255803100d4035a110708a0303d07400180e0540e100000d001c22a1001d2014a6100700103d9120744000c00916a680d006192500000e21030591300407180480c0c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 76952313 1250 76951063 76951087
    0x7030905041d030705011a0121050705090306070507150606020c0d080d0c050310050406060f050d02040e04050f0f0c030d051b010c170709031e02030715020f0105010b04060203 77
    0x20140c45142000742c41c1600200c0052646107422101c1d0a9501c2d070b454400440803504406082d04d405034083c0790070f40a00d28240c82e400c001d58441d0460300500b959500009003514410740503944040f000900703607601c03404c101c8001400c40d00a0703481591454440071090400b0079580c4204821120b4940150034104066002c0021a0004c00c20540e0007034010000305103441d0f03047c850403069910a450b5542c9a0500181030040550b25130402d034015881d0800500100d034004040070200042d51815594440440c480d0901a020f181e00819480100b402444200702c40400c9402c02c400c03440e0110785240d544881480c1d0f4400842e00440c0d05a08844100750701e8600c07402c0248800c2555080e020f103031481e45130006084030402491000002e9216201c5e0500a40c10366816812045910f0100307995800e40d201d2703400310482900030540114107a450402103403400d0114500801000348004814851070002945880c070103050036030390303529100000c5104a4000300380da040e100316500441c103150781c51104c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 76953563 1250 76952313 76952321
    0x1404020f0907030f020a020703170403080912070305030f09040f060e0109020c030405090103120207080c06030a0218040606030509281407080703031701060203160b0a09020402040305010209010e060703090504 91
    0x641003540703aa04d5421000b0490005203c1c50403150300403c2c4851170742c14850405a41090b060290000400c41080030402c01030682c0c441c2d010447d4101c0d006051a442c05251500030385c0010b00600004c40d505001003040b1018040480d0255002d2009400e104080c01c100c554500400003200d40800c010711002c0030a03409040910280d108492070141c6880016180c0c0800343d2044550201504d0040c2d0550303814800340d4002c18401000300400c5d00c0050003c2e00da40402099220f1507540800e00e0f092203812080000c40c070441c0904104411a1505c2d0002c1c0580000c9440300001d2051541c180c40060038901204150302480b1100d40810310295510020454100c1c0e00c0d003110b100740341c0c02103154001480140010340c03203500c51075850300262110306c0314900168407036019034000744076407984203454102c00081c0c0d54cc4164908050ba80e0203100c100100759422010707420504c08500481000720560081080030f07402d8803881399811000d420001d4a1140520080010300f4000003003020382000d400c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 76954813 1250 76953563 76953571
    0xf14150a030605120102090102190317041712060102011a0105040e040807150b040c080105100f050f0a0e190605070b040807020904060504030801080f120c0c061204061404020f09 78
    0x19010501c90f658000081c1c4940d01a491000d25950001e40f0002542c1c040200b00078901800c01040009801030310003400003034075500304182c0c607000d44000500f00710b80940c892130342c08190003207262204800b004000c1d590100f01c0c1c0042c055842e0400c0c20b2803e84203c9100c036041d40051707540c01c0ca8282010300303407000e2180c082c000f220080014040c0c000010a000d00f410180c00c607401c4001450583d080c100826514204914030522500c0801484181c4505d003408001d0442d40c108040100c456410031030707040c42a41903103001e0074400b1032030030b12240e408000654045400c40b5611602280066051410b243c48e2050a0100f401000000d00040c0c1605040ba40a8001e28440c0d0520f07041e500484c4c0d07201d1044401315201540c40d001c03c01019082680c480c058a03120004000c150750107140076030346541c3c2d10f250620790403003c150505081001c00ca10103940c0c2c800342c00f45488240d00410b002d92010155422190141840010b071044426545107503c1650005e054900d0304140005108172008068 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 76956063 1250 76954813 76954817
    0x71505070203120c030711090f0a1814150109020c030301060c0302070306050f0108010c0206011a0c010b0a0303030617010903090306022d04150c020604031e1205040f14150a 76
    0x3030b0f10702802e00118400381101856100246940b80b40a20b4260492201183e00a2280d0b098001b4481c4615104902d03540c00801e100001a0124030000040d1801145100c018005071182000c4509034401140007185110a00c80c04c0c1042c0c0d0300e076907914040e0300440320101501e901c140300404c0380610540d0300c211000d0190060b10a00c9032240c6440044c0d51045070b9440460760034100400248000340306001c000300030751000d08100c3d41411406600070f141c880192a800001003160100481c080d4000100741400411114040c0e030380c1d11300a40a041a0b02c500700300c3c4940140c64450401c411b010b80c030300b62035269440d110034034190b0356920002d41200b19002000c500c20b01c800000c06016012495000107138203400340d01c0320300d4041c40003101615204000c04001c0d43d4540a401a112902914141d076800091440c8024a80e0801d401c10481404094502d1200d442c018040c650428018000d6403240921020b05585a50b0740c05030040c8261882a00102107004a0750b8001b03500000c1d141d603c2642c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 76957313 1250 76956063 76956073
    0x30b09091c090819300f050705150c09030109061a09010b070303051504090c030b010609050112051506070606030512030c18010e0604030b01141c082203050a02030609071505070203 79
    0x1010902c228240c2401e000140c1d0554517840740d031160400c1c50000c0c048054600b06252805035550241c850007104035015003101103201003440d01d8112000e80710611000f400800031131840d41800c0000d48201a8208040541c00d1240001030401c00807090607100d60840c0715150a00903501100180f500500c3e1400c00103150b90703040140c0e5500c2c02210b1030b01e40140c144960003811414450b40d00c0c02d06902403010300000500800146e608045000140303000c0c000001403590303c81c1d0181c0ca6071101031801603441000028400b00b04000c0d641304005490041d4211003400444a07c0c4405070701c130a580d001d480030020b006d001c40b505409840030402c0c503010714004a0340c1c41c02001144680c0c101c0c1e04200c0d0503400500040c05500c0c1c0d203a41c40d90031001c0490b44183c103140e000c002e60007178424011000c2e1400301c1c002054242c1c030f1b43c004c0e13490b0b003808940c40c921151980da80c10229101c0c649024202e01c00e00458002c10f1140800169a5060b200002e484005c020741c0c032041501c1561103581c08a03050700031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 76958563 1250 76957313 76957343
    0x1906050d060e040803090d0905010903021201090f0317070f0e06031b030a0906050a02210411060d0f2d0c0909060305030c0607031a0d03030b09091c090819 68
    0x240580c15070195214001c04c6441c0d08100e030301075003030003000504401002085071080210f40e90010300e41c01229015610495809044400180548909070000c0c1030510300151309020180d105c1c0351a24080505038009255450f450011250f010090280300002a90200400741d0352405100464000da8040ca150710600400c9125001a8104890f6140c4d0150350f40c1500b42840454002c1650140c0356507011460105c10000d0740b040158102d051411607145440003608102e490030b07404078100401401903031a04540200c110140c1100c8a00d40a81810b022001c00c12111100341c51091034002d0240700784a8038503c194400402da403280300e0080020510000070714032224401c0310080d5001d400036603582d00c43c640500e4903182d005860348003014a00004022000b040c041001d000d88000c54003807207800c0c007508041300500780c8003080c03561250a250501140c600000b41c040811034080120100301c0d080500140d0b400111842024401d8006010380c250b1400202502041035105485040260304 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 76959813 1250 76958563 76958579
    0x1209040216080a032301151701121104020a09030b090109020409050d08070f0203040306050601050d0f050702011107050601030b0405030708040e15060a0509090702010608030703090f051906050d06 86
    0x401e0050342e00c0040001c05141050703050040c00740c0d18070700c411080c004514510b005690f1035014070445050340c403000003800640d4420301c6080780110000d10b2400042d41c50b04c2030040801c60400048440600c5003020b0415400c042c000d0f111910007948510404c0c074995281c401d41801c001f00000d050f5540c4521510051b55944648402c01c1d0180004100900781d00001404038080074150b4810f02001c800301c410945e45c000200e0b01a02d51190b008101c4e5200e05005980740d00803952030081d03860510040040c0300090f58401c41c0310350b903554000d204c01100b01044802921540304040c015401580041c0003080343d000f01d0540042c81242140d142425540341c1124540080d0042c490342d041000500a4440550880f95002081212440d00d4030381c0307440c40640301e8460f45c0b4036640903914550006040300d0003035000e00020701e9140107030b90f5149064a0000c181d0131140c000c581030000c10001c089854100104c020103005d00300d02c4000c11007428150142c40d00d4003c20075000c4082d480e07030400b01d0200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 76961063 1250 76959813 76959847
    0x316020f011109040501060804120c050a0b01060815010e01052b09050304140f06030a09050c0306010b040603050901020a0504211a040629060d0207051606120504020312090402 77
    0x1040d0074a0301c80e10f0f40c8502040109442040e80550100041d1905000c042010040c0c010518421424884030b10701035483c0c0036003415240030010b8803e0f54060000901c2c60b4105543c14451000d414484241c40000c100540c0c134214045182c170700090040c003180048181d5002d0507580000100800c0342c0035114011403400303641c00080b017203030b03182c00116007048010121b0b11000600c46084a4003e030310404900403401c90302000b003648907440d1b21441c440c0144201400b50740180000502560019038440d00465041d45c8144560b04c0000e141c103001542004040c425101c01d442d0340d82c0c59519161500c110150b02c180400c4142003845134041410000620b1281c0c582607000b2407014008551416003003100803a500c44182124119681c0d0010440700e55191380b0800428044a03441e03127818141072448024001c2060007000b41c0b00d8002c82c40e40741c102c000c44080c00c49119031b4651590340b05004000f802d641d0255002900360780403c00c0c1440c080c1a14001d0030020318041c000509010801900105c05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 76962313 1250 76961063 76961081
    0x61b010e0d020601080106120f060b090c0c0705013e010c0201050a05010b030f0105061b0106080115120b0112020f030a06050406110c03030a02030403021e0c0a060e060316020f01 78
    0x1e0748400012801c1c0798040c00703076a00404002000700a42440d00100d414035204000005220340e003a03072454020000c141d88a201b1403903000c3c0959410349400079000c600e9500c46000e800c4144070b40e6030009115032003950540c003c4000c07240d695800d00da414003941c007045e4100045c0d034060714500c000b5409a076024130803114000043e80c001300d41424004081c0c03084a4040c1c0280351001d0040041000303c1428000307190441c0c109039503041d076442140c0703000c0507001407041d4400825401d00000144118054101c02d11810020042407851130350307160700b03034404070580d00300900a803c00001081100c40d07030114401c071180003030404950781406800103403c01445582c2110703880d950780c0a100500900d446084040e03407956202c85d160140c906181503490000902140540da000000902050720901591030740c0800003083e0000102410080c5450341d00354031405011b005800390000d02944603020401000102600c618550780740e0350710074464a08950884029031041d004c070300082c00b10900c41c0f00b40d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 76963563 1250 76962313 76962341
    0x80c0a0503120a0f18030e0102070506040f0302030c010f12090302030706050c03090c030304050d0605060d0203010603080307030c03050106080f06010c1e02031011040509040510060308070b16050306061b01 90
    0x62030b03c4440c507011a6001000205520700e0700c1c41107030341100b8007800006069010b0811807070094403200100d2903c602900b00a800c03200201d03000a42c9603800201000356442207081d00c0031070314160011150169189002030005d01d10724200c4008800c264001c800d802c3c040c1c0705882c1b0741001c9490780800d95070140d4840c0e0300e815002081002c4010140007040680400710090340c5003500d0100043c001c4400d07a400609030b150b42d00c010448542d1041550003078a54042c0003813101070794074140340003140c00c122a01030220381001d0301c54801b2072007842010305964850b11110b0003905d4800303841d2010035008001505100003044240041400d64100d044800d00c48a4078070741c0401c15105060031b00e1014103944030018101080d00d482840d41c40240d80a584090b285285595554140146400c1c14040030401e0145080d00100a000390640103042c024090141c0c1c00c03440e19000442c240083c41c88074510009401400421418900880209861030030040280e042030004000542141c1d10070780c1d10702c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 76964813 1250 76963563 76963597
    0xf0c0a1e15050a0f111f0207051212070c080a030f14010e10060212043303020403020117100501110c041b170f0a090204060e0a15170307080c0a0503 65
    0xf002903408080d26004050f40c2c642004d280b5115035005aa0f000c021070054102c280004455000c1342013541a030708010342210031540c40f40040c401e0b81d41c0303960020318501c1c0828020030010b07681324055441e000c602c0d0341c02885117141c54100754003140208031880120140d29110f8a0110100461101150182c078506a90700d140c1c1c00d0061000c99580910380c445015904001c0b041741d2283c181030306440442d415100040220b4052503101e580c4c00c0344072070b801081036840c0b64001808540c5980500103403403003a07c5550000505d0452420004402c8826845150a49c1418055035104140305048011390b80125954991001e00140940d1994010f24586840042c1c5813010a42c1c807000d01c015900c861400444103091010070000c0c4600014088a00307562100c64901c210340341c03548240010300c0015002d0651f42000d40701c040141c00b461a07200c070406051700001c18890100780703102840c0720001d030042d85072600541e6414215041035800c50000c0c01968410404118280300030720078009000c10600b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 76966063 1250 76964813 76964827
    0x80604020913050609130209150307030c030c06021b030a170d020f120a020313031412090d030606020102040807180905060405031309090b060915030d0c0201020f0c0a1e1505 76
    0x800e00d20000c214a281b41070701000d09016031104c01140343c102e001d1982c0c08244458800100786440d0f41c0341d00080040c200e10100100b8403040301246400c0e5202e684c01d44144071840c0c09648002031840480550513084022100b0000b24100c00402074404000202030518200c40c2002c2c0498110b00f1414012141c00503100001d19241d02d400c581c890440101141541080d028485038908400300040c2882910702c4400c00e8141c641003030f20a0b00b0840d00c04003070145800d050312615400b03c1036032440840e0501e900030808c40e0060007a1800d40b00c0020040200c84d2400701e02010381d024211850a10344d50311400100071074400d010709071266024500840c1d803280c0c2010f215604d030101c0e0f4407200d1483c0c50091003000281e40c2c0384119401440c100d4804400351181e148241e001c1042450660b4180b055040e0740a006800c0b5100c1d101c8039000740c090301c543c4101c2421950703c824191184030f80c0043d10035000e124a4015042c0c0d420a061800c80010302c0703a0300c51614642400761460001c0110340301203004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 76967313 1250 76966063 76966069
    0x108012304062612032a12011d060904080a030b01120c05031b04051806040f0509070807140d08130803070803010f08150f07021f020301150206040f030806040209130506 74
    0x1100038a5003802546140b6211904986e401c9581e40c1100c0d0050b40e0b1580601b00114000660b0101c1180f10510869540d4030001c803210080041d509101030300c07482000501d03070310b8031500c000c0c0302c3c13070708800301070b1400c035010b0130460041001d030b41c40c42e052001e001040c50f0001030741d01c41c10701c10060741d0702c441d82d80b8140b0081420755a07002c8001d1900d0391804204c14070960b145c6080e001109000c24500310030b00d45a0070001406010042000340009281c041005120700300002c0800c00c40300c040042e078400e16211412906c041440c442c9032500007101002d1000085c1590009001c400c0e05d65049901c5651540d41d00b5085074884242903d10007030210041c419400c092003160010a000001000e415001070a10040008024640d841000707603880000c0c603807402440520901d03c40e10410f109104584503014000390820300078520703281c4101d480300c0c4200f4000a00c09010b240c01c1503070002180103503a81207403103d0000b8851604507030280050002d648800c442081008140e540101d081c2ca856014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 76968563 1250 76967313 76967323
    0x1c050313050a050d330504050c01030507020f150405031c0c0e09011202010e0310020a0201020d0501090504150f2901030b06130b07020607020d080c01060501080123040626 75
    0x4500e11400544c0000b800081c64030f000150703201c400d00030701d5206604616002d0740c12400d040b5500e00c107908000801080110108841c6c80710300c001d8034100540e465040c800ca079030788402084c1c40c4180c0d1140303001c0010b0f0b202d01b408003035000b84a1011030740783c000713042504404040c00740101400c19850b14034a5407010b80003680b6107480302e015140203030150b25083d00448640705100000c0d0502442500d84900394800384625054404814415503862014060090007580410008c2c2c1803249840004100031189000305030240303410880022602c42c0341e2017a200100050040010596991045600760104004542c5840c1c51340900003194104104005000e891410600f10312600c810031802e41110284c405400c151120420401e494001520126215104481c4040c0d4020340085109040110390001010001c420f60000d2200650310f000540340481c0a010300d0058010214145c05100ba221640c40030340300d0010300c08144540d40c0c6100004600c00004840403055a51041c0342d100e16003001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 76969813 1250 76968563 76968569
    0x8070303120c0806010e03070b0301080a0606090e060c0d06090c05040303080a06060206010902090d08033103080a2d020c1902151c02031302130903020601051c050313050a 75
    0x8000d201009101d54003c2c40c040c0001c4c245414070031034001403040d545041080c14040d202e002020355a958461076425034400321000c08840c01410000c000c954130b4003078044d915613260440c1c010310780398840700032a18094002050203299595120310000304107400b40511058240346071185561a41141030003041400010406498203082440030840e41da0300151603411111801c50041c0c980454400049140c0d100041c090f10311600031042c440500c6c0300112201d607454011a04a607045085503110f40340800b420000780100c3d80d504009070101c0c1c03598000500c00500c10383ca80c101285010411515105034031840c2c90101c3e404203500010003400c001801d004c1d103042e4200e100c040c0c0550b0004184c0b42c010324241d00c50110106e0018101750a600c10540c0301c040407001952246814461010100070b10b000c01e0b4481c0c50881c240c803400c21741e0307403040b10543d80c0c160340a40300030f80c200000e000c440140148196060002141100041001072000d0408041621000d60390140703480100400120590 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 76971063 1250 76969813 76969847
    0x18050303101505030f0414070b0301090518190b040c050315090c040b210f03030106020a030e0a030308060f01050910020105060f0a12060f090c0303050306030105010b040b0d11070c08070303 83
    0x512600b050507010495000b51f000b140c0301c1003140c0c1c0c000800d040840d140d01c242d45110003c000441c0c444403980142e48914401c58040c09040c8014074010f0b030b1035174079a0281c1c0e810017018001c1c01c085138500f041598000d00075907141105907a5600480e10700344200c00c4d183c200c11004014044469002c0c441c495219500320350134001c00502034006400b4010b034500300c10035082c6115010a40010602c0300f51600380f11081500c2e04c075a5a002c01035200c50000808800203004c0d00250300d0b00c0c2c58007199010a4075059500c1c4403031076642c602132010f802c000001d400d040c410184150f04455852848400e008030003035001040382c0c2040401d02c40005400d4013254440c529081e41480f48160f504001400550840c1c8046480c030342d44072804d0018107196001502141c440031012061641042c01503014ad10140c00800860ba03844070101243d000798000e0810701c03101004090a4601c6a401000348403102c440302d549003044035625002c1c13107034556020f8015030704490010410701d0380200070360201075860 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 76972313 1250 76971063 76971067
    0x106080304121110020d0909050121150614040e0601050d1209050d0b01060f0207080d0e0102030912060405060703020f04030201030e0f16090e0a0209060418050303101505 75
    0x104101640320701607402400346401d1850700300800d000881805141c5168040c1c0040388002c00607000a4813070f03d0305019100414400c0780006259003081c860702e4100d84284400c4c00d25156030381c240411603201d10100b9980880c60f010308001281d80780c0300e03610050106116106100010000b40002e86207004c81c2060141c01010042213141c5410000007000385d032120088499071084c81099407200c00c0d23070300714039080b851240c0200c00b000460088a8107a031080d0b2140c070b5807810040d03422a40c1d8503150003000c840c0d4000396034184009019a14a103408003050058a0501c03040c48046022408260101c8005512900611040c40024441139402c01307103d00e000c4d450040712150054052040741f0000f810946c0e2081c1e9040401420703c40a94400300036415600d02241c00f407001c207190302c16405108109464007101e1440e00701c00050340700d01903a0190034080550b840e003081000424a8000010039080041030b60390001e003043c8011485030740700f078120050030ba041088545c580c140c18110b1009200701 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 76973563 1250 76972313 76972319
    0x20c07180e060f070c021918180f0620070f03030e030a05030f0703021209160815010b030a0905030403030215010504020301051c0501020c0102041d0f160e21060402120106 75
    0x9220300345548401c1c0b0f42040b00954402c1d00c01f01e184003a984403072401c0d501420402040e0310304a00b0040344010f01904050001d9480c0e920490160104614001c00e00950741d0881800a910b980080345508424203800e869180c0c8a01d02d0f0400d64400c1e041100e1a09804855404040d054030540300d9200300b0300019802d003842c000c0090001c2c4005003010105014400001340c00c280f007501107482e0b481d9810300a000d10300385188003036611440101d005c0031068030148003085602e000035101864490010b111141a4604182c00c140c0d50310250030b031f170000ac2d200e10000c070100e2010070040c0000c51081e8014254600b04540101d16098103030030441c8214010001042241c0e121440003265060002001c05d05001d02d1400c20700a00c00c159003103886500100700011000d460086a9003004100710100c05207503502540c254001004607a0054030444070319240802c940b04140c01088000c0103082400344107440010802e2140d40c5c0c40b440c022a901401c1044214180305c2c01d107044004a182c024826607007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 76974813 1250 76973563 76973581
    0x31006020304080a150b040906021306050f160606030503030103050604051c120b010909061404060b25030203041d09010c0e010f0e0d0c030c03021804020108060d06020c07180e06 78
    0x2c040a0000c0300070714103145c00c02c003240c0e00c014444040100f08009100503880c4c508003135085030b80c00c0001c0740c460306800244c860159003158642c242e43c0e03140b5468111011411601d400a404096800310380d0b0b5030002c80060b81c03c10095000e54060001414240707480d14180c1e140c1010000400342185203034014984007a0002c102000f80a1400000700da14541d4100417640d20340164043c9a0240c244000090720844014580d049041c1c20741e0184901500c44400d64614811036083e4a9590300e21411a880502e9030031618051a1281c41624a440e558010214006800751b0b00060072083c000300b84116050248540110b40c141c2d0305020084800460002c4c0c296076440f0540e01c01d04c5144e071810019170307450164400702c0d0b1f039001581d441c00700d491303041018100202d404124040c01d00c0011278494813108081451203158143d5503500d413035891800380000300700c02c0c6c40121281764092046489100d01400650050f21340411801343c1001a030309150f06440c1038000f030140300d405c0607041c450749003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 76976063 1250 76974813 76974823
    0x2030907060c0b070503040516060f030614060d0c170702010c0e0d03090e070203090415030506060d20010e0d0b040b070306081c02030c0d02072c0402010c05010605040e0303100602030408 82
    0x4c20142480c94480d81d0b682406d070f04110000000380400100e00d140414800c2d0840d80d009090510707581e08205154846000c40300d05440c100c4210f510102c1800b041c94400425040403108524500e0310f0200c9500c54030010007400740c1610a81c0250b5180c90000070129070003804607484c0d2108aa40046258440d1005056a104c40c011039036410a880000743d00f250081040381c2708004098170070042c0102046008145440e42c2c0812201d40c041d440110f2040d01c0c100f0741c10500b25030468504040721800807558118904816142c0d414411040301400140e5114480d05030740c2030090040f4140c62810380b80c50b119540005040303400f4545442002e00c400d04001030f030b10f04800c500c03a0720415403120740202a4a076000d001481c072100c0c411212030881c080d90100b10030044407000c0104c083d0000740c003c081c2d4072501215803d58240c400340380004000d584581140e080c00740c003070b00c0005a6961201d001c00d0645100034200c5645500000600034004c86c030320180002800b04e440914181820141000c0d190 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 76977313 1250 76976063 76976071
    0x1501050703030c020718060f050103020705030d02030403020a1403120601020d050912100606050a110706050f091306090b090a0902010804030c03051210031b141504030506090102030907060c0b 84
    0x143c1d8520001103082c1c02009000c010305064131625480000c2400c1b4003001c1d05680c0610a0340c0046a00d00080650003030003600c7e64598040f002d181084a1080d1020003034100400030b60841c0b042200f240c01144c40e0b02070518080364040050340e580c01071100303001c5420314003800381e44c1154402c4a82d1071540d98040c09450b4019001c0f00c100c280c03210040318145c503000c1001c009a10291506000203101a00407006007410069a200c10342410303036603142d440d1101505e20880010560800c0340c40c0c0b00701c00507401415110301c018040220031940001c2c040841e60980c000c200501d40d1030003082850301c1c00c000403a50100581400b40200600c980c0001d040d218090002414810559141e50416008a00307644403da0400c5074250075140c210b50f4503084200301c0c0f0007030f10503081c1404100e105c1c81c03240e0654025654021042d6045600260a02032074900340000d40d200d400707041c0b00c0071001640601c1801c1c042c069103070000d41ca07402e05031032039030031301c0000e40c8404140128410f0000004103c9843c042e40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 76978419 1106 76977313 76977317
    0x315120303040206030412021603110a0509060a030b0c0f07120e0117011e1815080703030207060302090406080609060f0c090a120201030905030403110301051501050703 74
    0x60344026900650898001c05c006004584100c1d041020342400f40304031103550702501542c1e03503070040c5c540044554141000140d802071030103815000141c541164201002e04241000640c0d24202c1e10009008966590005501042c9441540c131b80080760aa420b6803840030b440d00b00c800b08040d07038100000c51150717450540c0551080002e64075460f01c4068020f41c41e4240507030700320014041400403011808006000c05c245c0c500c003402616aa504031008184001e0650b03d070681e11141c4d40004a46a00c240d2081010a90002d80702040301c0641c10300603a600e0718800424050405600306211a02c80c031800e20241240c00030b1128840c01041c0c0e800e01054882c008400c2840c854003048a50020000c1003e1244848800750711450300e205042c000361044069a625065410039481a220f00304034003c4080607040070300039164480010318000800002c01800a0b2160140d2580a81 = true := by decide +kernel

theorem cover : BRFrame.Cov 76798563 76978419 := by
  have h0 := BRFrame.cov_init 76798563
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76798563 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 76798563 ≤ n) (h2 : n < 76978419) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
