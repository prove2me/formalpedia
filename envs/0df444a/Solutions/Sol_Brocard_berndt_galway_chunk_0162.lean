-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0162
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:12:10.712978+00:00
-- url     : https://prove2.me/submissions/e90ef318-f09f-46a3-933c-ae9201cf3775

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 28956840 ≤ n < 29136696 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 28958090 1250 28956840 28956847
    0x20d2408070312030b03100f11090906040203040f0b0c03040c0608060a03080901260109051e060d0305070f0b0402010e040c080a0906110c030418060303020309010305040c080703110405070801050105 87
    0x1c96020b19105201010b5803130081a41c800c001c01007400e00704c50014200140391036444e20105d5031030a001c1c145040f80307820025030800c41280001044000060100390265a00001080c00d0050610182d8002900b00e07035000c0301401c107440c42100302d6000701d6040d02d44201d02100819420b200d02d289a000c0e00f001800d1304d80c22811a160107a859000522890500100400030350305038100c802c420707200c141c0011100352030350702d44458030041e94801090b2007440d0485842c4d16841c0e40740a048150044010744040c0300704a079500e02500c491040c00320240c00d0b0700d81c1c0b04403401000640000a8841ca2007030740c0741c0310410009800e000543d82d4250400780880d00c0d060000b213500c0342542c00070308200d024400104c0d101c50300000d4281580e101082080580d00002000c0c032021a03202c0c004d8491012060b000c124091954500030f44074059440c10604054482c000318080c01480107003623021703000c1c54003a10040d5a0f00e24011070340540b1040c42e02e010b2030030080003d071104d01401a10341202d2042c1c543c1c502c5e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 28959340 1250 28958090 28958093
    0x901110f030604150f03060e0111040f09020c01060b0c0c0a09020c031b07030602032401021f0c0c02062a0105010f0302010809150c0a1101060b0d0e03040504020d24080703 75
    0x28105020074003802c1c420b400c100103024001c1481000046011f00000078055155650903400c0d94007608038550141001c1000f00115403071064403204861a6200060b21042404c1050b8050070340d5070f001800b4940003040b050391401001c22098181101113500420b0156140c8480d01a4003441d07007410b03015003090081d64209200c21620011504002056410b441d41300e42e40e9074126002aa1658440032250440000c1d402905100b01c254000034001403075200300054070003c120541c04112900180caa0102c002c2e90b0740591030301e100365503005000341d03107600150000038840b910254225007880100d01802c01c0216042c4a490305076516036007440c51441c216001076400780d4000e888040b00b80b085062200b041c0c106003501a005c0c214401c1c0c2d107942c800f000383c0c0041c004142008140401d900d0b00404109040a0720200c80e41800008004244000302d0b0f66040c0c0ac502499001075001800002e80030340100c41940001ca1018a48120003c074000c0000070f19140d0740315000340d0001d58400c200900 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 28960590 1250 28959340 28959349
    0x20601030c0b161209030506090f1e0109060e03180f030a140a08040e190507091509030203030d0212011a1c0b19050108150d0f050a0209010e0901110f0306 68
    0x10b03400d000c100210f402d89207039607545080d00d11182d454030000340d01500d00380100716043c0000303074210003104001d1a4191828071344540f40d00f003030004c4400c0c8011000c94500454429000700d0507843e00f02c201044807440440c4895202d070301000443c0d003120300003005c3d10942d141c036203039070085030304068000c04d283e820079a2054000380090040c00d01c0d178481c056001001900c03a000500c054500d40d100780810741000f1140c4140885000300410403c0e003000200030034942e10040110841e1468040f1000358046100282c0d0060f0150300041d405000010b05140c0b1140c0c070303070024130404400b104660303002d03070b038822880d4407001c00382c1e00a901c240002c120400419094000300c2d810b0701030400d000611500b540f4006009124640207e22480a100e03208000c80c4d078200c8001540441d500803482c202c00b0078080000c09200014500030b12100624031403a0074048104501090f859014280c842656141c06003003c2d900c10885101c8115803d005c592092a8014410b441112020003203007400c5403100b10811 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 28961840 1250 28960590 28960597
    0x150415030b0d08070605070302030601022109030a0b01180207030203180604090c0e031002031302010c0804080d0203030417070308010302060c010b03010f0e0609010603020603040f05010b0604030606060f020601030c0b 95
    0x40101a1a100404460b99440741ca09048503c1106140c0e544d11451400001340c880c010069000e040c814000c0001c1660003244020300e61000c0b43d440b07001400d22550301c1405018030440290103205400c000c80c1000200e040c4117060314020301180c2c8003569282c00e07400c140c0c42280380082c0180c1051064280c9410a50408481da450007030642d428240c071742c0000343c129506070f000a00001c0e0b00d203188450380d003804d1003a504244040b100661a500c0c001c1e19003100140c0c0c0000081c1040200c080b0349041c0710546003030714003500344c400982e5013280000d0383c020f68a410981d000da1326030213100107901028002c04102d80d503540e4191940b001582c40c2d5005c21040d40c00905110045540b100920030007a902032144242910803010000786601c00c80c18606e01e8228001c0150382540c0c03415105101590350301c8241c9910951141602400c20b04500c0c01da800344c00410030b076070381044001c03d001c4100710031504070406543e50b96440c2a000131502c40226540d29080c480507080781d1804d90305010150b0341f00000d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 28963090 1250 28961840 28961879
    0xb0f0309010603150c08060f030705100c0c0e0402012709020d0f1e0e0309090c071506030f0605070512070f05090a0902030a11180f010e10020a030e1504 67
    0x1001e95813621060004403401c00420032050342c5450074008203420040c9150802c0f0300ba6100d40107449100c01190b07a404140c014a4480c191406201050074410b943d1800250b038403008601d8038903510500c0b0910b07208161b90481c0824143c1411039200d06031000c2049078142c0c0304c20070180e214940b42c00280203601c1400000d100f00d0b181c0b00b134985040c40a000b4a0039621200c845510101182140b0100303c54045161304c450350000c00500310030b503540c0f4028940028450303086e00d03a03070000c5140170b00d0399281080c0310050503402c10304c001090105055a1191040c000d00080c00665120302c41100c407032051210a210110505000c219504d21584039481038a0341d0f424414984a41140024000b85082e40011080c58001040202054050161016401e03041260900b054039050b0400f00080c20789080c14000c880582c2c40b101c00b680314900d078101c40c203800f074105107a03160502c60013511445c807450144c1c04100d81c520101810700341100c10b0038036041c5520301d903410711341801100844040382003903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 28964340 1250 28963090 28963093
    0xa0c0509070c021206180d08040b150d0302030a020105070504150c0c17060a150302010f140f0301030605180f0309041e061e0f0605120405100f020c1203010b0f0309 72
    0x202c40050b00c03450392101d040d24407100140540d1810f414002c00c0c034501d48480c030401d9001511005404e40e00803004a0304690b004401c00007a40e1000080d8034030649101031941d00443c4411034106160700030004004000440d0f0091000c2d0f901c010040d2070b0f610951080c603c54420040d01c0e40d101c45c0c4503240e9002c581d481509004641a507030300b0424030351a250b100e000840d403c1881444102190380c80b502148181180074401d200b40b641d000a8600e252090409007400150b1007001d440c40000402c4403440c01061240c0303602d135616810202c0c0101000c03103250709048503000c50920000c07000540340070509490002180b03400ca801045c40064a01583c1100c0c48064005814000d41c80c0c0e400380307a02415900ba14000c50101403c00104020705551004120780110f880511049510904070360020303009102103207086c0c481c1c0c6001031030003120b024242007080c5841644480301400c2c3d00145444c40c20401101c924012081e450a0b01b444284600b101d90b280c10404800000112005958030025007030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 28965590 1250 28964340 28964357
    0xc08040209040f15051e01090e0304060f05040e0c071506051c11030607020f0d03050c0403060914060c04050301110301080c010806120607030507110c030706050c0a0215040311030a0c050907 83
    0x1840016980c5c184d130980c03454055400301c60b601c0b00c2c1401425004000c4c1c60700501084090403502034a80c403541c0103401c00c0008525009198a008a040301c00400c0d2156654a081c50807009c001c1c1d0390780200c10102c981d50b00103c46e1540b03881241c0074080660703e00624401700c1d02e100c2c40200307884480e110800c5440d80000241c000c2c0300da07024800303144114155000303031070050001890981018903810000041c14030b0030b428010012a42c4007500e05499100300c0008640c84181001c2c406420180c0d100c4e4101e220301820440710425020240040306c40980c000d01c00150035902080d1f8a000c01d001d06c3c03039075501510700000c0b558818518a40c2240d8050140064103114a40e01420b0100840781d0f01c01090301c403414082416441004a0142d070150070140030098090f03c00aa142d607924031860040220110322158100c40034448840b0a0303500030001c1003a10707210542d030350303c0340c103e44415101c212030814601d809042c08116000c82d55841440d44840314100f1040245081c809000001040b4201e07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 28966840 1250 28965590 28965623
    0xb0901080609180609060f070507050a081c1b030b01020706171b030112051605030319180303091403030304030c080f091e0f01020d1d040f0c0f02010c08040209040f 72
    0x2803013603e0103030142202914044c5850303485054410b101410360001c2040402105011850100e0310020290741b1400140d50340862a5400030b17100c40084a1502d2640b07441640006008401303807500400c3c1c0b141c0c40038400c420140f801a600c40e5203900c190000301d40012038510070481d49465003030703020024040c46200d07107455514807070203500241c200d1900305032000981c0003405400c102442c1150824605a102036003004c0102c0d84034040c0f500d00b00d010011200449405601a040345400c40c01c2c0142c1140c140c83d500c0c00d000b0407003c280e12450354640c0000411807d241004400c582c86250103442d640004a41540d410f260b5a11410310300d108034406008014543d0350303038201c480c556124050396021134841070f400c115a441001119906560109400c0b080070380d0401004042c0c101c0040210b00e1104003040403401901403040c14047c4071b40b50000c1090456000110421044e89075402044401d44ad418203803008001079401030350140c0000006070010700182082070005100e0400316070f464122 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 28968090 1250 28966840 28966843
    0x6090c0d021305040804090b09010308040308130305011e0501090e0703080c0a050d0e0301050901060501080a0f0618060f0b0703020a0605070507060f02090f03120405040504020a0314010203100b090108060918 91
    0xfa1401c48604170300040810400149004d810140c0368201d0380f0800b15407442d40d46041078410b510000300080f03130129480c810b80120060401c019034210000380100b29202c0844440c00c4010307018450040c0c034207400030030800f10911500d40ac440401005008c42402c0d500c41075400c0d0440008074000c6e1241e0709800e000a0002d0240c3c032402a07a548440c40e11804a0301010700350b8100516454803a0b15160080100e40c1c3d001c00300c1d6811102c841c500150101c0100d18080c003403d00f40c1c00810341100c65442e146a41040d55009004841007100c00c0080035807038034010000c0388203e01024006a0003014900c01098003a441a42c1001e01070400514102c1e0b6555400b0070b0303034000e1900700e107541c3d030101c0c00010509000c43d500c42440004c03005400c0d0300071000400e43d903600490023514080c984d190b00103011504c4003500c61001d15008030b5004088110810000d01079402264402da00c540c0b0b10300e0000c0d1001c800815103814040c140c648140c940e07228807d01124120050907010203100c04071700c0800e01e510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 28969340 1250 28968090 28968101
    0x9030d0c080705010c0f030e031611030f060c0711010804050c061305030607020d03050c09130e030912060a06050904051c031e02120105010c020a060f050d020a0f080906090c0d0213 79
    0x4068441b4490041035a001a0481d881d2080d0414141c01c2005001654400c4c0b00d61100b00702d034080821403101491201007071034002c00d2450306142d07104004c00c3c801d10000f80c4010782205e0b0310400f215080840c039007004403078001c07080c2c400801d00d511000030100326107400303005440c904031500320f8056403030345d5034000a00d17101013079800b0780168000c8061550b00340d03450300440c0d41c08a2000c10541c074194580700030891000041030000c0403160788002d40c6a200d2070910464808032401031003d0000009401e40701d44440d401c0c2c0f00040864a802800103003800c00c0300c1c01c40d00c2280c01c03601801820344099161860040102c40000425941d0604825172080a0810100b03080c410500140c40e58903151881880e108181c002c14140010396050000581c0c0d1003024000f030720224500940790100c1e8510a80741c81c010404a030b0803590010800806030b83d441031032030740d45d0041c0703580e1490103841e8180847d440d5034041d00c601c0c0503508404d9508400b414009140c601a0340b000e00034820401000036800c04688 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 28970590 1250 28969340 28969361
    0x50a06060303050c0601092007060605030105041b0801060b0a08041103060702030a0e06040305031c02090604030803090c04050702030405100504030501020301030308070914030a0209040305070f060c031109030d0c08070501 97
    0xb00f01081c1e810501c00f0400140d409004006404c005114824890b03150100501e18020f0000400044410401c4007607000100107100240c024492414645403030315089050070301045414071414800200044140644012906401e01540c036121600d0350485850900500564070602926900c03181901d0402020344180c1203540619120040c00d44002c05035101e040e2490300c80c0105010600106001100701e466149e0003802d6096192590f20016019003e040c000a0b880540490000140410070300218800e00f650b0055494108a200030042160015128100140d105002c00d00950905030303018041d00d8080e080a1b403c0c07a40da5507940c0e082e42d009030421000584000c05101e4110b030410b494002603c5108143c2d1034004150000c2581e524558002900c41c800391400b142c14103019100320f408154208412a03607000050030944058940da240c3d01000a1074030a11141702c0320f440b01500d6042a0060240007441e650010444541c2008201540c1c2c0c140c04015143c0002c00c00d10481d04c030b14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 28971840 1250 28970590 28970597
    0xf0105041208042102031b06011409270a0204051e04020402030601050903191a011206020a0c060c080105030c0103060b0d02181e1918052707050a050a061407050a06060303 75
    0x1f010040e2001751000190b10382c0e10070b2648000014407003106000700301482c882090713652100b250344040300c03c081382200f80f41e80d201d8045800f0400c5419071011428030f200078000c1c3c1d000d01180d104c10001c1c96a119000724061910031a0f0f40c049001403810350015500400d051400a0400c01160300180c00c1000c080e44140072141c555641004001040701415540b407401020303030540f5858422005403403583c12100404050780061907101f0280608044422180c110340104165030703240a000d84410404c3c012940700c3e01c140b10b015011584a8025030056034400b14402e81001c10f071200c03410281d041400f0080c1a04070301e10b2440c40075140d480d00c1514464404949c030406030004000c1c00341203140369812550080c00c1d420184401e030640301c664294a42051000141c82c1e0b0361500b084a042d410350347d0031036030326502083c07500b00e0580014010260303601212042401e9583d081008401550740c46181d01041948082c446002c05002c05000010b0080056070095001d6035224400c544041c0c0044012 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 28973090 1250 28971840 28971847
    0x2070807120c06090503100b1906020a050106080c100309050307020d0b040309120804060c030c02030d11010e0313061818090b13111201090813030201020f010504120804210203 77
    0xb484030b0b0350340482c028a41414940600c5081c000030a03100d014403c00024140c1c0c803030305034244070340365200e0340792000707000c1d10058181c152504c4000791104071640c001d58056017442d1010075581400f06030308139802c0703000346a20402280702d2000d8001e0311b9900001e40f000d00061000901689980340e40d498500c3c0300b83d8034121180346c145801303800c1912680103000e4503042c051880001816000465041c2c0c3d4640c00c0046000c81c3c1880c04071106003000c1802034140c06a00404100d141e00303d40e030340d05c90888103c001d10008002d41e90440e40ca009814891181441c82041004002e00501720f20112043c2c02020b120100d4882041d01e2917480e20f40d00b41e0052554410300881800b4a000f1403a40001058424551b880c1050b02d0f0030700401600c1c0c0555104041e01101c840016409610205916500102c201d48078222501c02006202c0f00b07200507405400303050783c4101002c2041c803d4520907940010700400040318064116001c080050044503000d2017003c40446802d99400c0000388003065900a40d503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 28974340 1250 28973090 28973093
    0xa030e030d0e1503040f170301050f090603030d02090102030c010c050301061d0d03210603060e070e0712050408040e0a06030201030627090503090d0b0916050f01030c0207080712 78
    0x19068940303560720104480340e030101c0341c50b664007080100c80c0d40c0c02c10507050304c9840310b0518942100307130b4003c0100154840302c072101044104030007550403164111801088410f00c0010312217613080885030365502d50403c00203214045101e038083e240c980810301c1168180600003a1642c21212000c40c10004500040010420654454008040b621011458100c448112404900c88a0355181c00905009001c0080024070001070300f5201c9444459805200050362401c00784002c02e940c0d2440d461a0150b82404241202c3e80c0c140903005642940d0f490500c0b882d80e1404600503c400384c8201d0b2603e000300000207500c040e100c1030b030b0f00a81d000c2100244080c903510024044074070550017030f00b50b1020848052162400078040b00d05024080c803001c1820f120740e15140b402c40c891500b12540c08400d83d2411814400d03c440080c0c0b01d10348420403a640b03203c58000e4813a905005204250340038400705046581d0754400d421400788030403140120303000380343ca44050500b002003a4210005064a2006240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 28975590 1250 28974340 28974343
    0xd060305120f0a030506010e0a0b030a05070c02030d08071202030103060510050a0609030303052e06030b01170408090d140c010215060603060d0c151d040b01020601050112020c0a030e03 81
    0xe03180d4401c031680d207494525401102a0b01804003644145581c2c1c0c400910b150b4040c040f8040c1c00c010003420813403129250808125540c10a9034080c9800e8a414006008540141024413505400034010310799403030300000c1142d401c4801096001004001051959581c0042c000745010b90b101c0c3c0302c0071420303280403042d403007001400e58000c0d40301d807161840421009402640e86400c2d640c2500e00442d00b69a502d0104214600325845030b10400c811042040a440b03c46c01144155110341ea41882007a00a000454018001200e900154641d2801081c001003201c4018600008058548805a405da403074101c1210500d1f0061441a00510440c190560b810303c0400c03aa01079201064100d820003002140311400020b001501030581c02116500380030a1028200041c500711540c42041c0104040060450b150345080760200c59041c01c0c004030368074003806034508a08041c2c1c02807003542c5c40c00c0011165500d20005411500780e08000c030200030001400302c0c04a15010741c80d104c5070204503a0616 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 28976840 1250 28975590 28975603
    0x3040c0501081321030209060f07020a09020403050c0120060906090706090b03130201090305030a02010b011101090b0c090109051e090903030c1602010e060706090510020a0c080c0a05030d060305 85
    0x100c06451a2800c0d507400542c0c910224045814001c135040c0024030b82c188160024032030040a29401840442d80390448a03000c0c00521101c0e100341c88a1600a40c0d42e541c0e0070590155000041280e00003200f26003140d48620351102003821519458950640740c94081424140161214040c6030043c038104008003504100050003400c01d49820444c040c507141008505002c0981f4801518000c00001429603114a1500b0084e41d008000c3d80c0d035070401404042e0091a034940300c0c2d40880c05140900c46551018490441e04640101e225415030303540c003000103450790016210906114500002282070b03150a0000e588000390800161050300c00081000360030800200701128950080042180ba587c0c1202500d202c40950803400715111038910060f2000d0301e80e0f82c1d200742c120344085501418030542d42c0200d07000b14022800c0d100714003c2108000b050b03204d10789142000c0348a10340361400207890701c0000e0421044a0050350215141d95507994210350210f02040a0161224818801e2003000d2012 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 28978090 1250 28976840 28976851
    0x30c0303090c0b030a1a0d231e0102040f06030902130b01050408010606020105010305060f0603150604020f1c060b04051809070504060b1201050d0b0c030a060b0f040f05040603170c030705010203040c050108 90
    0x40300c0c071201141c1e84005666143c40e44030503281d223148001102d1000d0030018441001840c603000e2805a0340050001d0003900180703d0903040720300c54000014220302900c034088200750041c00c00f911003a20030b043c4001800841e0007c5041200400001903011004c0c0b0070500600115030000c40c0381e500d181402c61900740003600c0d09483d12a480240030240d900010b004030540d01e03280801102d0354400002400a001d0075161200040c40000c1c5050351038403814203074042c00380400d070402c44107840d40102c0d4442d0166001ea0741e00710050802616842001000320b039404141d0300700300c0e030700b00b9190ba022900307954250788404000040131452101200540b8421400341800b03481903402c9082d15182c50001050117403484101800004c0801c0c03210000307400600c050065010150750b980302e4581c04030015409803085500490b012314010400780344c103019140c2141c3c1c109220500021602c2c014090581c0403145407100d91100f000700c900012028009148500e0107000031250b03a503d0b000000d031505100400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 28979340 1250 28978090 28978099
    0x10e0601141f03020c010203010e040203160602031803011d010501030c0b070c0b160507030506100815010306020a0207180204140603040f03030515030a060207120c030c0303090c0b030a1a 82
    0x8444550b40c0711110b04881e484400c0142000e0101441c50a070028421040c0015030303940000300105110032100142c5016038030903402c80d0f0f988400510100d43d80d0400b0700494005070820410400d180340e29402c0e01c0b0030301c40010b00000e811880c40c0c59050052400c0c80504129035100d00040003400b00100c0c00c00f0003401d4001c040b515000360781d50342564030030f041d00485031083c1020070413591400101c9201c80384c213980541142d960319140d0030015500c0c0c40440389403030007000c0b06001040348840468030584040c90243c6004441c0d003103540d500040d400104084045101c1c1d2200064580c1184029401c0140112001a40c907420900c1e104041c6403501c0d0a5401808108140000900da0010039042c481c1c05140002d03c03a103d5000310a400d00d604481c15238540300c0c0d15404020301c01c03203a00810203503100d0200d00340803450b41501507400c20000e03400074000c141142d040d00b012074042d4100348a11449032610141701502c1c1c424150060700140c0d076910582c0e41d240240101c00f101c450011084090484 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 28980590 1250 28979340 28979369
    0xb0106030e120a141b0601080118110909120315040b040902030d030b030102040b0a110f07061e12050703020c01050c0f091e0301021902010b010806010f180b0a02010e0601 75
    0x44541e0000c0c440c0c100c00300c04000e50f1380b4207254001107840580d04000903a00e103052004452180e455a1a88280a40c5409500c5c0c0350701d1403071000003c0c0d22107901d075500402d88402c117607151080040030540100b9020710f0f03020f401141c8400720b00302401107106182da02e01c01c5040785c4030300d0240800c8031105440d13103004034030300321a1074090b0354006018910a090b80c03901061091070100801c0c0680102e81c4a003070b10800c04201c0010454001c01417610003a465011a200700c14100c4a0650b01c0e040c81c4100c8010030441400c9072011140302d0346401010045003890080c46044c1d490a0045401c220344010000e540401c4a40ca81c0000780602d0342c0296050320f1480c24403010145000742c070b100e90400e2074031440d440b08030862906140ca12048211034010000c64440011010251840e6000711401005510300400c2541e5580255071080c01240b0694030f246a2400c0000280c5034000d070801e0101d404443c002c4000303070440010000740b204041e03d0340041403482060041c5450051b041e00b10711000e85041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 28981840 1250 28980590 28980613
    0xf0d120806010203070809190e09030406120c050a0503090114010f0302010f090602071e030203060705031009110306120c0901150f030524150409140c090f040b120106030b0106030e 79
    0x4405640c020350080321100c40560301c90a00070340d010225440270003e400386030108502c206c40400a48202c0d04541c403105c0c0c0ba21412a00031080342c0303213190f114010910511660601da8480c1028561007580e0340d000207400d190201134024000d2003680103580041c07201e0403d20840d41c0c070a8441400101c0c900304490a9814124065100d4103103024541c8903004000b40c0000000360f0780c1210b002190098161129401e00e140c0040160b842224494141c0301c4032100000d00108900c100e140c2204800146811916030004002010b542c25154480e984140d400c0785c126a501c80e2036450080150f00c034070441156100d000607118144100e0352205240c078243c2044900070300d042d500d015582c0903602d500d00ca40c0c0480c0010346050711402001380b1101d0086800b06400c012035104a070b041e52101994141e030703035488070400308c94401c914211782c101c600b01c031418ec82c60620b41c101c01c0d40e03504010560485284132440c0c441c2100e805a03c04e0b00d000fa01100104041e0750984503114000306208064040e15080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 28983090 1250 28981840 28981853
    0x1030507091404141302030c09070c0803040804090513060e0109021507051c020102090a0b09010c0b0403050c0a0609060506030706091505070c030501050901050a05091002090f0d12080601020307 85
    0x39403007054007490346000d802c0c007207948030382c481c150076918012854550305000b280320450351031110303049002e4800c0480701d01c02407a101648601c00c0d4065501c08904101d00d41e145449034001034000c90b59000305000c0411010340d14060184103230400419070b0070b401114180001501c120308008071180c4d01d040381e4480945c5078505030001c1d503020a58900ea44240d680352a41c0b510f800fa5411490f0200c90100050101d81d06400a024a40d0f00310746415081d900c607081c410042c412154010f000c900d00d13510040c0082c07441d1100607400750280c20300f14242800341c0485070406030240c81c1194210381d10b144040030010103225050b0001400d4004022150030403001900946160180c15400300f1140d0741d40d090b00d41315900f00c440c0d4a40c400d8000000c1c65030391070700c54060101607440c0c00302d0b0b500f030030300041d01a0091300c15903129542c0300d030003420441c410008140095000140d1503802003c40d240c2d0207415141c0c569880000c9101d040d02400c51042081c006001c5200a42024110f4100700312080200740e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 28984340 1250 28983090 28983107
    0x270a030305070c0905150f130e03040312020705010f030e1501060507020306010905010e04030507051f0212070c0305040612090204230a02030603060106030c12090605090106060c02030a06021e07060b010e01030507 93
    0x2400e951f5a6144160a00095214980841d0100c4071508200511181c0322001c03000d44110713442600720194005e0b41e94421307a100d80131405000c1c002144400c409801c640b181d0070442c140c8009500303442da42c6c45001c0743c000b4128001d0b0024408110000761032401c600741001460700401c68003400700041d50400002900008001d480a010030a02284050501c4001c4c499045018223486085200155880d103450294000f04010200d251198000400c542e0003099a01e00d10f5505a4030f4900c3d050a090040d9a00720400d540e440b08184e4075602e01d030041e150b902ca01a024100600d50306061100b40e1506035120f04002c1414041e0b50060040c030449840016002d4103490542c00d0118000d85a0f440c11500c04242d03504a452840c1080340c3e600c1481199400107000b2008580203010080d11b0344015030303030051650b5000303415074490040340010500d580d0103410340f04003411510036042400d0001800c3c6811074102a01c41903640c03a029451903806c000304074a07401c420700b42030115103000e4602038030000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 28985590 1250 28984340 28984381
    0x6080c16050708070806070f031506080a180f0203010509070b0f0a03020c1603020a0501090605030406050a02070f050c0301051506030703050415090606050a06080c270a030305070c0905 81
    0x40c40e640201002030a0281d100504222411103c90f203035100c0c51a40d07101002d8487da8007190038030401c90f440a2217801000f04050155a80e03425442c1f071304000701c5000600401b130101b5a541d80b4a500e02e10114858031030b07015405070070115048501070041508681e000303812404141d0180204102c081182000c2e2010310710741e04c01444d00e13100c208605a010b4400c0e9648940f10b03001e4083c3d0524014131105408090328004d0700c0071340320182c41d04015100349419016803400303d641400046c2c0050761503041151f10650004000d0708001840e40c0381c03100b03a158000704540075045940e0764003050600f482010b44c03290f040400811007000f410301280061202400b0007041586078000602400b10307182a5000c880c030901002c0008041d00c1c1484c20043c010342c0500c501c1010a0180090001c2c03140001c580128041200c99282088600a01000c0b854424a20068200410304110640d0720851a240118082d0300c0d1550380700414602a4010350040d007189800c6c034a00004d000d100e100c8407003040140f2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 28986840 1250 28985590 28985617
    0x5061003020d02040b03130b010504112203050a030206070f02010504020a0b0c010b091608180d081e010603050702010b030a150c0e060301060201091401270602190305090706080c 78
    0x500c1034000d010b01030b205a42019658402c0003052042001c100050904d54a005510402d043d03602c400070401a03410246103440880828800b4140d0341207102a58080100f0040d002244160340c2d640b040d0a040c2c034000182e0158104030200b014403030700b04000903003240d1a84000c014501c1c2942c0026015101402420805500802c2c80f00c5e0310794003580807484081004103102d0080c90131003e001c1500c2d01441c640b400137000500440c01e100000c1110340400360000700036025030794940c00d040381e100c080145907460340200446c91902e109414090b960207050540c1e4003248034900340d40302909445400c05000c3c0030358030421707200000c50005420840040c001c6400802c0f240c01d40b03030044071410008000d9943c0300030008000a9580e0b01540b21088561250707a60700700d040c9151a40354222403010420f0380c0705450040f820f807001e000029412850034810b81005090a80810401848214492109000c60703503d00a010101c101009400024400d07031800c4080e503d01680e524915000da5102d0315100c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 28988090 1250 28986840 28986847
    0x1050601120507050a2715030e01110304080f040308030408040306060b21100512210301080c010e011101020313031b1509170c0a110907020a0f020a050409030503090106090506100302 80
    0x351030703070016a00c0b000388282011080d060344401280468014910300e0740082883d1909c0318092282c18000c50703c00b004241d408509581c0c8685171155258030051307070b04001203020000071001407001d0001d18012401100c00315100e070305602c1d180080398a00e4202044504042c402c2840c0404181c01c110311002c0d0040b108205500c0305072401c80300c14016001594000341114241034002c10000b002c8104084603150404d403a28041c64a000344e2000703006d00130080e00200d0061005501800d8004a0020306240002d45400200c1e4441d08a0704140c1d4620030310f440810551050561107a943c0e80d0400010b40e07000305100e480e40d515040c991908148100761500d94890100740080d00e01d481004a9090309801e90352141880f1b52900c96820b000c04941030074520708080d0035400c00f00c44981c031030b480741e40040c000c4000d5911240300c0312402801c200c0c3d00809110011803207072200e00507400c4280c0700e0b8030ba268076410442141d90946101d80c1050040f240b60000f0400e251381c6103180c9502251160800599 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 28989340 1250 28988090 28988117
    0x604050c070206090118050d2103020301061407030c02040f0b03060901020f0909060d020a030503040806070c08120a0e0f0a0b090f060f07090305060106050306131118040b0306010801050601120507050a 88
    0x3040120ba07801f40da031040b07000c01040d080c00382d01030f081400880301308904000301056110a5040740030038061360000503035416400011906c40310003052000d000c2d00b8074400c038194903400141901c06080d4400c0c0d04030780355030400c0143d040400c002034021580b50000c0d82080c0b612940100940500c1c0340d41d42c801e01c40e9501054068803128a40d2a406801804020155840c5e09065a407540300c0d02c00c0101c68801e14000682c050301c1500c1c00c505d00b0350300030803040c507100107031503641307103813a006840da0610656132510240402020007260482100284c0030b807460b8406418203c03503942c0f0051a581180c0c22005148861042c0480d44c0c50b441240c1070340328500da4481000c12150f450003500300501c14890400045540b98003d405180302c1c0500300c40385480701415039428004c1d16400c0104d0041420b05002c184082c4403481c0d84181400006800054480044000240303040d600b07a1000005956a01c10306c0310740d50340000d0038143d4100340001401141040c220081c42417050000398410480600c040c0c42c2c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 28990590 1250 28989340 28989377
    0x3081605030610050d0c0302041a04030c0603110d060f0501090b03100e04031103030103240212010504020a030b04050f0615031504020f0d0507080105010206090708070308070602070c0e0604050c0702060901 90
    0x550000c903502040020144c20074011f00294000e000750341240900d07044100b100c8540e9400c8500790f035400444499540d250a1094014008880d441c03000261305010b8044209080c0c0300d400000c180034941078004a1034440050b14580f142e420440000c81d0400c104900541688001c0003160740184640e4102d540d5401c08076288840240c600011f07010000000081c8071f100322a0340c4540b882a00040c070f180c40020a840e080b0b100b4002a84008101c0700010170040c030303042c0d0190031441440e0501040810b0720b8000a003c5400850700c4084030308140b8244039182c20900d04508860300030f50180d61540c24003035000c0b140030140c5200e583c4a20b030002404072305c038214030040d5981c80c0e00c8420140000d00b810000a0004042401500e0041c411100040c00885d03000500b48100c4403004042c10400f030a51301c6900e140c1d40150020b4a61640800c901030001c0c03940c000101c0217225000c00c8020a081c01c1c0c01304810390314050040a4002d00602411025030740d840200c0b2803402c03007420240c10402ca2695280c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 28991840 1250 28990590 28990597
    0x190501021606051b0720150c0609160501090b0901030209060d0905010c080610080903040803030906101401080f0a06090f021305090708060607060e07060504030308160503061005 78
    0x4015512600309032a08000c0d0301d8210500070070090141d20425062250720400d980a240c4000e040241802001030764680450f196009a400240c1450a180c0d1f0011440b080340d48044130542040c0c0c09002045444102403000c0103014080300b000c144003502c8c00e0b0000f400c1080600400041e1140040c050301c4c08e0b07009c0c0d8102c0d001f0250140000362110141c01110300100301380ca00c00d8545500f40251042c071184240b03420b074410700c2d0040011107035120314503040b6288200100400c0c05440104408280e052040019500c1511060001c001c186405601c1c40080101a402070b4a402c80c6410408803a030b0308a0441c5034804a44001c1488aa40e446605405409241d1144034000d00c1c042c0c0303821002d0703102d80003410000e0006091007000b035900e10a002e0380141c115225400101a10b01207145454498024178426010354404180c1000c084000b90410003545d0120001c41d00c001001c20406400444043d0b01035070000a1151920200001500f43e1000038155445046060511100c403802041034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 28993090 1250 28991840 28991857
    0x10605031302031603150504120c050a0501060807030510020a0e0d151406040b0607051005090304150804060507051303060e010e0303010b040807080a030f0302090f090a050406060b0c19050102 84
    0x1100c4c69982152075007880f0103c01d0200f40c3d940e4054003da20440039243c052a4002ca42c8080c180441d1103405804850f000e034204c000316840d0080d06910004076509000725000b800d05000a4a8210700e907141103460b108004102043c01401070080c0b4903c1500880b42800f404030541e007201006035a482d080d1058141412003202891804401142d00110f01203424480d80058070308001c00d10a4104006160151160091881d0b103e0340034046a81e03000d400040e004400703401101d05281d02c070f015000050704aa040c410005900104000500c2000d008454110300300c1d042892038080715003821412881c0314000a0142a04ca0b102010081025400820301c00170b03840c292500d070758481c004410716230700c42d2040da8900d208040c0040b400000c04210340480c25891789418140381b01c009810340107904070741082580084c03030500c900c20701c0d01d1b44800305120b2204020000b4040c40c240c81e08604072813880d00f1007080300303070300740444083c1620020701d900ea07401044180030006500d0740303801806803040031007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 28994340 1250 28993090 28993093
    0xe010903150608010c0c0b161b03050a03050c1810090801020d1d0115060e0607080406021c08130201030f060b1b0705040902150705010608060c0d0e0307020901060503130203 76
    0x680c00140a450b81c4402e043d5603603c0002d200c607801c42a81281d0214503400c1c05056000c160021804100d03084005280c507811500307040001c0340c03850749810703041d02104e44140d01203080040c1d100e034000d41c58880c8644c881e04082290b8242002d03854030a2601c000c3c0417006008481d09100c44617818001c503291401402807034001c0d5950341102091074082d01c9000c10300801c00550a0500381403410601550040d450980d031420106483c1100442d191507280b41d040e07801400401c800700105512100420103000650010841c41c1890a4407803205a60391507250200003104050102c10841980c0703040e0160703024a40840d01080410644009243d180c0c42001401c0c0001000344404a0a41206080b00c03031203002e80d08119640c00a100c255085218001c2d402113086202608940c0c00ea03000e080018024000011025100e0b00058604202992640908103003c918529260f9440c011382c030080d184007000c6c5003080140d50200341c0c1a80d040c0100f405101000c800500500d000c0f600d840070482c2c0003070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 28995590 1250 28994340 28994363
    0x5060106020c09130b130c030501020a05031e0108060612070f060206060a0b090a0302060a03090f14010b040603050d2006010f0905010512100203091609020a0905010c0308070e010903 80
    0x20800796441064030101409003460200183c003048403940c0b000700c40e41c0c02c240c40252a40d12080c0039000e840400c881200c54009200d4048003096092015000444032600d40c96038909000002540c500d098030031405420018400500000e100400c3c1543c200710141c0d01070821513410340455042442d0307504480d0078a2401003002070902c5d030001e03c40c1d01410054842c0c0c0790071078485101940c203100e03856507550011307410281040103003001801015025418980000d180c40199500781350140d026905445142d1000075201e07540a084c811295000350480e010808640340d65039458840c0d00382c2ca0b0306024051581070100900c03c010300c0324018540351905480d2250785a9100002403003080c029022080c0c6000004203c2d400d00004a900c0c40c82c17060300815181c1c6061202318041e43c0f0080018000380034a0f10b40c1440001b42c89828800703403080c90000b50b200c405951000b03005078820b80c011030401075541d074030501080d000310485030048082c2c40e015506502140050311119000d50008201e00c0491 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 28996840 1250 28995590 28995599
    0xb09150c07051002060103030c031211120a0605030114010302040f0204080d020102180901080a021e03070603020c0622330203040b01051009060503130606230904120806010309050601 80
    0x105801e400e44034119024080d4500480080ba9650301c24000200805c1204220001007030040d071502544a41110340402d140020703041e00016030300b100d540c0c148460262014494081d440e8041e03030b00509402c5d0001c02000c0c03500c561002500906210203400360ba82c1d03c1c07020490003030640441c4e01606d00b00040351300710030314090000d000b5401980d00c9482064501c0c811041c510702100d50a0482c3e1054004020200041e001c0112030502101200c1c28503400381c41d103c400e91000e12650006080d6911f0058941c1d80f000d003200d09112004080490542c10ba8000401c10b03494120600d407841d4001b82240c013039210700303020130404080301980e51140c2c01800391156000080d6070011f42c8901d100c1c0d600400580d990303d0600c00328100700000e00e070106c0c50081c014071a0620a0f00910790060704100a0304044006807102d0b021610541c10012902c01000380506904400d440900b51442d000e40e01000c152420352200c2d00d401c5041010744d4104001c4c4408901668401e4005160f065000020b4842c1541e44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 28998090 1250 28996840 28996843
    0x5030f0304031106040201080a0c090801050c0403060e120a0f05040302040218030f150a0b0414040f1211030f03040305091e01030e1c030902010210020a030507110c01090b09150c 78
    0x8641c00c80020388051507550300800049080341c022a81a12804001d4590080c1c030809006c030400d1038020815070850011b2403035402d02405002d520f010756503690340c6045044c51400d45903102580041075100c1d04095056408046c100e5a1840444c82c0120340501c2c043c03011241449107600180d40b06001258440240e540c0f012450000d00f4110100d5601c407034807196068850312440d803c000c1030000c010002d800641540c0002c030302580c00600008a4803054820303900801da040d40c060b16200340107076010707080224484406000103090304003064200005122a65a8420a891240b000d240400804e040600405c1503130070340d18004004218840b40d07420410400d185858040380000e0030b0501001c80740304003154071002803040504003107a4240c62003040d800b5164402013241140306400c55102c00314200d2000e00000c11603a03401041501303080d603008100002c0d180c440002d0b50850000c1409582e0803503503580403144080d1520f6218488100020b44d0484440105a6807020008007034850020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 28999340 1250 28998090 28998097
    0x30203010609120203060c090d020301090809180c030712060504020316032004030f050a0b0708060102010b090601080a0f1803021c090e010603020c0c04061d06010f050a05090303040305030f 83
    0x1810b40ea44078100303503a07003190a01c401e40d4420294154010304042494180b03103000070440f2000247c042c6184415960210b0b00b19052101e041e0794040c80030442e00581d03d061915848071404203540340200381070020b404084c501c400340405092000403002d41070440340642024000f410014011510307894043c045491081c400002540000e10301954100960740d481c04100a040c3d0304480c00c0c1c1003034107660701e100319041c06010903115489115000700c0000d49003581144a101170380d4a20649091640003e42500e42c141c0550340f1488081381040440e0b640401d0a5a00040811000c141e0484460508000344101004154400c90304030440c010f158000410480034a080c402c0d22921105901044600312124001c0e41c410080c0e5000401c10365110350041e144c1002c07a4815104040d1101001600311a130f15802500c0880d91086001c19101c0c020413281d038401000c0c21714540000208200030683c4c490300c0005800e015001c100510241c07410801d880141d64024122a0703209061820b0245540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 29000590 1250 28999340 28999349
    0x414011e05030402150a0c0303090804081911030a0f08031513020a0e0904080f0a05041806060e01080f130302070e040501060e07020c0102030a05031302100e120705150906071203020301 81
    0x120001929161766015812181068071554503019076802c04e54045000d00507031082920500000d110204c0c00d20003d0101e607a56500c151f200a5141c040ca207031401c02468410030642c0f00c0e07040441c01c1404280202582d80000e6170010f4016500d60b611021506c403c03049148083c1c0240140701c811400d00c01c15030061001210603102d110a03850048204007411304110f40003803606609005c0150703516a040040c00400c5014100310342480e45a4514a400101c035441d034080894561004200e5140c01c0f10300030040000c2840c3c504018600b90002008000014101e460700c061100c1e401d0041c54828071044018200960030a04a8241410500c1c040d16481c0100580070450502048200380005100d44111a040e00990b00b07068560f031007540d07140c10040200404d100e05c6a20880140d507020904004508076031208016004200203110703040e5003ca405200d5644042c1c02804160b507604c0740083d60910751003400d665010f401005c59001d015021000300184041c922050786a40c0640155050701d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 29001840 1250 29000590 29000599
    0x80d06060503060a1205030d020f0d050a0b1215011a09060309030d0e0a150515030a0303091104021305091506040f0503060f010e180106050a030c0302130504080414011e05030402 78
    0x41e150340d0000c0c00040082c0c1d00070826801007040c96000d03500c54000d0b0ac00c44c0071100f10700b801c00e10880032403070581d542101c484403515134800c0303000414030b070100403543c24610b00001044440d010104044040d14103004001c5403c1032820140c0d1568401c000b00c44410001400791510b1342020001d20341c2e00d4004000c000704107805c0815440c0341c16000100021758541241802e03640e001e40e881c1c41c0d0010440035141100040165201500944041180c104407610a9400282ca450942481030f106016810060300c1a4010009591038000c0030b0024825100200c5200401c0d840e661504040c43e120408800d400102c082000601202d0a02c104011220207506884ac40c2d5280391480142c032400b40034107140c802801010444106d05000329000011110700001509902c030b03030015080755050341c021945152034007014021820a61103802d00c1e42002442406107042a9a9103c150301550140c00140940d0a00c8408140e2141c50003000b00101010710b02e066022007000288207610880703003030307004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 29003090 1250 29001840 29001859
    0xa0801031205120a0f060e04030206040308100501050703080613051f060302070807060b030a0203010608101104050a050607030309060c0309020102011a0a14060d050a020403031202030c030105010507080d0606050306 94
    0x40d000c0c0040758a85024501c0d0300c10707507607101c0130f01c10000c02a44a040a6080d903414000c10110718465010380117038041c0c0c0080405103400c2c130b0000e100b000001c100207803c5015000410076640c0000640d4503071985820055000d665407004580c1e41d520b4a204054442d003040c043c0281d00a1281100c1000c6034007170ba004041075142d11055042c0d00c140c0c400201950020440040801c61a611034480003900500b070b00c0112005800090039108180c00c12211030700034800b007245814061003032504c0c00e4100000c02d41410f1a140020710485002d204041c0217060000c1e0101c1010f120b507214545d0968031100400901d511503600034001c20340c40c0c4049001d03629000d0641051118403001004041e00140990071080c18240b000c0d250910b4040c803d070301710a00317001411042140f402018403a458002c00141c03201e00d0750070004c0055500381d5882d01034034810400e202c014480141100e043d83d03400e080c2a0b40d12081c0c0c1c544440d49210304100e514102d4980384001c2200d0b80d0207002140544011500c2180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 29004340 1250 29003090 29003123
    0x6050a031e1514060702060f0d11030702070f080a12050f040e0402040c05032a07020d0b040203070f0f0902030c0c240a02041d061903080301260309010e04060b0a080103 74
    0x7034400c0305506240d004c50300f4072000b001850301c000181412081000171500f400e450040d10019074044613a00c0980844c04010081c10a0381045000f0080890700c41c503800652421b60b115855003125440505042800800728460500a9080718103021411091036900e940d0740f03009003039440059034228440e50400843c0c41d41544500e06507400b0714603603003122144c44080c91a080b40744540d00001700490406000440c0965144100900c40301c0c05041800300c6440d0500c10581805036035000709a040c0d008440a1103101c540ca550001620800000180c2d6902c4801b040b0b8207a01458441c0c0d565803140042400c08401e49000750003200f17003507041304141c0b0b45403d45498103034096130045400c80085ca200e03601000c01000b03500f0f0b400c4440030b04407020190b4150784032804000c0c1500181ca502c10008010000003141e039001119084928032030500396142140c08a8503803240c030a9942c1040311540c06000103641c1d90b0300000082c0001c000c00340d0f503004031820103840504248410303111400500300e070310b6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 29005590 1250 29004340 29004359
    0x15030c03060501210809040504060605061606050603120a030e030409050109020909070e060901050921070311010302161103010615020a020a0b03010503060117030c03030106050d0f0c02030406050a031e15 89
    0x44d4015401511642040482400e100080c00c000307201f40c40c520348445000803203480e075100804000d440e0f40f07038480a03041c180c11700f6000c0d64400307081030f80030f030780032000d0800100000001d40d904001c0910380440d22030740e01c1d01c0b203070302d94002c54014500c0f1515100000460801907402082c0e4408140c800503440c1c0d440080c20f66009070341a1895411141c03c008002840d071050300280480c5400915000300085908025219112000303124009507004400038418400a016071083c045002d20b000e600d44034543c5502c1d03159418409001b040301c1080b000a94a40d60203400440203000e183c50101d06010b5182c0e4001c0d50f032060f46100740e0080428120115400c1d51704401c60b0b040c0e0f80045c00030203440c0d28100c5d4984d85902900c0e5250f1103404240117209443d101440214003c0c0340981d640341d25002d141c0c5000085136180045403103106d28000e011986190044140d800b16001c5081941d158a10204250302501889808503028624100411b11101c0d50f80d004040c5451107071140d01c2c03103544480504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 29006840 1250 29005590 29005649
    0x609070804020303220f03030c0308130f080904090f0b15010206010e010510020a06180c0902070f0b060303210106180e04080d060803071a150f0415030c03060501 71
    0x1e0f4040d00108041c11603000040b440d040004001036585050319a584212080350b660750700304400080c90003440d4030516502c000010380114075072682c45d45c00c00a99461100616405400818841d00420200d40c0c80e910f590001c6140d40d004481c142e5800401c0c5400b200c110030481c1c1c424902c403007455000030700303510008026041e54203580003609243d0802c4204290188411a07450862040881d80c1e03000420394010809034101000f202c10000126113007001500e0900c1c1c10040c041032042c007124010039505e810742c059141e00254440d4a80e2076a078042404d5214000306506005007184881d110020311000c1113040305e040782e5940201c80d10b0a401c0d19141c1a80340b18094540c00e0000220b0041151000100785003454007100141c45079450030f5050560704085402c0d00c40c25030301d8100c2c1180c007d024006590000c411000c0e40c60b80345c00100061040745070002000e00441e5501440294203d044032444040c50700403440700310b01d80e920715040019000034000c40020940000e9907041036020401d0306e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 29008090 1250 29006840 29006843
    0xb0901060906060f0c0f0219030b0109200304110103020903150105040509030304030c080903031c090218130303020c0a0816060e0d05040512120c0a0201030b0303130302062b050609070804 82
    0x20746a040009440f0400e5000c01c5d80740c142d038400070300f0702c0400b0000c000344230140041d4410300661142e5807610000c40102c1d02000310000e006040c141d42504035074140d200722540198003d40710103a541b00540120300074011600c10b25058814005866810b101c01c80d50107040340c1003220300344082c0d5201c240090b18ad00040d50001c01147c0d001c0115000121407001504800c90040c040f00d0400942100d525414050754101c082c4540d42c0c0c034004010340c1040342c42c2c0c8416070203981e144441820f100070510500030344d036000a810554040381c0146020014054181c1da2038021901c5905d80b00840e2041801001c40e4030121041460305440c0750880c0808908039450750341c0c644541d41440d05d000d040c0100f54084446151640c01407044601c0d0011910024241090f003820061035240c40c1807001500701d5048030701440c0319500c284845142200e03e5600881940e60554050340c0345c1c0010b20b139007050014502010081d0201540241c1ca100600c0c2e40007520910080360b000f8502d40f107480c1c3c10360341c10f0400d490 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 29009340 1250 29008090 29008097
    0x1e02090f0a0209040603060c020d0215180f06100e010e06010e01080903090306010b19020102040b0306010e060705010f021801051204120c0506040606030b180304030b060402070b0901060906060f 85
    0x9008003000040d000c1e842050803002501e04800da00c001012143d094000300c442681d145008018185d040014103503000c8540014558500c00030345001340f400005051080115004100c0ea1100d441440710f034445c00312607011145a0b04007000d07070129040303c0d0300451400d0001440000f8074000990541c034000c1134182c4032000e0741c00d030600044a070040000c120f410369210411048046482c2001028000c0560b041d500d034031141001d604214084440e0840011603006010511005640004894110301c0074200401c0c240d01c1100400d80718080d28034052301a51810780151400d0384c0ea6002451800c1000c0c00349034040e04600015126802210707000548076400e000000d0014a145208100d0107a42d0305045000700c2c43c0d039449030701e002e03012a01150741607100e050400821601d81003231500415002080c00b8000010703401c4c1d90340d81c0182c0c440500440724000100d2100d84403981204c0e0480e400c090708007080e1070081d8034103000c0d18071841004030251800200094051250b26802442e1ba02c5a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 29010590 1250 29009340 29009359
    0x30609070c080706050606041203030e010b030307051203060409171c1b1809020f0909010503010c0c1b0504060303021b010f0e0d02040e06041a1609060f02010b1c1e02 73
    0x120740c13400400c001800319400c04410000032949102110740c01e24032601c295408150944079a515900f5601d540600c01d009920500000e0000380c00440c80b50102854805181e4590b5507141c0060043c0a00c603102900c0034403500c202451190084000f0112a07106603483e01802001d0030b440700880d42502d4800700d42c10804411007441c2c52007a580501d00d900d409e008044520b40343e1100030100d900807000c0d181f15090008483d03100e42040140700303004110480003000310030001c9902810303a00712050b0003084a44400c001d070042c001001001d0000e0318014104102403926460b000e996449048220405403002c13080d440300702d42c4181100c03028500c20340e0707409244001020601c00702000000d8205d0b070040d01d13481074241200c010085544504c2c01452110168060941c800b440707114050286000f071500110b1b54050550819090400c43d5014036100c0200703036801504030300500c80c0300103c640c882480120075200c0e42001900210301e90040350850007401c60385800c04da8001e50188000d40091250 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 29011840 1250 29010590 29010593
    0x3010f06050703020c0901060302040509010806100612090b041109090c0303090d020d08031e07020703050d0509030c030f010e0c060903100b0d060f060303030b040203191104030602040b030609070c0807 88
    0xe20207051118402c4c01102e005015900004040c0daa090700a500000d601040411151402d4035250b40141420000303802141480c90b1081100031f030710700800b81072150301018500100d4440e4041e400e640d0304207104000509040c07030420401d030304103900640708085400104801d400e02081c2c0da19400002402185011019424480b5610503407030240c2c1c2c001a900c0d07000300880c114400951007001580c2a202e540d28074650004145980034140008643c403d07a41480082d00019650103000d4071410714a072201034101c0000d00c0c0c00c001c02252074140c0142c000048480405401601c120301641c2c0c26240d08801103014081d560080e0341d12281e040d4030a86100007440c0c1268400d10780118044c01110590003181c50710f0302031381c00803850003c2c1d850381d0f44020810b0592601c02c02080510498082d0304d10300300075984807403482d4221520341e22540d9404540003913804030000c65000715403000056441c1c954540c0c000515800c01c030780c0580079501c1c600008801e40d110310903c010040c0c2c0b2948090401919 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 29013090 1250 29011840 29011847
    0x11409150105012001020c0102030912070b0a0f060b07121b110d050102090306070504090b04020406121a1302030f180601181d030315010306050f1203070609050a03021203010f06 78
    0x102070613800407a03612001a0300441c002e0008010803140c00e0000359072801c01c030790254508200350078405690701d0240b104100103a4580c07d11a0031a001c0503003c00c54000641d54200205140d51041d001702c02c0004103101000320120107000401c103251541a0b0140401d002c1601e845040000249100080b011aa000e4035041c05454016800f420006081191000100c2d02e00001602c10801280001c141002040e06078055a80f10510580d170650801c1e240540203080c514000c12082c0d2002e03142c1840b18070b041e81e601c2d51a020f040c001050952f04104040a040c001e60054905065103050f1314001210200e8079918103c4ca40c0000c00200981d070f292194000f100b40060b03021410042e01c8a0312100706800c400f000c4070444850340c000c2c0d03923642007041d180400c04039480019418503003000c40822503a0b0728207984a03904e035019a0101c8a46030030007001030940c400c900700200300c03c1c03034040c041050010006000c285140310350200c8983d4030401c080d44c1031501003442100300c1d00c8103009050202510 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 29014340 1250 29013090 29013107
    0x50a0209100f120516080901090203010c080109060602010c050a0507030c0605071116030f20060409020406031a130c0c06020c030403150515040902030f060a0b0312040305030a05030709090e01140915010501 90
    0x300100009c0c680459500080c203480308003c1680001d40420018086c864070303449100d00030b2440f80020800940c0050f4003030010700071484503209008010400005060242e802c40c007046920403010442031529603005403d07070f850307a07401c1c1d90f01348152040300c035807080013150b40f006580d0012001c140b0071980d5035070581d40c403940184000c0e0840c0401c003140a5900c0360340c00f810140c4080c8030f02603151030810000904175071481b800c80307120300c6855440384007076240d08031007070140c540e070308808201480030200076283d00c001180e004011501c0012801705604000c40604180d03486805001c8081040a03000340c29104141e802e0038000740e01240c207030540e19042d40b1080c103c0f403001d015201c038046a111440e061400c00c484a550a90300c03403c409610307160510401c1c021104210200e07082c41e096450341962401681d4002c414400000042440d080c014651200207081a4005020380726003416111702809240e58001045031074480413500520f4049000b0400c403181c21220300303d0340e10700001100c6160 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 29015590 1250 29014340 29014351
    0x50405070306051017010b040b01031404020105030c040b04120506010503060c16110907020c0a270b010c02060a030608010501050402031306240e060a05030a05060a050a0209100f12051608 82
    0x901c506000906071010342060f401c24940c0170001600e186214140016509040c0000c1e040518004103011021485d10049400580a1a1241e2a90b5480344c00c00d01074440c130341140c8100c54001c100042c54480728140d80c0c243e02d00c42c078141ca4050340e030b8505240c1e554009840d6044445000d0041109051281118042240c0180008801900d19101003400524251070308070044e00000200c4205007001c01d010001400000603014810190341240815401000c1505040e145c0b11110070541360301c40c120390320301030740c004081310f591300c00050014001b40910301c5000210350034440001064903207482501c0c41010310300c1ca00a6480a640e80e0200101005125111016607004070b0060321083c04100c0e4001d890000b5046103a41405800c0042c012103a0740814829400342950324002000818519004844128003040580703500400300302078050000c40f9908a8105001c03c9035542d0700044451209505407180d0b02032885410b0350406446084407800b001400403454039210728441c0d01c881c0e6100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 29016840 1250 29015590 29015611
    0x111003140c090613030311070b0c28120503070908010207030e04051314010b010e030f03191103030c0406030b0a06020c0f01030204030b09010516090f0302060f0c01050108030301090e0105040507030605 88
    0x9091350070011115091382013a070010346485000c00014008102040140041082e85404c1210140a0719a50305020307460000c441e112200845e514600f07200204100da80c04500400440c00b6414001c1250b0011606840003901a500000da440010f10807035400d50b80540d43c070b07a0091000d1007400b0140101a00070b4130046803548050f00403030460700d02108403421180c00840d500414000040100c00e248020350302c030783c2100c0800c2042103070000407907550b00381c0c3d0700a50607801c59001c000d41c1c0401901c101d0700e081e07010000801c213000c0c3c01d800040c003d9452a07241004640342c01401d12181420b1800f407040940c4c4036440c1c0481c4d034504a02503805020b8149405031400361203030745100890b0019100165661745490500c032244001031300982c0c012000740b4004800c1442c00c002600c52860780d12000e4040e88000902000340301980d0203c1d001400b086000780125652a5429590307503209100d00c40304145451550300e91200b044c01072a014942040c010320b00c983c2503458090003000d000d000301041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 29018090 1250 29016840 29016847
    0xf060108010e0702160b0414030309060405040b1c050a03080106020a150203060d020310050720030f0702040b04090f0203070501021f020f2503090509040f0f0201020c03010603111003140c0906 84
    0x120007082c409440a011110519174865103008c0010f211b0303c0d0302452092290304144501c00b880c0d250401a1411502c04503008241604c500011410350400b180e90f01d20741d1440102c81000f40100042c3c1210214400d50b00c682444e81d850600301d8441c490100000e0050951200d1100c003a0b02c5a0091900400024820380060042d0350009290a02c1c0581445806d038654080101994014840302ea0072034511040b0104a28011180c1e80c8074410b0f071451b03960400c4080307000e0055456130b0380501c5181e540a0710400180c071503801c000781c190b00700010480c440c0c0719002c000304855201098076407a00118602c80303041100700b071110901a42092000e90590750050200c2d40740401410140303060780d8900541001c074482d140c18020304680b0329811044c081c00c00d4400307001c0001c620000c0c0804031038101c4610900303c400c2c1e03c0105c0c101030014042e40e900d0340c01c0140200a100e8111500285011704842e50350101510290036000c0e14181414641c44084080c00182005181c10080c040a84018042840c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 29019340 1250 29018090 29018113
    0x5070f03031104080106030506010b09030d0815060f07021e0d0b040f05031c0f0b0a090902010903050319020c180c0f0c0717010e070f120c0906090209090f060108010e0702 75
    0x71a402c19441401c44d69181c070001c1060083c10b00c40765000d061741000061400207520040f95407066a40204000c01c20740e031000440e4594140b5100c00020001031200b581c4000710309001345103402510741070784500034100039210315203803050000200300d0700a0301004003543d86032a841d4268000a0090714100d164109010004405100a0004142a00b2123a0010001c1c03598041140d01c05511511024507101900149648007000001143c2c03010801040340c1d195440100c0340e15902e039000414610012910041102c006964248000780070360072550401d0852040000b1011104400071a4042c504081080c602d4a80000d0400800040c2c100e403520744900c844a15003445a0700440c075004280c0704119000c2000e0281503510f0740f88000a054050504183d005520841e2103556808090500043d00700b00c200c024100003000d4800c0104071080e55005090060741c400e604d014070079080384c0e002950318154103415a00440d01039448124a81c00c1c08007108420313001815410961190340071001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 29020590 1250 29019340 29019371
    0x513090206160b0708010b07060c02031306120f060e0103020d0f12030903080115170a090b0103050601050a050d050705090c0d0c09050310020901052d120f0709050105070f0303 77
    0x10b1540c9202819021420711801c1c5031200c008003801c220100700345540100700303446a010a662405130070081c00912121644d07001d0f0301d5880b520104c0880714000c2c04002030b07000e030041481e801901541406200b0220101030346022204940100600041a0741c0103001604050202d51111407150f03e000043e03455907100c0c0c00c0320320360016564001948804000c0c0400d94017084150040402c6041e860515141060240000303040c000ea02e0400c9000e4000104421401d030010000c154002048040300c1d6100d040c050380f0b9040074080d090050450745400690390401c2c0700711000c07154005000e003515a0409003040506070380901020b004520a0129482c0d000d05131040f049807500316180c22041b245000145030502003207603103501d076152061080c0e002590f000302c100c8803c40810f54030600c2c01d1130030503c900802000345240d4200f0301c9010810308c4030451000100c50145030200b2201003580c1d140202107a4040301400380f0350015005101510004411501705050345102e402d020030b0003d1842200e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 29021840 1250 29020590 29020597
    0x20a0b0a020304051201060812120a091506030302010209031209090703050402010306031505061306150503040c030b010e04060b0901030804050d0c0509092d060103142b0f020105010f0513090206 85
    0x141c0540c1d541c1c500030004038030108509c4060001c404421420160410085143c00d00020059904581c945648004001c2000c46240c2c1ca0111128108109074803030500038002c1d0018a81d907400f0303100f102060400500c030601614200000244800c0741c80d91400c50440150801501c220305058644c900031001859050181c802021240d50010381442c00304100300f40386030505911000d10b450088103106504071840030384810708541c100559a034445161044284000c1c1e8400380003003078a0700c000b0601c0d01c8401409805140030340010300850040000700041d0003c2880001e0280c00c0400041005041018000c3d410324019000e00c0f8a6030358407030102d618504100c0380d00107d074100808074041c50540c114041903030714119540517001d8400c40680c5543e10410700001d80074001e011000c00c0100000c200550001c0340a1702051040c4141e0850880ba441042030070b2808641c1041160310346030720512a49048640c90052045060711704030910000509001c071040603070740c0b40c52000016858a0307009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 29023090 1250 29021840 29021869
    0x110708030f0901260c0702031c08010608070306060e01080601030e0d02060106120207080403170403050a12030621060c030b0306011701050702030f270306041209090603020a0b0a02030405 82
    0x4036030b6a407180000401002d00c0e4030341c40b206003804c6000e00f450031041d01c40f0710b90301c03003c40c2d19420340c0c403812400040c0c07800c01034034140081500344000d1103c0d55544001914101d4407181c8072a411910707110400e5050310081e000d50700c0010040c64a42045601c45e5041c00d03003044040c1000107005203020001c038100410941e0660150b4441d10040240035404803801c400c1001c205170443c100803179541d40307010611652001904403044003000c5490803042d082141c0c02558080300700c60084209284c60102d40000b24803c002080c54448006040e144650760900031005116162801c0c1c0407a54443e402400124204010503941c2c00d201800b0780c608200160180001009a101d0034100382109420344000500040c01c5420501047d9001000b1100b5102542c00305100cd461009144d0204810f02c01d0158010740e0501c40c2c1820300040c42418018924440c1055941022098072600d0480c21f40303546110094001605200801c42c00c0c84500151041d51a984103403403070680d4072400120543c04000a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 29024340 1250 29023090 29023117
    0x3151b07120806010206060a0e0f040c0506040905010806060a030f2a0b0d2a08060d0206070602071112070e0c0c01020a0207140a031104020c01060305010e030403060b030c09040311070803 82
    0x2888404e43c0c042000c20340c424011949103a00380d0411610154000e005000c900903148500b011030700700b20f00b6507814005041c020340b00341d442c1c540e40c50005024220a03c07417242079000b400041062400e00c0051041070340d40100c00e140c0d46403070558a908490f4002000c00c80c003e584848222400551016001c004118941c0620789400325018064100d6100e4100c01c1c240d401c241030001c508018060802c00e00384c0035070502d00442c0d510303071002c100191403c520003940054001040303c100314080c0e016002840c082c29103804003942d22010300c16480101403802c1d00d00d91101030308010428074205415400401c48848d6400d00d100c0b070701000d080e40c100000850150b0404103044c414456500c101640c90042100c0c0c041e03586165440320444a514580124012600001d00d0024804250080c800a6a00c03c0003000119070769021280c603a041808103c90007810200031140d54a0001050014000001c0421a40c0d40710350b0340540740c00d4002c0011103003602031410000f98202d414005445019810407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 29025590 1250 29024340 29024357
    0x30106090302011b030f05220905040b090f070909030309020301050c03040201020609030a050d0b010c0c0306020c07080a05060c090a0f030c0e070c0c030209150a0306020703030b03151b0712 83
    0x10014064002c0034610115050b80580c012010a40c4010b160f0303150041b50400c550703241c80040108a004420403c1108031204500e4002140d44440c0e100702c0c421401341207154580d880d0301c800d1945074580c00e580031040394084503040c400c01095502100c60310f031017414005030365072180d401710b030039100c0442e600502d8001c00700800080d56018000d4940c40200000610300d0304605e0b4401503c0ca01410315002080d0340e540810601eaa4007502c610b00c14260007188028003c0e683e850040080e6110201c21015402070480000d002080080c00e000804e5114000c2d2070b00e9a5400001d01464100d03481c1140d120341e01e0000000c4120250070319101450240d01010540c0742080d94106890b01c0242c803440c00c02000b01c0c00c00c00880c01c0810130748192039049403114080c0d01e6240c9550142c0c0120104240d000561070b41c004200040c50780188541403003031f101488181c408000701925074520024280100e00500e0000d50f2403049410b480200403800a2014108032990712054651280442000301048060307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 29026840 1250 29025590 29025593
    0x20312030a05100303021203132a05030a03020303011205031b011401050901060f0c0809041a09060a05090c090112050403051e0301060c03031505030f060a0f0b0607030e010309080301060903 83
    0x103008240e840362403d615405454a15a402561840d020519407003661010010441317030b08000b00c02c0c811030b90304802e100c290f01f032400d440804890741d480103505064800610002e00c608002c541c1c002e80c02d4054001d10300311380ca011804074811038003082c11107803030104001e015005240c1c20100d070861810100005154084419000e041507010381100f8850164900104201d5a00908002502c6001c0ca400e0700298054502002c490188010481d4040d04021294000411400c0d02e039030700403c2101c10985640321482404100c244c0c41c02103039045000c0c1130020310f0048507400200303001c040602d030001c0103040c0031010341c4c2180c4058400300c0c001800016901568407082c40c03500003680c0b0000440703145500d0194081c101c1c10380c0c13200040505d038803074400320b80785592100104000e11340501507641c1441d446500300d8686031704442d13510010345084040c00480c1d11621480284a00c0500660b20b071190549041d10358501242400341019109c10150002800c014051402080349496514000e400c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 29028090 1250 29026840 29026861
    0x90611040314010b060702040c024306020304030f08040801090b060906010801150f030b060c060702060a020307020d080423030c07060507080921121806130603020307090302031203 79
    0x614075003807410f038149060045960740d0f000032a54103c1c2c0c110f4000913417190312941a404d100d040f8044160781180c140308031b601100e01e1400c2c07074107160480b80c00308408409025101009500c500400c80181d106001c180006441050980b40d580c4c06005000e0422703994440b11400d5a0405004440081d82c1f40309000e05810004070741d54001500b420840b00c1903041c6240d400780200c002c2d607207a0400c0341c44000507000303034000e500c807034048000541241c0c0d0351044110f08555030481503458900500c00c000c0010380e40c01c154800d60f4080c600700e5000d00604401d07004211410700000d001a01d0300142003540c0c202c4040c4600c91588401c0c460005540c40321040c68401c0d00313003401c0d0351082041c0a010080c6100007000c4108890440a0032070f45a002c140240c0c031000101a00440b81c120740e80304240d045030440790520b01034040c080c1d281000c2c0d03403650440030030311446010380361405124819007202032202c00d000f90061503101c0501e1900301a066542d8001a1400c010601c0c21001e0020020912502421 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 29029340 1250 29028090 29028113
    0x3020112090201020d1215090905060108160306020708040506031003110612060405090102121e100e04030809010b0301110405040b040501320a090b09060312090103090203010906110403 81
    0x100410104080ca2075078002039141c0100d5a003980800c00314a8519112044690140182e1140120340716403040e101c180041c01001c2d4244290342c248074080c0006186040094142c0300541215600e00b910b525568071400a900070800441c0c5c070040501c4007007440e4548a0186200d0708a210b83d000d0210301c0c0d0b040c064650408104664000c034410450140b00359030007252181c01c4002900e00043c0da0391581c80b0307a030080c000c10f6111482d00030000300b4040300305008160107107010781003000002d041c0c403550031402c0c0c0c004591050301d490054010000f40403900502c00161f011090341e00210f9500040e500003800c40303203000c1070fa400500000c80c00b0320003420a0302c9003440e042701c180c50412465040c1010f802070880c00d02141c8507044000d0421540c2c100c0d03110b09092103880e02400000d146900d808488005c1c06400000c2805581000c00003041c80c5000509910b07000c0ea43d501d06440d06035400011030207007107546010782c0c0564031281c00b880055503d100f990080d0080010b07503500c543c1103140c0030741f0509 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 29030590 1250 29029340 29029367
    0x6020606150c0a0501090c0806070503010501080c070c0513060303030b0a03050a080a050915070618031b1e080301050a0b09100e120d0905120f060c090307030b0a06030201 75
    0x14018010040541c940240d40c24104041d80300d0941c5814500e079400c0e20300354600e00000c15550078400010104901d81014005860826050350000d9403065001c403a10b020911605000400c68004140608035450050407154003400440c0c43e06034641f40410907900984562042e403c2d940d1108109055061180c00d04034901120f000c015135140d91521980c1d00510800a0f00740782c030014090944600960440b0350420024080c454020b01488501e00250002c40081d640329040140c006209105030b500c80410740e03410340300e00a4000740b840142d00c51111a840445040c07044030310f80c2d4143c955249000c00d01314400c603d155542e41c1000c080c000c0c10103060b40306500f6a401442880119642c2e4a04016000c0e101e24100d0440750b2a0030004501615a910070941402210071484110f85e0003c000c2c015100c007038410303d4454035415002c0b40d40e20144040ca81641d04000c01041c0340d4003040d002404800c00040c111500603481e9182c0140803030081c0c0d83c0e000c50a0341e60344e08004650304012803000d000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 29031840 1250 29030590 29030593
    0x7020c04110901050c070e19050109021e0a02010f0203040c06020d170703050c0403081606050c0c071202040e07060e0307150806090603010e030c010f110a051204081905090103060602 80
    0x2045404070025450040301001410301a0110f5001015502044028000d11400c1240c5140341003104807403c5448001010314400341c20f0100108005400e4001c036110024012001d410810000b640b491043c0c0107182c903601107540315403003410030a0032400910f0040f80103c030aa544181b8184000c1d1500f2480119002804102c520705011088849403140c2e1081080c1408604d0390ba625503052012301c10390300014000000442c2c00300d2140080303645000d80740d114032010480703921164541da085000e061044a181e0b400300d10f040c00707000303000021000a41d01c068030120328080030032400740c1841e016400c44400104240d0b0001038624040080c00c1c0240440242c6d0072034450981030003402c142c00200700502840416000c24020389003540301c244040c0c070300020380741c550310803100b041c0c06412074000302400f09051010302040640c54004440f198000394840c0742c5001101031031411840001881507030208024840429409241d100c580c420058079580d150391955107600150032911290005003c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 29033090 1250 29031840 29031851
    0x204050a090f060f060c03050a0306050a080607021e03040303050d150b07030225030308061305010f060e030f0613110607060905060901050f0c0708040f0605030106090e070f030203040203030904110307020c04 91
    0x5e29030480300000485400d80b6082c0c1e668013026130194041e003001d034002c0d90000f01400c000a8840400300345540205059426100c00030110210030040d0010240e1080c013a40041000700700290095000f0001d00c0e01502d00403c806200300300c02c400038841580095042280020750104047e070503c030f0b9003010404d20f500000b0f41ca142803103c0134a034a442c040201448100004940250b40c0d000003a003810030584800e01580d81c41b040080015140344c4500404240100d14080302490003090300d6203401c4089000341115510480c0c1144843c116000c11b4945074001c90803041d0b151942802422454064480410130a41d245001c2d403501600500c10607a0303034504000e014800e000c00c1c520f0364214035880007070390712140a410560f05622459000013140c400a18001035065001000b550403255161203041099565504c2441000c1080781d940f40042c0940080c2e800c4213010380c0c09035402070300103405c0701e0a14860b0310124040301c15645c1c10380c1c058000442002107640e410002e06e08ad045043c0c0d000d00c007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 29034340 1250 29033090 29033099
    0x4060308090a081902040903030906150f080303010e0c13081b090a0504020f040f0b030a0b042609060a0e1305040b01090903051803011413050106170303130201030204050a090f060f 79
    0x64100105030080c403880d07c6880320780906220750095001150840740070029003000e040c60031f144004500c541c58202d80749800c0000e00000220550b4101e5803003001c00c0b055643d4004444500e40e11030080381e4000c600700d00c0c0104503c8400c128111007200100d0454142846d024104070758031000801461001342002c08220041e22410b0b0302d60110340303040e50003240090640b01702e20042c01c001503040f5007500c150103409040c8504860000e01842c02040c51b100c120800107554044c551151b031221880090070003a03040c0a0030820000c100100e59440c0910003a92100c00080304d44010220b610005610f41c002c0c401071007002e031180c3c0d00400b06000e0401042e42c2e10f03a005001401074140154a00714001112022030320207401400c442000c40c239540c405841d0550840311584a1940c094400d03605e450004030703155052140c2500f07240131090056045030340d1051104d90043d2041400c9041523001e200c0090103440e404050000b4140c410000703d11422643c89260440e080c550200340b030000510410031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 29035590 1250 29034340 29034373
    0x40305030d1b0f0f050d140f150105030403111203040b0a0605031b010305130602030106020d0e010314010e04030c05030d09110f06070b1e0c1b0a0506190b04060308090a08 75
    0x1100c202041c00c08540d04c1d0801c600c261864020024a08001c40c2070002d0070301110140b4420a101c0c4d95500c00e110036545544200724501030b66980c80d14007007402007000c9004039008112400c21007429801300c81e510000d0710801011a0401e8800b10f5420004a080c000880000c0c09103002400f000c0c2c0041043c00d00b01044407041002c039008482c141981d541c0414140794200080b144000c2e0041e109550700e50359910002d41d030b90b000c0d02c624000290042011465580300780a050748181030500c80d20116401d000008a00202c060400c80602a00e001e2880018000344041e10710480401d40001c0c10881504010340c1075240c810743c1c81e102d1440101260b4081c0d5860096568550700440003030100d0340d9511a4911646110b029030613114004010400e2550b490f4000307014410009a110b5494040c0512032a628101d0240061254110b080002c44d00c403500c0710324002149030500046061198030300801c040359403a80045da02c41c4400554903115013000325040c4006d020020040140b00071717250003038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 29036840 1250 29035590 29035607
    0x1e061706090a0b0a03020402040303050403020108101d06061207020105010501090501020303190e070305030304060b01031a10050903010209090c04030614090a080f07080a03060f0803041a09040908040305030d1b 92
    0x103410594490300b60301c1c3d42c0c85050721103000e168040e10455886441c0e081c06441c61300b040c4801ca001694500c0050003514602130418202d0309a80043c81110807400304003912040300802040d040720b802c9c80b11a88040044440341c3c015445030f00001000c0d41031100051030600190056070641d0b0040050200580346d09407181600b101030800001e1310350180138118100216a4800f400c50301c004002e03c03080c441a640b00501c41e03c002d0b241000701d0000014a940040e0f80e550107a40c3c40042c03488148a00ea010310000d003c0c0c5040200014038090a03440014580710b41500c415a044c0f4020400340104000ca1051445040111149054074039040760f15a0703aa07450700308010203240d004540090101d1880c01910801680701e0813150301c84003009002001000d030303440340030300e08003140da0001210030010003281e055820601141542880d0700742c807030700640c2c0400c0d1103d8011765200754070b07c0031a07000e10103880550311034400741d07543c0c501c40e640d500141c800444200c0541c41d0b0174607107000d0b41900010030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 29038090 1250 29036840 29036851
    0xe030903061812030f07020712020303031f090204060914010c0b0c07060f1407032009040207050c040203091c02010605060a03090302010b0405071709070621061e06170609 75
    0x48407280c004518815083c14441098040c2048010040c02629002000e2142c410b09440c0e0899807010b03558001a6196010210040c0d003640041000c07a96940540c9103c17a26010f03040201001940e491100700100d9001d50f001da0700058521905011440c1d01d404902a115402d00e012030303030341016450358111000041e000498040000403008104107030f5411015001411000420896a1030600b4020114007221041c0020349400c0d070054864032280c0401280452035040a428a0b0b8110b00703000081d400b1307100c152100d01c128078140c52195168001544292102d001402e2020308084210f04111116400fa20541e41008000c0c0045c0c1c4460041d035401c0c511602c0d001c0342c2840c0d0fa04043c1c5c01818401d01c0c1e00e800070305201c2007009854020002c50031554071094680881da4404211685030b00b00b0f0b02030000040d0050081400c82c640c154583c1c0d80d8180c50100001b12195078580c01c1d03148061842c1044140800e2400800003070b82c1018910f24082c0c0503c1c081450703850500300160796074200404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 29039340 1250 29038090 29038111
    0x1103040c12060902060a200a050304050d0203030c0106080304061106070203030c16020909070612061203030b1804030e1002010903080c0a090b04090e0c0d03020a060903032903010e03090306 83
    0x9606002140d0000f50f03103a0340150100d0b541e841500e20062191034100024000d51015076503645600364001002000580c12101650034181020108840380440c602c050313074140301c14070040c08005401e04c1103100419010008690791032030b0500203050781144118000b50b0740c0246003040503040e008000c0b070350b01c00300845165036150418008015807960300c0380301039040260581002003031680094080184d44036034589114460321200c0d8030040e141d260054441d1104000030102c0020300941105030901001071601c80207040c81c030140f0100300d40843e420390005948a129500b241089088026154000c0c030091201840d1078802900381c44002c0c1c09202e00c8580006c1841c0841d1142103950068030340d29000079a12a03491300c8100141c40c00c2d45028805006043c0130700c3c0e80d0715043e0b07018400298960080c00d0f6046094840d080103040520080d03050584444903100b140030138142a19800400c4841c0c5000c012001040c14212074050242d000701d507200304003150660ba00010720980c0000c0e100c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 29040590 1250 29039340 29039369
    0x80402040e0109030801030311010207110d03020102040312030c17010b1c02091809010606020a0b07030510050d030309050105070f230d110409050c13060806010e130c031103040c 78
    0x2020800821260414007071a52030720114408150f403100c0664100c9001e135888a01182c8611003203800c0344603041e0002c0401d03025040c030b04a14108881e1115015000740001805c0c151b483e2148201020005284000a6520414140000e0b08010114500640004d200140b90f0410000c0740d001d205a680060f440303803064050350a00d038099011506003410140684d112072090941a10701c032a8140c88940c1c00b9401c3c1207021820f10310005022140942042c80c0e61441d89038080154014080901000444000c688010909846407100c0d040064420f5400043d82986400c01c031703003111005001030041000310345054005540c4800600e810403c1e003411208003241410500c5600d210f41400580013504107500c41070440b50b484041e10440c0e40c0d000041c0300c60b40e00e4440e5903c03e84600c2c001d15281070b079048002c1c4031031481038a40562100049c1024118100b0800005200c0c805071109042059100c006140940340e060041c901001c0031040d0302d07419401c15995082e403550040c0038900f00914801d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 29041840 1250 29040590 29040593
    0xa0806010c021504151412060603041406040b0a1b0e060f090409080c0f0a0308070305090a0b040503130905040f0605040f0b010803070b060d0201090611250806060a0303020c010804 79
    0x43e0402d2030030380c4812803280c0c4c0d4a6540c0000c1c103140c6444070007407012a000001d070454104162084a1b402c0c074400701a00c419a48120800c500c942005d00b069401c17080400c850741d101e06040010078081c41c05400401c2139407502403648401d503540c0402c1c80301c04484150610603810b070050407680640d00c04a640c13544030001d03100494a98014112050390080c1445010703420b015080005115921401c410356503001ea041c048241d81d003140040080004080e000000c41462280d0301c09030f0031041c0401501c0c1d012502d41c071041503043d0252003e031040d80001400f94809404502e9a800402c0410002d0040b80f410340c940c40c6202d060000060710980d01c0e0400102080100361800a106034400c820f26102e50312032100c145e8a401c8100121050103841003c6121440c1410700c0340341040c1d0580d241700c502400d09400301c507442d600d940701000a01c50f5011750301c0050000c55801800d80480003040c0512351414040f203142c00c901403c194090b40201e0b40500100313034081165092442c003802c1c910100d0f180c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 29043090 1250 29041840 29041849
    0xf0103020706150504150b1210050607031707170a02030403020313060507020310050112020d15020a020c0f060403031e120c050306010215010b071e120c170a0806010c02 74
    0x9081c001009a03207026002c0340c0c082c202c8000c0d64291001510304001981d5910030b654181c403014011035039111030501607a10f151103840403181d480072001e4800130005640740d000c98030540081100320003040717071881c890204030301c4c43c803201e540540f192400c500ca500044c154081565006803103e40001d800200050505008200319050119900005000700380e40b0000188244c0082400720300c240112002002400080d00416060301c4a0b0417050140c46011740c20010030804021044606040c1c3e4248200303110070034030280c2070495550700500381c030f69502000c11034480310b940a0b191103003034284414004030b580000d4101682d50b018007501001d8100c0402901c119081d58401c03224181850102100154000e000d035004000a03001c442c3c5c0320300080c4800f004640240611000740e401442000c000c110f44229030780c25490050a8034030501002d446081700c030754a545507800414011580b91003001402d0044403007000790b9041c201c0c01c002c040b2900510400c006414141000f0301c0c24a000107541e40d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 29044340 1250 29043090 29043097
    0x60f16050c09011e08030301050913050109060c030209041401120b04050a020d03031e060b0a0e1801080a15090f0605180715020d030204050a051504080a060207060b030c0d020f010302 80
    0x40180c0d140d503135504081068a119102c206402009041c000500c110740001034905980c0000c03c070092a070342d210100c60800c0600002a2441e6403500840d5000c1a024032900c2c2241c3e4482e03a001d80d0b140400400e21003656100000c0c1e0b0404400c401c0100640380e0b1003101c00d47c91592111700002240c03a1070070304030318180c0602c0020394007000142c0340104240e0194018140f03080312100902031080c00000c1c031821034000d0310444031520010801c0506071841b400450358450701c010007003440c0c10003044011015090076040380d822541318801c01401e000c07a03454000a080f00354501030105801c2c3d942e544000303101d090340041c4034a45820104040e030828001d03039070400702c4000032171b1412540c0d8403001880030307070342c100001c09401a20024020280304e8000c450594001070144846580f6000c02d22511080c2e168980501e03010030320010821281c103008445a140c0070318005a2140d826081107011241c0c01820702d40300ea8460003e00003903481ba14009401e1540441d42c002e407064038100142c1c064413 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 29045590 1250 29044340 29044363
    0x21308030a020610170a0201030f06170c03010615140304020d0b0708060109080703020901030b070302070c12110406050f01080a02090307030c0e0603030c1c030b040e031206060f1605 80
    0x11030961551680050b1051040462011002035259900180841030b172440710781c000d030398010a46030300c00b55000e0f400000c24188107c81c006626640ca14207034840390180c2d040b0405582000d00c03110b076145402d0040d10081d0059084814051002d544081c4c8180c29000381d01054040200006083d513440303210482006d03401045952051501d0340d0000c01c820310840d201808607100041c0400da1400000341c58098070340c0940382da1020390868450404d007800c0285840c2c1015001c11109000600c800000c0001703107044200364004a48034070b06030f5401948070300080d0050b407401c04100910303030b5440b5900610b16000e0030130781134984822450101900c40c6080981d018410381100004001d0b10240c8481101d8918a00603210340b544010542c403441801c691030095031050310498000d206902450700085014140020030403200d0000c1026184580c031b5891180c2c00c041250840d071500080c00701d40c4078500300c500c14a0042071004101c0140214240003004800701c00e00c034010031000700400281c6c2c0303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 29046840 1250 29045590 29045593
    0xa1107090c0c0501050106110c040207050109050a03050301060201050112021e0406170c03060a0c0915020a021905040e070b030106031a041802011b050604020f03101b0e01080c0403020103021308 85
    0x5180881c0050400a11a03030b048a0941c6440000211944560405502e076401400940a2040f24004200107500410016038003550303640040c1c000207004102e0841d1003840381d00c070251250714104010342101c40c160700a10f120b200c4010000c0069a46010010521000103c0c522164040202040042071f8580208515901d01c11071041c0d040000908291001c8084003215200c0d61040d03124419103500788850f0001c219a804140a140d0440120991440041c412211500310a07000110171070140c040044102410003400c1c402c900b0b060050011041480c0018442c4500d00303181e401c00c0784414440d410405030f07904000c0c6c812441e00320108070200c0300204280b0001c181108000d5400c42500b004a000c2960140041141c80b8141d2004480503000000740425603140c2d024029109402d20070b40c0e0307140c02010840340036041288261000a2001c150030500e2843e408000b8102c401503801c40ca06010040d000c0142004d00e840032107060ba54286005601c03055110703012035407140c00348c1010090b03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 29048090 1250 29046840 29046851
    0x20c070807050f010c02060318150a050a06050105070b1807030501021b010b01110709020d02070501150513060e011403120403050a1106180906060c0d0c05010c050f0a110709 76
    0xc00000894805489040780c04090740741e506801507440c0ea8074503100a401c94010300008080c4049130685014901e100e40a48a0b0b00040e00e0002820840c203d4801c2c01255580d801d1080038006445100080c02007820210b00e00304480e1561750b20f000006000c508009400340e5070b0700411100707011a80003160320000954960003051224500030740c003c0d44124441d80307007031813000322580b28200c030000002604015000c918100103c0364040d500c1038017014103d503002c00100002030424458182d810100c03407000c1686a0070042045080e110712600c85e42c0b540d007820b07018020307841e10005060458510380f04070b401d40020f19001ca8145407039407000f44070703040e0081000000e000003c50403942491044511808403a100010024140111f51420300071100d44214101641032005400750810402031070b0314181642070780240d240c030047c0d11071000000d182426642c100300c0240075404400d5083d04180d801c05505101990041c020a12004100030f55002640f016000034440c0c0c2d0003400030f80344213108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 29049340 1250 29048090 29048099
    0xc0c200a0b0d0e0c0102010b10080a020412050102070c05060306010e0123030103080307021006030b040f060e0105010b180406050f150c01020a03020a0e01080105030d030e01060e010e0402013005040501020c07 91
    0x1040201c01031401d501031303c1d021403502c1d8411301c078400c6030780d10003841074540514406049400400017850207039607640c20803005c81e005154a520300c001d01e200c1c400250b52108249041e2070f43c1141a0300030f5029090a10900010780c0c0c10026400340c0103070a1078681010f540c11680381c1e130700304031001c99054a40b01c00000802880034032002275100399147d80031520003c0019240f0341c1118494030018104074000c0c004180040d042c4d001e101e5145002d8040824804841d04005086071001e9000000c1854002a0320000450074461b4600c0c02604581c100041e61800340442c8000d9040c020f040e03c00c80307110001e503071424210400d544002521900864a41c404e240020700290b00c404800804a080c0d0940168603621801d8460305850024000e400c0441080b20f06030098240302500c0312840d500c8a00c081101c0e0080020180200820070720aa078500742400050200c404948190b40440c0d01c020007a0790241c5190703140c410040203050009082da950341031150082c00b846500300c0c001d0180b4080000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 29050590 1250 29049340 29049367
    0x306150e090a03050d0b03010f06060f020c0d021302032d0103110301090c06110a0501020c060609010b07030504051009090c0c120e03060606070f0b010609090c0c200a0b 74
    0x1640d0000390409840d8403207800c402e40d20003800c44000c001500410402c003a80741160032000850601400128801a02e85002780503500d8030b801c0b2400043c400711092020703950401440344100020755124440480d6500030411110756540d4139204c40c1e400001244442d039412050140e014102c501940215050071001c0314400d0007880b042c1c1e81140108000140703454180300c0c203154507a01411400640c1d2a10341d0a50700070091446103080b6020790701040000c02d50038001007040440d1310003d099140b80903002c11400c100180c00000d0f804d401442240d00207a040402c4400380c4d401141c003040040d0000314125140c104a41010550a05055030b050310150408600309845100b48154821980c50041c212440381660010940c590311940208034a800c0610090030442c0c0690301429640c030041e1192903850300207038441c0c40042e40107101000f16000602c203903221218585400c640004c07440e1101c0620300c980311000401810307035104d440c400703540b24000341005000401045407241c1524039001d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 29051840 1250 29050590 29050631
    0x41e0c0305010609020c0a020f280504060b09031f1e05161b0f05030408030a0503090d0806060301090b1201060909050f070e0c0c07051309032705190306 67
    0xc5034190b0a110010403131041c01c0c0241d80080c2a6440109040d0100e60204105801c01c1a81585c1251804d5154103165041c2c2503107100c0a045440b00b100c1c414900307401d00c01124940d50110403005014482c511355a50301080e001043c6040e880b13203843c0c0301752110b40c03c03004000d1064543d106900e0400d0407210385c4140d400040c422214501560041e84950b1000d83c2e040c5074401c0110406800880c184002922018201441e28040c0b01100d0070541c482900601e141e0082c40f0040109202100b0811126820800b44004550318640b12455092440c08508140070601603200065240c0388840c800307441c2c5504015024001a009208003690342d03410740c0041a00c7c4405884500801604102c0034600041080403500d41440c0c106466880003240742d10740d007041550356070a000b070380720000c2d0640e500c0d100114048005880056a1703441450094124200d81001818048071508194800c007020307841c000480b002690101c0000b0307071284030f080740304040b500010f25083c500703c3c1040d20760051520a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 29053090 1250 29051840 29051843
    0x1305090606040902090c0d020c03030103050106051f051204020303070f03090911090a03020111030d060806010e01091b110a0c09051806190929250e09041e0c03 70
    0x259105900d4900900083e0350300d9580207500591900c020403540d0010900812441d0410000141030411003100790b815036100781d00c2070341c06039180d950500c0185801c0c480303003007104550110480f10b0611440d000c1c045002d145a012110301804c00094155102441211030150780268188280b0045140143c0303030b42c10341e01803900440c0c58082002c40c2281074804031901003e005068544180c9140e00450f80041170040e000402c1c0030510241446c1807542c0112405021260090b0540c2e43c1018005203400304140e1018020f01c0c100384004050b208a60b03004c40c1c0d105090715085403151007080c40c0910b000c40070fa900414a4101c0a0006591007140d40b1050158002c3c107042096104807413001d5550300e001344d6a2040030200f0030350300303100b6162a50060201034420140e010f040e00c102c40703801c500d0300351010754842913410f22400c1108156110030440040d5180c07104904140c20094802026020f070000003034021000580131078180304541944083d00041e08008007042c0480349003252120406200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 29054340 1250 29053090 29053093
    0x30315050103090201090509040809030601030305091804030c11030708030406081806010608070c02041404050604021f090303050d020d090f0c080a150c0e150406180303140d0b130509 80
    0x40100d055071180c055011095016911090743d83d00b06801c014440201400c00c441c29001045281040c0d1001d018050080d40030b80c689945400c0500140300160700c090b4005040c001c055002c2100198104410f41d032134503005116101c1940d85200420700d042c1c0241c00a000c0362101060004240342c0c0a4049480780e0301ca040704819491030031400e070f0ba48140078007c5a0108820f40b000421040c0308900d41005940002e00215180c9c002e011040000503040d9000d95007500440101b00c25820703c1c1d0400481d00994622028000c03c0c620402403001041c1e000040420a0009101d840c003031054040e01e51442d4895001c2265000d941381c126070284a80340c0449a1041c0080d000981c0040420450310785908282800528400146004002c141800386c49003170145480c400006a12000d5500c2d03031250810345c0081d910380c106803020304190b8610a9055241c070700e290080c03000a0340400c440c5002c00582c91065202d0380d50303c1c4080007600300011229000052541001c04a075503d4101c01e0250039200d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 29055590 1250 29054340 29054381
    0x130311030706050406050d06090207030c0b10180f0f1103010303080906060306070e0303071203050901140606070b041a04060911061e030606071b03050105060108091504020604050d0303 81
    0x2414035803688450b220b0303840400c100b808200501c0340580000c01905989480c0050205d80341e00008089030842007007907001800c50f01d10345c0101314a05010542040314861908881d92503d0008100710040c1d006030980c00c4e072100e10341103c1c88080d400c5001c0301114a20140a81644034452041070780007480150300140b0f880300880c115030000300d406402503801501400e4a5560160182e5040855010a0740c0600c0100b1404000c208005e070030b00012130103580c0118840c20321281c12030950b800c03014031802ca0b020f06814800d187d61014201d8840a074440325000035a07649040800880340303021040c00e0034110220411041100b6640031204070351064501800c4480c0d100141300c241d0083e00820460060310704a9181d103040304030040d641c00034008150600e07290b01503482001100b8458000c5101c3d0484000074030400c5420301840d0340c01202071901c1c0d40b00d40750005c0c03d907940e84940108070303030010000000301e41551a41000c84000d01405024900e113008580390080090800304482000d070118030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 29056840 1250 29055590 29055623
    0xc0c0f060207051204060f0806060d0c1206080d0c062406080f0f06010c03031505030a0309090b0910090504020f060a0e0109060e030a080d0617030d05010b041d07030e031303 76
    0x800070b45054540996590744081f40006d0113840031040608019070200702400741e2001c81c00a4000e0b0031881c00c20707558205880c40018000001e40d5210b8000c41c13000d400500f024114a42d1200c0d03104141e80d0044000300b072022104c0844e001d403d02502c01114006038990f404030304c154118140314011005c48409402d10f58841c244101620001e407081030006200002e804042442900110301c5810302c4119644125600c0001a00c0e18422510480109082a800b0041500e041c0729880d1130050650700400300346060145419551400e00070540d4042c4c0e1074000c203003075441c1c1c2c000c07543c904200a0007a5982d030320000400307881c0304010340303100b0700145104001142c1d040c855603900c440c864002e801040002e42d1a500c226998001c0305802c0001035a969000420340d800c0c1c05020007600300c01010f966600044003c01055900503040020040c01c00c0008000d1088011b900e008041403442503a101521035003002c401070700c5040f4a42415200c0414042080903d00315040c080f80e00c00e03079001502d030707801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 29058090 1250 29056840 29056873
    0x2e0e030d0906110c0a1e15021e0c03060103060204090e1209010f1404060504030b010e040c030b0c07020406143109030c060c02031206010201090b01090c0c0f06020705 73
    0x80c005160000301c07800c204100142c0100011040c40c641002030b40c401060700800b154035400342e07070b00980910041c000c440920303002c166502400741c00e1054044684c000300100c081d6882d0b90750303889420400c40500300c4100c185001c0c440346589141c006c0684540e0350352400c006010b9046405910302040c9000a12914100001140e90107030010510407414184000c00549201c14810b6045c130900100300310903418108401c000b0030281103151249910386040d0300300540000d905800140c0d41ea030b01d840c00d200c04110b614480201700d0b94082c820049a40da0750800304800d001d88100290011306000c030100300101107c00e01000a10207591480e82004041c00880b10549911140910302c40b010041d0803401001e1703005080741a001c0c0c182418a40b00c0ca546020407141101d2400700181c0004c59451407000d005003503207400103800d10080c080c1044503141c2e18030010041c403807100b905554080d41c4c44407501541224800c260040d40307031140da03560f504008000e036100080480780341c0541208071140015 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 29059340 1250 29058090 29058103
    0x1d0412030902030c0f0d0804032009010f091d0f070603150e0c07020a050612040209100303050307030f0e010c08010f0501081003120c02060d1401081f02092e0e03 71
    0xc00034004c0c100e503a40d8a060201190395000c105030000f4400300040f010450080052005610428104030070010b16014413180829807180039120309910300040182c2c402180c0100b003684e440680000d01c0c1032a401506110900280c2942d5050041c000c000c2d21004011440404590094400307010020a041c4070705851072590003101c1c51024900041114500c0c600083d00c000c500c084c2c01d2072055a22000050b48540160140804040e032510400003103060510056401442e50f40403041c1041c00c503640074295000050000c02099030340c2400103510b5800b40c209a00050180c0c00800050800d214001c10465090007071794400340b061000090303154070545010348118445080302c200203055070b076803040055800120782c040084c070000d400056030317480004098110344400d0000d143c0c2d5811056204803a0168040360030b40c0c22004a100341c1004100c008201442c00c1080160781e00c43c0c0800042c4040c9407420700208182c4000100440c0c003203041c0443d04801d04940307458900903141e1042541d03541 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 29060590 1250 29059340 29059343
    0x9010e0a1103030d060b180103050103110d06060f09020d05010b0405060f0f1e03010e0601030b01020303070e01090308070b190e030403080d0209030604030203190305060d080307091d04120309 84
    0x14440c6001401046140d09140324080006080d079107004103032110300d0156070654100c001c0c241400191004240602a501601c585080c2410300256245032603003100c40c9034207008a4068100301410200f080050382c8403e01901007600c114807625154a5814001d40004400081c0b080c98070b000403a800c0e02a000361821500000d10941c030300040c2d015542c055070031201c0010b140782002c4c010005030071080401b0110070700100303544d5501e961410f52050300240e8058140e82c10305181850654150f40d011049070741c001d0b010705007800000d0100780100e480c10740300c1d030000d80f50341408102c110801001044250080302c202104030400c100b9001d01d07034200c50340030b4030341d06080e4420807003080090840e0740a042d50b2450a00c005050140c0e07240462b0030103008440032001a000000d441180100c15805c04c1c9001c1e400c0c1c5020405490b21030042490981d01d150301801e41c80c03001c8000b5078800e20a8944401401c0a01022200081040240404003e00f0380d01124000c048441e80700002c1d120707120350001d95 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 29061840 1250 29060590 29060593
    0x405060607030f090b0408010b0907050a08041704170604020a0b13090b01090b0d09030807091404110903100504020306072a03030f020c031b060f040303050c090d03020a03020609010e 80
    0x1180e40d5082e50110605030b80501884a650000141501400003400c000c0c807d02001141020414041102da4000140900b003404030600c00d030000e03030f50300409503580141d22402100000d88d100100b80020701543d8056031003440891100d04c0790520108032240140d20035a5500c40054a5081006083c01030304006030700e00755410810407424040b9080340c1001039040c10946281511820341b5081130784080d400324141e50721403e010382010b61001845500000384d141c009003442c200030701c0070422014055914452134507406040581004481240d00b0420002e0840e20303d014246034031405000100c409078407034011480002c50182c002c00c403140390341e0044e002070f180f00c102112500001c250852015000c050340d8030a4054514070742c0c4000c03d502e01c1108021511000081798800d00314010304e14031500d0750850310070b20810342d200410381034006070325003030126603a074070001511050300584131b10702e81c00185084500241a0042201e80782e4038060b03800d0b11001d548900111342a01c1c1880c01c0c0c200203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 29063090 1250 29061840 29061847
    0x106020708030a12090b010305011a01030606090506130e090a050c0409030f08070c06020a020c0a09060501050304020d06020c030d060510020f0d0c050703080a0305011701050601020706080408120a05060f04050606 93
    0x4079413060511040c030b000498400078103035120380c84012510b1000d8208032040d80d5680040c0000b42001d03410500f23200b100b441e042c003420342882801400440c0c13a00c02c103030051202103400110903514544902c0613040c0c54000fa000c518141040c3ea0703a031940102d00f80d4043c010780f1400c4005050078001c824450350503882c0c0303c1c000092500212800f41c4c0040c4030200704601051860001031441c001080b4401c4240e0041c01d085040740200034a8030910383c0300125061421408119990f040810303640c0c015011030b40020b0000c0c50341001d00c041c0c42080802082400002401920030704503600200c15100c0941c0c01c031541d81c9050106913543c070000450303810154003a03490003c070b880c0305040d00b00101d03211b80b05503000f443e039913941d00b82c89030410f4100d080030a0b02d4000500c00b000c1d84516125281c00c218000740401d080440c0041c1d2602d5050041c03008101a400008091180c00b504a80c3c80380e2540c1c0c3c00354454036000d86030200421003030360001d00c984000c1c0484142890280036440c02100300900440c42e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 29064340 1250 29063090 29063107
    0x10b090f0d03022506020d08091209030a06061203030c0806150c12030f061c080a0503060109081603022404140103090212060a15080606010c02031c110105010602070803 74
    0x5030702144070400c5085118040b508481d519005854034402d400344c01c0000300c034505042001e81000c2122440342c0c1008900820048800700c00542d07d903c034400042d200b40d881c0945400700782803000f400c0000d0000d500b021400580404400c85400703065003e5942003182148000d01102d10f420255011766002d000f08840c420440300c1100204480103100c802c9510307103d00880d04684541040f00e034183c142c0d1502003040803606201d001102c40d0065450348400b00a0b4031341c0d62205038084d6182000070481c011001640e564000d241d04400340600708d00b1a44008840305c405540ca00d02400f08a0040c00800b00125010380300b1025224605407000201e41064141150700510802c861815070406440d04024800358698203c445075414064020b801d00380780c07401c584001c1c0c41d52408201513500d4005402c02065501142c1c89030405c0302464400261501c9000013450100c0c0420f0410010f640400d0810200b07400280c4074101d058004002e000c26a40c2c0c07142603881c4c580724403c40c040c03a0810082c041c0e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 29065590 1250 29064340 29064349
    0x170a030e0907022517060a061707030308060604050a0801020c010b0102032110030f0b090105130201080606070c09022a011a090c04080d030b0f090103020a05010f11060a02070b010b090f 81
    0x80d644c80401d00300310903035900080d045184e01c50740c03004503a0401c0c010302403158203901401010b4516424071019400c01c002c0300607aa41210710015040040803004074841e42e803010211001003000600504425072900807c41c002d50082945402640ca0440051070035400401039400544042761445004007100390100302c2c031100100413502c10305c1310510100004940d11f1a0076021401004c501c4c41c2854901c2c05142120301c00740104401c14039611110780180c0e448007150350700107010740d141e6490f1a4180780c0301403208600d80141499074000300b032614404002402522051200c030441c074103112000d03011203080318a254280500e03000905200705a50030803062a6400c0011008510300c1e059540750f1150a155a0b03c0c1c180c0c0c002601d03076140c0d521302c1c07500280c0e064013190700701c6184405525541c0050703d00c6903244500c0381408640c1a603440641c0c0a01c5030b0120b82c0803080c3c26520385240a18480c0029030104800b04c070441e9174140049851919101612640c03d0041c1000710103510100800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 29066840 1250 29065590 29065633
    0x6010203190c06020c0c0306070305010311100c0501090308100603050c041a0403080406120605031f0515090c03010305010c0503160509060f070b01090f020a05070615170a030e090702 80
    0x21040c0111018210000b409604c014511440260060f0a042c1901c404160400e000901203004143c18600140080380980040d0700308071800310350361140282d901030240d40760040000054584e5290007024030605420044e000e20890580104c0302d000d6403240310540480380309540455141900b800188119107004144a518041070014581495501e03076800031a940244c203c007000541e0090341003500d21340e9010315000b50204401908412010301c804060a082c0718025180d9581c03950089460303400c0300191407038000c0014003403010074035010303840080d103034001e220840d0990303e407c9500c400280b188040e64001d20800800d12030214600c44216030542003810b001d0342c42401045108800a220300c001c0181e0b80c81840b000f90380390316207000d60045132244040000800d004000c3e10380440c0d03000080792a0710358424000145085001220000c1d10010707000350b068000f407900414144000040c0c4120054882c0d0b4484013600030f501c0a00400d0a010f986c1e80340540d0001e00204094110144907 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 29068090 1250 29066840 29066887
    0xb040b032d1e03040806100b0306040f0605040f0b1002030307090308071b06080405010b040608070302130207020904030206040b0a0c050d05072a0317040b040b09070b030a06090b0906010203 83
    0x444802e40c0032140090051070b6001802d2415620000e82003044d500180070300e945c010864190041940d141001d0142c0c42c0c48001d0044d0b10403071307958507503117003142c51688000050301019004125040c001c0b0f445074001c01300b11001600c600641c07000411094800402c4a00c81d03250ba0b615022428950f41d15101175400c40c210444441181c5464002001240c8104000800046d0740f132004a003458202142100c1c072000d0340c070307008a06162040c0035460380000c16004036541034451205034250a0b6251001707005401000b5807014451050006040d030018011b80200d002c1c12078035906850b1050300c5e1080b29000800e243c0807402c248003107110508240e00455200380d4900301007920100c01500f0441c403010200c0000c0171085007980240c141503010707840044080d8407440c03402d1681416214442c1b031000007000184409186000911426401d04c4080c1c000d1200c12002903c82c1001030f1103401030482030145003111880d01c10322458030702e001040035000f940182c002d54900030b44c0c2c05102c0c3c018158001e4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 29069340 1250 29068090 29068093
    0x10308091509090a0606110a0b070c060b0d050c1e1003050415110c1203010506030c0c0a050714090c030610080601030b06070b01320108040309180b040b032d 69
    0x800002c0e121203410601c80e003403410780014010b01b4041d0107000c0b290881d143e400503030b02080c0c0070300018620384446c0ba0001d50030f003004206103206281000103000d4144000d900640390001c070b582004000100c040310408100e8041051019812100c498034000c91a42c59000620403d01e110040c02940076a801a0080080601101c140d100000640e00014410075901c0800628011103590038880312041c0c1c421401203a207103524003000940c0034000074000c900528000600400103003010005400400e52040980f500785a0751007070801c2049114006501400311000010b0600044004503842007400425400080c02c2c0031134110f4207884001c1249d8185540c8043c030304010394590003d040001d00c41c5c5d400d04980e60512181d8a10884040d0444251098040b234214180d182110100c9200400b0300e0401e0381691581022102101d0303650051045003450050f0103c81741154010010b41502942c052002255810915507540c030707001034012020900c080051403140c4421300646503000c1310720 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 29070590 1250 29069340 29069347
    0xc030807120905031b0d0e0a03021002030408340305060423070905040204060602011104090218100f030e0c0a17010209060a05030108070506070807030e01031508030d11030103080915 80
    0x1d0f030f00c41c40c6034800c2c07008881001d11340804035034002e03041291030031011183c1f900c4007018001c0c1012442c40740440c080203101e41c00c1d284088002c0c038420030a0758024040d6100700c800308100c0c0b5625026a244900c4a00d4440100310032400c0e408800c240c00f42c007100d03440002000d9941d00c0d9143c00758201400120100d021111010b050a0600104109405403080e8800020a401d162040004807450360b44000150b9041540c009018444c4e082030728110340301c292000d6982c00096004502c1003c0c440740307180d0f00100c1d5849c3c512440c0e5001906800009450305c0070003240038100d1400e9600c61207009015840005d0900521440e0900400c142c0d03540f00380b80001d0b0030112940001076040d0000c80c403440c00144e0200040121202c10003030700006141c10380303a9528207581034661228510a140c0040d050010980105001e0791180d840709180c1c0180410030812207455105098590b4440b2191221141c24076028000402c0302c1c0c81140e040303035072020011380340803150b10601500710b0300240032000d0181c051 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 29071840 1250 29070590 29070593
    0xa030e0409060615020c01030b0d03020a0206030703020c0d080a050a1a041e0f0e1e060403081314010606020f03030112030e06070615090c0e03070603051008010f02040e070c0308071209 81
    0x501e1a850100013503001b40515810b680001011940c854050510a41c0940b403060003094000c00c4041026406840103542e03603680c0318050f00688a050551b01c000d128403466803002c0c0768840710349030203506280018060317610303140c9220701a42c0031003842c0c0302c218134510741100b1380703203841d0340121044c0c031401c1c4400000702c030156002000c445100c641052800d072214011400c45c038040c0300041213808400300d003625008074200c03199614980207000600744071000c0c011642035002c03103102c107170741c030380c3c010840c00c0c0e001e0004185601900f840d114040151203a000403a102c07c3d808410380c3e040e07401d485600c609050aa8400f1207030060790440180d08003130100020004104240104020301242c83c0c5180b9407a45081c07030303180494072210001420024240850b50160343e001c18844d0442c0c946140205854882c0b8910445900c0c1b80e03070020400b90b18010b0610003030341c40303500a04211120305024031a507565005064401c81e1009100a0014070b070030000520681c0501c008604803003151200040000a5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 29073090 1250 29071840 29071859
    0x1050c1b0117090c0f030d0804030c02040204030501020318060a0c121a0907050901020c0108060d0605060402090607030e0a0b0406020604140106180b1509060d02030603010212070906110a030e04090606 88
    0x2903d035180a600310052224150400c10309050f88400700380d000b007001c1e1003140002841c00b0000b40000b02000038006180007955180d0701640c0c090768018000715641d09040089a0410075041c1c40c5904038040c1c01d001440c0108640701e14010f010050711900506141141030340c00800107002030b0640205100c4200450351600c0000c40d10a902c01d850780c03591a00c40c0c000280c44d280d0310350f1b0024100720640b4200b040c69101d440d081c104c4140c0c003e02c046072a4803140c000801a005030b800258000740d010031200700345548080c01041d4601c0903184510266151080040c003441139015001c0561700c01c00c040b0f000501d0400c2c459007942c00b500000101952580100b0203801003221404516984a03d400c81c52468180c41c940d4288074014503003407a05003010f0101d15203004005d00d401c14180e001c40025402e1701c00b90102c0f4107103010a21094054601610040e000f81c1c15401950000b45100c016036400e1503000034203468982d0181c817a41c404200c0c2d041000081c2000240803250103455650010b000c000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 29074340 1250 29073090 29073137
    0xf03061207031202161202010e0307051507060f02040806041b030206030703061706040309050d020411030c0a0206160219020d020a03120f090506030c030c040e0c040302090601050c1b01 81
    0xc900060300342210f00c0c4000a03d07003c80d50100021401c0c24890400030500350400c0991116030a0810429158174003000900700341d405e600c420380020101592401c8a080c034001050700314030602e03042050501c80032000b000c80c0194055624241e00100208010030b205101a030302030f00c450801c00120701e440c4ea0218200303030016102c0201090721880c3c18080b9080b01e004000c00c4d480301c0401450b1524254038010b102c030b00c192180f00c1c01601845c01e0710055403100e070400e541246005100f1a60303800c2408441070107510041042d00113006100100d144007108910038584441261b0082c89004040d002140da21041c0744000c907408a28590b403400141c90314000c00c80194000c0b44000c200001f0400b0103410000c481c0c0401080001e100c02c2403102e40c1c4c5a506031703078105089008294496641e031008013030501c41c64002000c0004000200510410344200401c1540e200396004640c688070400191054002c180705003c01e50010403030000c070a8042c0c07050304411081450064114074480740e110a100c803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 29075590 1250 29074340 29074343
    0x503040605130603090f02090a15030c030209060105130905070c020d0303060609080313030b06240901090906080a03080405190b01052107181b05070c080705060f0306120703 76
    0x1680802c1c05403002e2004041c8100a00e203500307060054a96560741d0304881088804000e200d6080708001c21a09046640814007500150b007104200d592641441018810701d0b2204038410100c50300001c030154403803015130301e8503a1004000d04030316050201c004090311005104004000c206000340c8003682d140380e03c02c1c4005001c0d03140011a0b50070304d80d00500703501c540d4011540507802080311905443c00c8030101e60403640c011010300b803d87c48042c009580050001003c8145203040081031545142400041214800c00d0b201e40000a65460118068a01da4031030580070750071071012440400c6c02005980d5109124a094138512089800c107030104100003c429a042c0e054000140304034180708064100f0080100361280e003882a5002c5143e4440c4280214440070403140c461700c01c098900d40080c1c1c0412a5480440250302604c00010010380020000b0f1362825083c00b00001c0c103440100d40401a01d0010309054039018100181101c294006000c458008801400342c040d03d040c1032002d4000746 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 29076840 1250 29075590 29075597
    0x402040b03040b0c03070e09040f02031212010e04080a030b1302030109020a08060301050f0105010c0f0203030f0a0e040621020d08030709060809190f031e02010510211e05030406 78
    0xb82070030304140864900c003c044280ca080100f05000000760041d02154807030000312910b800360303592842d280045504582000f9007500c40e02410004182d00c100140840c0038103051410f009a87e503500300c1c40c070716a040d18054800c000c1007040304001380c86034000c5203d624015103d25000316000c042003040740c1c03003640140c80c43c507404105000000d60101080d0b8000703000310300074032183c01d0030720005900c2441803050505000703080d0240c00c1000241102d070040f603a001020359840748440000261580d01015828002480b1540d0354200313840c00c3c3c450001500c51002018500d9480070104030784030705503140117036803006049654500041504009600c15440c035590320014a16150018000350f030040d11151254001c1490b013446411040d80241c100c50300a13404803240c004c4c904060b40c0520301c2200c1e04060002190595420503015040f02d4000c40419003400d01555485249951040d084201c0c0c2426810300e40005000c10f0b0150b80c504600c0c03221031000b041c4480941d07030b07440c0745070f10680c00030020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 29078090 1250 29076840 29076847
    0x103231501060f030c170c0c0703060e010501030201080105030a031e0203040b040305030403060c051204031d0d050f060106020106030b01050f03070819030e0a08061308040503012a0302120106031107020402040b 92
    0x40f69458003841002d802c10342080c00c40c06000521400100c41d009103007084900300807442441200702004204003d5420500400c8180402060076020344000d010590100e48a00c00000719800c0001c0c1012507103425964090301942c940300c540203040c0d240704000c411444188004a441c1c515103006000941c46840295030312440c41c0303400419250300c01e125100b4000184100d40e01c103d0b4001e1440d900039850710300400301d502000da044428603026400e01c2e0704940b05080c1e00041100000702c004101c0c001c181101e08036030380c0340022805d8a07414000103142c0c0045034010006800d19074540c1f45404801010740d69929218404a8540f002c0c0d440355003850b4442c0c0c1d0ba440c05041d003000054040309001c0d1402e022444c200700310075540d400060708030807880d0301101d0580305000d04e0f14103a0f805458010024003031443c440c2c49207500000c0d8501c02c00c588000c031040b03078000580240b007218003e40c180395000c4076aa1030300c20242d0041c050441c00c1e80b00098204954401a5564401000900b61a080880d02c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 29079340 1250 29078090 29078117
    0x19030506010e031f0b040b0607060203040611040b07170306030a020111030c0607021c05090f0d030c05010f140f0103170307181203030b09010602060105060f0c01060305010b010206070305010323150106 88
    0x1035802001701203009501e00700540c503017911500201d40b0403d42100340540e40741c030740386803100040082c500c407076000807070104000c101041e02c1401006102e0080d4500c54000080b5031040005200550301d01d0f074194400d043c07560065006031099203000106005880c2400741c509505810007004441b46001a0812001401c002450340c0c4503a152000c5480e0180c00e0061000205214440d0b00c1380d4240314501151010040505c910a0000340e9603004009201c80d030060040d440150407107034004190340041000050b41e1911070410981203d03004009a01705c40d406d00c1d0644001d600251810301000340500680a0030b1911034000c400505000350100022001418010100c8005070314052064484034010400c003540028520f0560b1401c507421a07a0b41c1c80004207080c28850280c0c250465424418000180030301036014009098081e0282d461950b1a100210112642400300401130349011000020040074201058010219030048034a180c0c844901428000c000364803000002c1c1d20b2445845 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 29080590 1250 29079340 29079403
    0x20c2b06090b040c1d040b010e0c070f050c010306060c02060a0c050307080c1506010201050411060c0a0c0e010603060e010b03040b130b2e08060c0906040b03010605040906060519030506010e03 84
    0x17403000c002c3c042840c00d507003041e41d80c90a40786c406108016560342200d02180c0c1100c0c004044500d500d81c000010100301c0d02900d401c640f64441500c016012038544480041c0c2c050107201180c41d0341ea0b00400c400d282c0403400b20103450f50445030700e0580f01b500c8103200140000340b110b0006d194030b54144000b4400c2b654201402080c101c0010101da0441e410401031000155500e5900201200100c503250748602d00c58040c5482e01f40d01850141075000700c980001100011030340f04c0c5058400f50303035043c0001611414000c00c03030902032040140200c1e0800009011039843c0000542010190420002c1200c00f51a810000038040d6070310b0504002d82604e11182020100c1000c0d1703641e804100201e041480c1c81207840e110036008040856418000a030503003e0780c1d0782c0e81114050244559015200d584030807005200d50400e001e2400d01a2801001241090041c026100c0d003601c1504001101800e450341100a0b2030080e0809051010f884000c4e1002e58040c48040701000b403620061401c09901e01d24034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 29081840 1250 29080590 29080619
    0x30503071511030601030e0319031a0f011d01030f0c0509030609010e0c01052d0409180206030705090a03060c030c021005010608130314030106050a020c2b06090b040c 73
    0xc1c4070442c58040c1c900e41c04406003050740d034428002d08000400642c80407440d4198860440d50004245d40d80d030090800a4142c0d10050300604030300510104001040244855602c60031102c1d80480e25908210750028951220014402c80600d0003281c0d041c225801c180964152071140070100f40c0110b040700f42c509041003155032203885032000f4008264400203060321110030070325180c10411300180000c480b00000701c0ca806c80701d0145183c0100712070310000540d070a40140c014108003038203000c82c0c0d00f4003812141c1780484031500103244a10316100c540c0103941e10b5209998407504014100c1c000070100d1120b20070030503103500c16180412018070700080241040c42007030a03065031078504030050141c0c540c411078240e404510500503040185990a054510155109604003070050000000c03e11a40c041d0281892040d960215400c1c45545010044402c1969a0000401750541c2c00c007004402d15142c1203c1450190400103019107280e207410030010360803102610200500c0300c00300417058078210706 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 29083090 1250 29081840 29081873
    0x60b010801050604060e03010b03070602010519050c030105040b030a02040f020913060812030907090501030309031406130611070503070809090906070c020609010e030307060516020a050a060c1803050307 89
    0x503204960404000468500840c0183c03410004103519881d1691000d50040e403000d440201150f4002d652120028081c260445038006500030303400c94259030f0900d078080c080c014159401384605582c201810b00004000034102203500d8801c4080210241e01c841c81200f0b1009680d070300c09030b80c8000700c00c24001801c0c01c0042c0c18100c24503000c0100242c80300441c59042d10409800320958a4130f50004207442c08a107034101090a0340383c6800002090f403c9015502140e00c034800700c91075281c20000d617030b481c1c0d0f904445220880c40b450702c0160018005078802d00d0342c0080c41200c5401c22016803241403444d0005c0300121b400f2140081c4400e80c520307000c0c1e10264031000710001880140340400b0000c00f00b211000700203006031000305c1c0150140e8021a40c0f0443c114018044940b510010700b0824060310040e81c80c10550720094411006040c03011038464102d642000c02084d0b0810142e8400c0c0c02800d0030300381e440c02c100c018803018042d03102c82c000d00801140250011511104542003140c076842d01d8244 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 29084340 1250 29083090 29083097
    0x3040f020108041a0411010807090f0b0307090513020903011103061c030320030103020a05040903020d08040602090d20011107050d050115060203040905090105040c14030715030c02060906010b1209030421060b01 92
    0x404001864be0342189100380da070b45002c2a070304c0e0707158440d042d20703c100e040c1c0190f6840343e80c205517951035003030540c0681080d100860080c48000c0040203000c140d8401038401d5a00b040040c00d07190400f419000400d13481a10134a00020708440101810080c041003441c11040710030000300403c00c2d8900071160502400044408100015491360003035514240c20307240b0000d11240e20000f405201065040d0f03200110007074424001d0400c28604030750502842c1c0380901810b800e440c81502c041d4480c60032541880e035100018103c0d681408100060407501c0003045503150340b00c59694140c0c090b59070300c0314002e010540042d91103500300761751803050318001000c840d0380341e00d8002004082410203070000e0849807a020802d00003811040801e0074100383c1c0d048072640112010700010696070590007011000c06990a9901a0b2640c05041d52510001e01c2412520a014010950786071801d581c01a00003040c2001c480c50560342e030990400b001e0041c1609140586055074103000d010b40c502604840180034039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 29085590 1250 29084340 29084357
    0x806190605181e241e0c0111091306030b0a0207020307090e0c0a0b0c0705040c18060e0f01081b032205060f060f010f14040b0c07150503040f020108041a0411010807 72
    0x244404d0040c0604100405100305c80130500185c0001041110104001c280c001c0c480b40e000340400390303801e510840c200b074001c1540341c0c101102d4203118403a0381c042e40e80c0840300a026495192002d80a508030b80821790b4180203c250000b10a8040c0c407600c4503400760040944402d1542d142080052440f0750300144950034200655155214049865030584034200c80000c0c072800800340846040c05081d007001c5615204c40804645680c201c1c8191103955002c46000d540144a0801120b80b1082078544881e0941500c1c02c03184a401a10051680118078185240c105000001d08a9002900c0303a015101504088140a0f0180c202030302c196000c0b005a074001c044c00081760000f0044c0300c6502c0340030100450220b11061180c032502c103d40003414001c001c15151100c01080585501e804d200380481c182004911304281da0240080d24403454120740361044011079500191583e1a004108940201080359100803002511900a005a0040010001d802e810320000b50150102511880500c008030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 29086840 1250 29085590 29085649
    0x4050d030b0303040e01050d030309080307030603050d030c0507060e0102070f0b04051504050c09070210020a090f050306100b1c020315030d0503101403030c0102040b0304030806190605181e 83
    0x7501e1b81182ca05642c00c0340e00e01040e0404900400065100030041c01c400806d12804590581004055a01070800d560008803402010b600312912083d00001080c42400303034502055042c0c1c80304d00d21680d5a0005450076059aa071440c00e100e0264080310082c1c0c40d08103200600c030040150342240202c1001c6401103091076200c1d1a520440045524440c080c0f94000a58062090106000c4044c43e1031003075403580074400009d4070600080c001e410151451040c0060103240005072203000e042a1072100c0000c80c14036000c000c05620055803110484044425024280007034801544500000608528248021000c250030800c0707080d03801c0e042010038410301030054214000d000440349540110b850f20802e46011a040d800340a0440000c1d51001c6400105400e10100943c40355200e0340d2049910341c0c82e04108485009295a800c0d0b500064460600105003d00c000300703886481c92412550034030350140007514442029900d00860b404000c000100342c2010380303440325811481c03c4270b2174034600362 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 29088090 1250 29086840 29086859
    0x31005041d03040e0f091614040b0901261207120c0b13050c1002030a050a02012417030a020307060506010e04060807150c1214070501050a020301210507060f12020304050d030b030304 80
    0x917800b23072400c00b0003c4442c81e0141e50ba554440301325814040c00076040d5607911600145055001d00d5061001241501441548030021548954403180c1051507402c04540e40c88040100d20703883c00000a10450074240d41c041140c000c60389106100b441666140e0042c50f04c2c0c102d040200c0310040034050400d0810f01411982c01006a44903010940b418944413048a80c04078050140708903a05c00140401c04c072041c1c1699000c06020586103030704030010100000d01c0f8444d54a110340c50007500160030030b004000000d41c007a0401c03508040145070400d055121000013404a031425440030340c143e40240b4041000000c0b40c6400f01c0b00154a00b8208a40500b68881c800000400d5044204105001c890030300311602c00c6094179240340e000310080201d8035181602030000d41c401c1c010b103140c0c60202901c3d0443d0704008100e10721a280e2240203040c420f07113081801d4400407400c0f4868820b1001c18007a20000c0e1f03002c0e01c051841180541c00030600e10310000805030880724211105802500108030500250f00c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 29089340 1250 29088090 29088133
    0x304021f0f030209030a02060d05061009030c1a0c06090a030806010201060506030c07080f070c06090f03050a060e1c0203041809050d0813020409030e0f0402031005041d03040e0f09 79
    0x5207040150ba036080d1300c00081d00745420160029809035010034440c500145943c08244100000d0b982010000c3c1007140a6855480078031000b81120683c02d4184960f0b5862410080350f5605100010b090a90b41070b407280c01c0c20400c48910a85a00880000c820315900a000c56040b110a00081044900f031001203019480020540003064000141500c10081c42400700c41c47c0034801007800c1d07120262441c040841c00c4051141c000015207600c4013040c0d11081c5a8041c0490f54402d0041038129042c2d6198800b500760403800c03610500603414100c17182c003213036200d02c0c041c1c6505034041c6658a040013150340b04035240c48070329032000340f91824000c0003400c0010110307c40041c904003406a555140c04401c08142d030404025089400c10f17540204040d084a02c0500e500c00880b6104071140700c002c11f0200724001195411030b403140302032003004541025404818603c4404605101c54007212241e80e00e164841d030f00031500343c1001000c20004a90f030000540c1c120024501502c1e2218805481c1c1030042c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 29090590 1250 29089340 29089367
    0x3050106021b03070b0307080a0b0402040e0f070207150201020a170622021c06080d0216060309020609030703030509090112020d080d0e0106060302030106030b01020307020a030b0601050714030304021f 88
    0x150411440314041c1d0b82008800300404200200c1556854142e40041c44908183d2709107070800d007003000c0700761a807620303000703440c20707101444040c0c0c7e15562520081c16040714007412050a5000303050011a030754480b8040018001001d07000940d84005030750300100f8000305058100d0b0401c03605020f11406a0700d100c1800c2c481103080c80e40b80d04c2280c5144104000f8420460440c0303450594200b42d0a2a01d4a07410200480e034041c0141c905154000500380c2e20380a04010195103144883c1c41841142d000703901a8640ba400506480d090040120200f85000d00c141c00c25030102c0c03c00301e040b000c0740c80d10000960140080031850341180d2080c0d808103244460000c0014901c000c04118484009001d038040e401d1402094024059560b0300c12014000750300c280210380010341802d5901d8015400001220000c2d60b01815910100e45140c03500c840c0044041c2c540c0f410440c00300000e50204040c0c02d2001070b144000c1c0c0c081c50790780c01c15204001d00c0640f160764001d4840702e5024480140ba42040c04108410f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 29091840 1250 29090590 29090623
    0x3070602030705040b03150907020a1a09070b1602030d090b070b06060705190302010b040e03040504051f06110c101e02030f0c01050a06091103040f022103030a0501060305010602 78
    0x90310b40001c00c0c1c0345405a9003104c40490000f00402030714290300406080850010748071408151251003080307840e204095005804030b0562164144901c51180c02c0c04ea200d01c0280a40d96029101ca080703000d030381d000c0c3d03136034032295403200c240142940343c02c1c80300111080d11401d203640100c4c038210580d01580030319031010f0211005000062010744400045688241e0310905441d504040c091501080241c0c10100b6401503107448845845400e061203047e0690030003038029800e040c501010400035090084c00d12008800c2050041c808891b030800d0355020b041d060b00c03a904080070300750201c0d00d40300d040c0964906c101c5441c4982c140301c039000b12447d81c4142482101c0b041d41409884180d01c0e500c0380c0404120507107070009612801c040c0640c031403400740425020500019a43c1c40c03c1130260b410b54140310700c0303090042000c0350000c0c003404003c0d01c02c1c602c042c2003c503038184c042483d40760654004040907500d410001c20000350800e5407040e6030140c490303030904024950403d04000d41e1104400c000c403c02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 29093090 1250 29091840 29091847
    0x210020306010e09160206090c130906090f0b01031203050403080f10030b0907080f030403020105032206020d140a06030c0611030f13050102070e01050d0303050a1508061012020303070602 82
    0x50348103a0f0790b10640740f40a00540032030b0900542c3c070030310700071741500070030050040d03401252510401080c1d102c07444400402d03020500300f21104140052806180c1120742e90b139030740041000207030b5091210b82041d000702c007034582e60341c5135051030640103018040140802d880c00c0100400240c100c0c032025049801030302500c1c500d68030b04842c040c01224030303000544150310400c2080030b180c034300060440554800e602942c0c00414502140c44e928043c0e804000d0200380b00b8000941f2190421a45c031050b8040c000c0c2d860b0641800d5207401080381d11003104109041d03183d11400b520307900300e09142604405080c13803c122061558441c00e5104106010b40d20130407608081c0c2d801d82c20010401d4994001c0450411907580c0c0a0341e802e90964184ca10a080c058044c8000004c1d9401039280900d0403940301030054480700a142e542200100070082203100b102e1703640d0280c40b61100500d02804041c100c000010520707400c10304d8401e203c082c0725a0120740c04c1740e8031640700d0f40141c03000b00a031040c503580402e001d604c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 29094340 1250 29093090 29093101
    0x1080a0903020109050f0f12040806011a071a01030b0705070506040b070509120d090b0c1f0e030a020c1c05031e09030a03050a03110301120f03030b1504031e0302100203 74
    0x13516510074090054070909000d940040b801003a8060401406e0080300c00b05042c0b00301526603400780307108504558010100402c20300340f002c3c0d0103c02c00c01700050307907510f000400d95403603003d12083c460000903148520014000c0083c1e00c2191a0050000d042540c1071111507900c0603581c0c80700a200400d2610041c001c0340c0709030302a00c15501000c0340201104800500c2151080d5141035020306100003030301460000480032980c200300c604041e1103c019003490445214441040c0d00d8542e0405c034038035030780c4095030182130060000e00100ca0321a8013421940703c1038420803201c116400b003180e24120b91495030200042c8000308076009042d003050850281c82207040807602900480a1b62a00340c000c1c030f5007800802d41d003d0010104035030b140e1010059410060402c0003280024080c0452840b10903002c40046481080e40f01000ca201e4a00440e081200704040352a00c03050800c051540200030406104100052100410f81c81d841d5846043d21161510000c0d034520308501c1055855500201046 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 29095590 1250 29094340 29094343
    0x4080c1f0f090906030b10090c05070605060f0a0e07030e0712031209020301060806071403070e060904060b041203020708010e07050111010609021c0b0405041511041e0303110102030601080a090302 86
    0x18000d214110040013401c0e540d042110a01508588084a5158503030000c50004032038442d0114000c46aa00e60341044203030f42c0c0f6100288000390505a1002c491003203a03900c0d580e140d0314807020b0321104820700d4441c01c2003140039094070750400c0020b070182c2201c0000d10810041181c000c1601382c1520305000244400c00c0c000d0010400101c029405509040b40441ea401c00020014040c0100e9540d00e500605a0600a0607070300095a26000003002090b210383c062401c100a000743c24001400082c0a681d05d8100d0160f90b481a0300040080c18031000d03220606070103100e40001001c10400034800a030200880540764504d42c0205414803250461400c0d00d036200b5800007002d0101d4100440d555030700884401180c4088814103200c05007060707446a01800c1500506004543c820000d0031602c240d0303030001010b01054905a07010040c01d001c0050084d089030740605c40c2c04001e03011800000e045042c02010204002c40c210590380c0100180402a45e128200035405130007444002070503131452404a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 29096840 1250 29095590 29095607
    0x10f050a1b0602030f010605090901060503041b0f0612050408040608092104030212031206211e0607050c060106030209040b06030f06030709090b0402120106030b010602010204080c1f0f 81
    0x4039001410380070003604000a0394011030140756400c0c02c1030541d0382d030354008442c0d610135503416680090060340104051405131703002e181c1140c41441d080d0182c10707040040c000c4003240d5911420340341c0115481001282e821000c0c9000e460550745080c040c0d40380ca511a03540c1441184101c0302040849400180d10010030b0110105a0318035000c0710129020790120380420342c004c0d02003a0b1084610a07041070000300000125400502c50002c1d01d0065904c070000c1100401031135140086440745004004001c54043c027281101455958030300c1c144031540c005d03451070f00748010300d1b107000e101003080000e840403800541c2604594007490b0140e03070b603444040803801520380019031030b0300001c000c4184801c010b01088441c1c4035120580803101016030f0344440000381d6201960180803440103101040250400e4072000c201c250700b040011230354a13526910711820704000d80c0010700607507010605005241050041e07c504280480d0342c6070304103040f0300307115071101c090303201102c01e01100114800529005030100d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 29098090 1250 29096840 29096867
    0xb0601050f12151002060a09080c0d02030d050a020301032105120a0f0c1404091d030316020105070206061003051f09090203061f0509090309090a0e010b010e010f050a 73
    0x45944070000402490040c000548100400240c0009180c043d400c01c9412a140c2083c543d000740540d840c3e481c04480100441c47e000d40300340004100548100404109641940c0d443e43d00856480340700b040d0507000c07608080c0403145e403d801080108082001108011003850100611058107100002c8c1541c952007000e90303488120f050a4104800001d555000100300402e0000500602c100410100c84221001c5c0d5a04c41c407440601c018461072900b584045d06488075482e202040c841a03011030782c0b0307641007128000c1c2c0d2110380c8901c1c1d001d43e640c203005150b0001d00c2e41c0010040f84c203040d0001440d07820380f01400004c01d0380d1000061800c1c1c4180c845048c0c1c1c2c0d4400d00d680b040c2c01d512002c100e00a450007500903406031142030042004800802442c1c80c12604161307400d1841403c01d81007201003000640380528910050007101c0f42640c5424400d4040c800c283c0c7c0001d05492090703001820360384140c5805043c010188034084190360460620f084e190244e00c0c02030f03a10780a4130000d030303400c8000155 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 29099340 1250 29098090 29098117
    0x50105030705071a0103050c030a080a030c030b040e0303101502060f090307061109030d0207050d030c050f0d030b04050a02090f060a0c0807080c0114011815051905040509030702030a0b060105 84
    0x135000da1182c21180c40a050701d00680a0760304d441095424036903100c803c504002c200d084100300358048907100c2d80c003000a00d4044c4c58041118410303040081c098541c50f0b01700c0f403c00d40000007807100189030390042500a21202040b5241160042c1c0040c0d04d940b001003403c4600148080051588101030003203544256103d05c04100b0042c4141511649802001c0320501910a21003814000350000030750a00710b440060199441158641c2c00700c41960300b1076000c803102e204003000750100301000c1c8036211503459560b4000880c51528410401517a002030040966144104aa2b2090361160a0300400d80f82c0282c1d4210390b40c070315841040760b940d071801001810b40c590120b001c1042241200042900c221038400a0041e0f56074480500030380d003428403d448002840f800c02a02c0c1d0040d540190070b080c09440c2e0380c04001d0340d452007c5240700740701035031500403071045140034400e903e000d126154103d01800021030034400ba03a404030396a000300b018060201269a400504903a10403011202024418075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 29100590 1250 29099340 29099363
    0xb0f0d030c02090c2502031203070201090c0501080f0402011d030712110405010e0f0406020d0f0902010807021207060504230f0c0303030714090301060302040c0c05070906030c05010503070507 84
    0x400a00c0749440700d800301d01c1480041d0201d001500f050f4295450b084070b52194401048030070603a10040c02010b04100d815001d05188050031035110740103148944610b0300086015462854500000b201942010781449010300500c6078011803c580280d10a90a090105e032148503030046140a4004042c42c590500c601070307001c070300c3c40324507808640558440c1030601c099581d2130f030402041d81c000f40680340e92001d400000400c120300c1090781e05c2d0031038020b013801440c0110041941c0c09692070300440c104141d48554009045583c0640c0a9a0007650b600c05040103074a0103c01c50b0481c82402c101411007903c1d4030124040c4184103120300b204441c181c2510110094002540da1a40d0f100040007015000c1c51003482018240841124072511065890620842612030b92860035000b0307011070394241d942d5140100060b00c50340308145241ea125110207200312420b280461900d0041d800c441100c030704049040002400107400107007a564242040e5407a66111642100c03540210b61000c1c20120112 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 29101840 1250 29100590 29100593
    0x90203100603060e0f04020121090c030201121e09060209060406030e0601061407150e12040f1a04050d020d0c030809130216030e03070503030706060501080105010f02060a0b0f0d 78
    0x6258001101c0305510305100c0ca558684144101600455100021070308000000e001584203025400c50344e8040c1140c52120704841c801c10044504005003190b46c0c10140105205668011380c130205081071144051040c01d0102c14144200600a1080020384d03850365800410131103e60141d41c2c01405c05048282c4540d03841c8401000781420000c500c0c42c90040c0170010a00d41d1140070031141c40c416148010303190a042c0c3d0749500c89003d601001158403a5192103440b40302c80c0500c4a21a0110009140f03500d96040c241c004031104000e900c03990340e48003d0040d1526080b008421380307003100c404807000c00c80b844c00c07030021030703000c068a540080000f81d026034040704114001e0041c10407010f0070780c1c2e14818088002001c0307040f80703d110b0244001c40c00189038a00000d1240400914a04020341a034201c680d507207000c2491508103c2040b2407090300e68605110700d5901440a03030040c802440c02c060241001c0c80069214a0060079410405480c0c029501260b01d50031012038012031301504d03040c242d8000d0f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 29103090 1250 29101840 29101861
    0x30b0901090c120b0103032a0b0601090512070902180310060e01050402030609180304081b040c080609010b091504061d04020301080712060902030d0f020d08010b0a03090507090203 79
    0x4600302d9014840890204040d550303c002d074125154460304c1420141d007161010743d842845c0ca40309018a40c0f40c54080e10400c4114501880c50350310030b003140308550603c01c0001d002415150070a50103400d40702c40c4410110b00005105080300e05140c40180c2d2001062075000603802400c002c1a0544030f040005021581540e1200e02200c0140d1010317920340e6243d0040001303030320064330200ea1005101c00407c0c2d001210034040400b2041c200c0c112803916642c0d08103a81800ba4091a1966461040d042c5c060141018001c2940c03060242c03600d40054500000003804102042c054010003000c0442d00c071402d6101e10301c1041030302120b005801d88441c0d0f1540c0040403510445c11030700840c09045480e90300c6003040c3c000e403816922071002030007001e410426090f084088040003030f2205070b111b41c54940580c40520111042c1107056503911041008444040d00e4011103880b81010061381100402110344040203864800b0091300d00030030980b01c242441464009642c118004d541d00c00020b11068403031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 29104340 1250 29103090 29103101
    0x9050a0f0c150e010c03030e0f1b03010e01060302060f1e030c0705010b0108160516020603161b0b0f040302210903010b0303040f06140d060e06040e0a0309060513030b0901 75
    0x4103403007210414030b90310500710b0f1a0015015294003180c00300b64001c00180c06900880d0001624400b111100070441d03000c18a480404030205c440c2c07503980b4076000c1c21401d01b03000b8000711402c0c110092048a01d10360108190348210781c9a251010404141064000e64001c0c80454140744200b41c80c3c2c0b281803141c80004268410217046449600c0e00c0a0140c080d4000c2c09150720445041d0381c41c9144c2d40d0384100c00c0d0748903409001c140c4868580c10001d44016076508001c0c50260070b08074110175030f0701d15a88025003040021100c01d4881d010050040f80060880c40213181c1c000080701c5903a1541e03c45103016131030710084010400c0c48071002c01c402e01d83e030803200c8040c00301e04404034003e101a04d0640c0c140741c0c59220301d02401140120450091203150f0207040c100b103454560308882860585d100b05500300b01c0e50035030440400ea20f0040c0503c541ca141c1030080c00c0d40e00f0b0291000e0102c480240d1f401406c0300c1d07010b00c151028040045400100c400c0c0c40c4845400941c1c109856211902d00001814020030b0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 29105590 1250 29104340 29104349
    0x1050f060d0504050c1003140105040f06090204030503040501020f0601030807170c031c0b0d0213020a0221070309140f040e030f0a0314010611031209010906020c010b040609050c0d09050a0f0c 84
    0x1b0100300403003601790f02c0703409100d0710f003290045074145613400e19041c40040c080740c1c03141c0303007011303448010004940c5210300c020001940104040c41d201d5003020700090a04400360042d44065105000510214000c2412690300c19440490b200402004152005590045016020720741c0008640f18004602e031580402107103c9035582040038240300d07010410341890707004000e90803209180114901030200c0d4010070300d407101401210138550b00c139440c242a601424484d20b20b264400b107040d400f09a00b088501d00641080c0136080208249600803d6007101d540114a02c40d6072a00594030840300180101d92004410103041c2d0750b0b6002c0500050060001c4003060b801c40c9c4840d000005545101d400560441d1b0541b8025518050010352034000380580a05510041e550b40e107000c0c0b00103002da2004003100b1100300c0c008580024518104011507240d0b510000351141444204100038108004554a030752540d2000101011141003203072401c074200748004d102d01c540032a58000e00c04003010000c2200c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 29106840 1250 29105590 29105599
    0x1e132d02031507020a0206030907120c0905060103180201050a0c0606080a020109050907050301050d0311031305030c01110601090f02190306180b0d03080601110706110106050301020304050601050f060d0504050c 92
    0x8148850042c9030244100c60314001030f0440200c440c01031500c000255081108941102d40e410f03155100d407049420b1944c3c0442d880b000d030314000c100c2d00c0080d0150f40c0d4408030908081003601040c02c00780004000315040203042110000c0c41c142d40302d006915180540d90888420059641c07183c682d60355070350034a48140e011548070390000540f49001d83c1d0700d44c0319038034555a40b0b007164038100c24001d0030505490200d042c03000c40c8041841c5034904201514001541d0340c00c4d8600340346008180350038030448250a0381040702d9822021610040082c0560450300925400036511003043d0501009024001890707102240182103004025031640024041d103e8003822400d4010441c1d1005003115070010140c2d8006070000e20407004030303000314a81680501d060400c070100031b40001c600c80c10325a860b00300340040307480d503145451118402d1290001030001540214514202502c842d03944640c140701c4c103071161425103186012522058155071611007454000d010030306003440c1c00c0f81c85880303c20106024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 29108090 1250 29106840 29106853
    0x302030c010f050c0d0b010c05060f0403110f0604240218041401080d0c030e04020c0f0c010203070c0905070c050706090e060d0209040204090204060522051e132d0203 73
    0x240e0880384119030046003a00c003680d1170808801c0c05080a4548104110305001c008080b2402041c0144800f0744603151a0380104c0c524601407902a100703c1d00301c908811a03a0010840007504500041d52940282c0c20064203081c1001a070204282503003100002e0320f61900105a000101d528440ea0651480b0b08403001d100c01c0c0c05c0786410000d904801d100c1e500d4240c3c4030760807481e0580e0041d50490784507402481c04240082640001c202a6401070340c0505165002d558445200c50007131100c089680000d1000d5881c00d0107903211160861a5030003510030303c0c4e0341d5001203001746014400c810131195001c1d081d100c80c00e03038500d009840d004031889103851303010055000501e00d207042c04200c16882e50041c42c1020701c0d1540e40034032008000c1c0344001c031b0f04559a0400816140c0d00d00c0208010300c010113450213800030030851040241c4002518140721050700c000f210915442583c0102d90242040c1014401c00884d07041c00ca0203100070010207254000181404459801008090707282a8025811200c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 29109340 1250 29108090 29108111
    0x409050a0c050a050d02030406090209090606011e0e1c020a0602030d05060a0e04030503040f021e011202040305071802040b0307030903021b0a0504090f021e090f01050a030602071a040302030c01 85
    0x301c0f4825400803200241c010844503848400c00d5003d1a0458090718001548200ba540803501c804d8003921a86010380c4460200001507070b00c0990003003100042c105c01240c407880a0ba001e03140e010703241d032007a01c10441300d20040700580701c4802540031142c00a04d0031802c03a561340700103504c81d80f00600502140d4105000510a403d142c0c0549048401a85c155089075a40f9242124207400c0a4012640441c4005000c40940e032401001c0e40d208002148021030403910100150143d2010030b01008100d006000c03c2000c101c003c18480c0491301c01003005003d207019211444000e01c9250408130f501c050100a1001e0558140d1156201070711a400b190006208420340480210040b1034440d0b200300711701024400b0381459000300b03620f03d21500c40584030384034603400104110800c940e80181e800340340da01c0a0103450b00c41c070300382c3c0c000d1905146060340d941010040740303422180d800b000d01465000152a410000c260700340002c0b032424001e0f0b030400e50030503160080d260361002d0814480d135030900500307a8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 29110590 1250 29109340 29109347
    0xa090f060504030f12020f0a080d0f05100506090613090c08060415050105130b0f0310050d0302120304030c02040c09030b0a0b1e030708120c060f091504020a0b0409050a0c 75
    0x181504e80010344291a40115074601e114400c56003402c0c030850040200804080314200900d803d014441c5006d02d841e003402c0d00754031044603207541610401901345814040d140c542d01c900030080c0c5c0e0007a28026076801d201c2021568602c00c400c141190790007800800640003116a00813140b1451654440d46541c80c0e19041000740e440000034409502d02078002040b540d80110000d04a14400a0b0101000c0e956407201030f00b5a0840300f0050554100001040b41c0510a03602c240098082103407051030384031090b14025500d441c00354a5002c4841c0005c041028036000d200000807007035000b0300502c015040c3c000000c103010900c0c03200301c540304046008103060345205c0c000d5515600d000b41a15a2490303001c5094603a00251042203901400b0310007003c2200319089c45140d000001040354180c2c0c81c9049019585810300040a140e01441d5070400e2008606c008258080c01801d401ca02c0056512a400041c0c01c51841e60b108903174101e000180041e0101d0160030103841001d501104200c0d0040e2014140c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 29111840 1250 29110590 29110597
    0x4060603090809010309021c080408060703060b040e060a0b070303140906060117060406030804060917060105061803010f0c020109060b090103030801060f02010e01180203012f070510020a090f0605 86
    0x2d1180a052121036655446a880051041e000504007a508144140d4108210488040c261035050001a0078080b10340100441c030707000401843d040200a2404844c0c1d160b0340140d02800e208200c044000c100c2c0c9aa030452084050401d60035010342d106803034540a001065100031075101100d41000080c1e400720f01050380351144d14180c5a94613043c51400301014030b81c9004195680c416507800011020485070400361003c1d0001e80c54001400e400d11403d505518002212051541c3c0480014816511000281c407c0c88582d1181800c5c1130300c1001c0040d0142050000003400c03d03151034484c410055054115005c038901a000070801501c070942405800d0b40300340401340108085000401010780708030086100c100c4ca510000034103010700e51401d401e582204000f070b103d99821040440c1545820310505861100c0d005920100402043c8406d19030b8421003098102c5201c0400d2600c11b0080500240000f692000b00445d03032010445400380c42009039018507070314401c0c14000441d5050288048 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 29113090 1250 29111840 29111843
    0x4080d090b04170f06010305010b09130305040504050c0d0c031a0603060901120f0606030317010608060f040f090b130b07020706020613030306050303030702060103031d13110f0c0c0406060309 84
    0x620341810260f148056450401c403d1076540f0a18004070116141070050314061031254002156a0405104000c04000e000d032990620546204078a80029040b41c00c4400300c0720142ca0200741c0f6998a40c0715409170080811801a041c02c0a81c02c2c2801585584410b0550100400340c0c941140c00205000b054081182d016402c01d41c03210040c0701101c00740200d0016188202c00120301020940c0d110000e8a4040d0720840c04615640d03d40c941c1040311400b101d02410350361400c2012407403d030380002c40344003551001d0b601803540c45040c80d00151558112541c8190000c60405041c20200f080a40b99003a06000b03030f82802d03009010600e01440030841008550403030340105103a899002e81020072280c00322048040c940e4801000406450a0004d18410312451b0080d1403550b15500300900000c00c00341d51888221503111170f002450f52500d940300b801070604080010714020b809291900d0b48a480c541d840e074020082072041b40114005040c0710350319016a800e0100550314041a01980c014100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 29114340 1250 29113090 29113109
    0xa060b090d021c0206040807050102010b090f0403080c04091404110d0308040b060307030c06030b09090705030a03030e030d2406023d020f09150708030f0901020403020406090204080d09 81
    0x10310094070f84410b5500d00d110b150f60154681519030390024007903600c0707503106c0d400681008404110700d680a00c50303031178102c0d0306030f40c14021464903220700301200b90001d10060a102048000c03ea080c0441c0342590003a0440090400c04514084040f62805004481c101c403802c00c0d00484200310308080c1050134205616844401c1d00303446640e0790b0100c0c510011718407909031050560000104a19500c10310061910b034500040c2d01c404081401038040b4000c1c095200b0341d00086041015860000380741c4c20350b64042c9000142d2280074000607080d485002620612035051102c0001c1d28103441c081c0550003d11200305017422546d801007603031a000301c010704443d20010001c0540500c070746050320344032034821958034514142140389100201e070800400e0450407640400e460b60b16080190781f00c214040600403407410300d81641d035841a240f20051507178103052094004907100043c2501500e01566005206000d03607078a4008010094025100d080c69620905950b0700850740a02d4803001550901c04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 29115590 1250 29114340 29114359
    0x40f0509040303020d1802040e0606060414010306080601081c09050607030e061606061d13030309020307031a24010f050a09090f050a0605060a0e220c02060a060b09 72
    0x42080380c560801402a410315408111004069007607100340c0c1c503030b40c10f60052000720741d5850043c401101d0424035502100e03880202408820782d10003068400b2659080c4c1d22206039001040100c0242c1003990008140d849075900100700c0880204405003500c0103072440a17a061a42c0e041120b190000d40f080da0b030042420400400031900c5141d0181c1c2208002d081c9034a042114080115961041801500c030f05607201410300442c8858007250300840e81622028410707081501c111990301c800100010705042d510440c50046440034003443d00119000611a1400380828648825056040b240f8401144030f01a24071000e0318100804100e640041e510003160f0340380302d50305903000c0e80009003400c03d020403090001010b800350302440143c01c41001c808a40d1b410300051000548046400240c07180c0350034814001000d5100d28150350480040328040c0c19010780410031104c640703000181c50321240c20403044074086500002c4050103641030340401c00c9201d5031211310400601814800691018101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 29116840 1250 29115590 29115599
    0x30b0105060904060b030a0501150201140c1308030c010c02060601030c0c0204050c090301020c0109020f0105040501050d02070f0209070c0308060102030c0a06050603030408150109060f03020d060f091b0807050402040f 95
    0x64052002d001e000001c8450703c174468100560801c451440b9440e881d1030042c40300780710000514070403280d680000c1c404d035070619642d144070b410010086800e0980115100680300c60500a280c020480d06007502e0307030740d03501030006030103010307880c54000141c03141401180081d4401d1203035800c1c00c0460350307617100386035096420080a05030140800c90400000c2c41680c41581c1d0030f100401c1d488001400010b5440c0561050049101d04100420f0500000380b1040000d0390300038088070340042046e0b40041c1d5800c0c10340303000e000140c00000c0103508600107008100c0195044803009811500079114541c90341c1d05c0300012030b0f491203110988a869000310200e075000694a030410394114a004065a06040d21191214508409015800100c1401900411a01e8140e200b008060428499145c400070704540214002c0749501000501180c1d4035036000d105400c455004407055a40103440081a1190380908580c02e80240200011800307100c2c40010189001e200b01c86c100d80941440e0441d56140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 29118090 1250 29116840 29116849
    0x62706080a0905120703090f0f030807140d171803090105070201090513091403030402100c020409140105010503010c1106040b07090305251d060603190e0f010c09030b0105 75
    0x1e00410380c00d5485444080020710300303216050b405a5407606803a1074102a04004100c00350603800704220341c0d10304070180401044200890141d941100e881a030310a190b10703007911a410180c1c40c7c8401c1e03004050402c00c81030380c403c200342d07640201c00b205490652600d40f802c0a60525170b00d0205070640c0200b01c1c902d86540160301400e00d03203005040c020300a50703880e40418244000304440d0201703155140c030340404108010001c1075415284900030750462405a0125241c81440c0d100c0d002807205e201072050840d512500320300001c5512004004140340b4004407079000e05003c0c05058800d500702516010b450f44140c00d001c0f070211380d0f80020b004540300ca807a61a440000500040100400c42c2c038044007256040203403090940c4e00800451044095220741c0711100280c0d0040c140131882c01c2c14420b40105823a0009030011011108165203444800c1441e15040c000c110307840f4150b0800409051040d404a07000c7d10030001140244942c8034100340843e1804c0107400000d240b40c0000c0014882e80c1031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 29119340 1250 29118090 29118107
    0xe040f020f03160807080c040603050a0f290d080319020705030c0c1005090d150e0d170606090603010e070212120405070605210901110a09062706 64
    0x2185801032500c0c8259903408100c0d44225141640d6040c400c0150b070500341d004480c5036000116150800e110305010700c0344101c074882d07481560300300340d1104085442001140e012204e16140e460080140c001005100c40210300c0c074200e01d0f6450824070101c6400303405c04582c200c00e03099009800300c0c690ba6580c05121703008040c0c035281100081c1c1c240700c02e40004408000800c800840100200704e98203c1d1000c10080c00e4862102404002c000c2c03081c2042c0341c850469034203819a11000031040d0b50700c10685200100100028101140318014550f10541e4101e01e0b0500742601008014150340d40701d0f81406071a1003207200e519040351040004210100e0050720041d0407121920541d2b00400c087d030407182451300302940000c40f507441c00040c00704001007006802c0041038141041b605000070000306054030a074500700c10403010040e00000784854802c0d4042004c0f0b440b2040959140e009510000b007150700640600c00c04110030101c80c80c0150300640c041c08840d031802da2170382d241505000b0304036040c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 29120590 1250 29119340 29119361
    0x112020711060708040f09060509131109010b12010909020102030a050705011103040b070e0909100c0e03030c0d1808100f020706050705030702010b090f06010e010203070b09070314010b010e04 84
    0x2250041e80480590340c04008055440c05690095210b40c104403429000d48850740c40100c8651400c2410001c640310320f25040d034411800000300c0084c4484d400c0104a40c0210326890340d0140d0307010008108006120041c0015003142c0d41d5000441e030f00c07000d00204503004020040e01503401803000c004040d104034001c1000790320680011540c000c885c404011a0380040e142211454a08001c00403d180d22800c19040102e00301d40c6000241405d001c41511005103558410b5000e803242c450080d60343c02420701c1c05650a02a0480340e64238003d03003c0030380b034010b40e0b50301030001208032040002403580b90902c4d07000d884009001d4812010703c001080014420821040b58442e028042d42001c50345503c10a403060b100c07515010380d40c0c540510000e084030b400c915007a02ca40c06a03024841c508042c044010750098013828521030f1030300d940006034078600036000010203000c109001c101c461200490044102ca20803641d0002041c00b6680507402c4c1d4144c00101c0c0d0020700d0034401a402407510b80c1101d401c88 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 29121840 1250 29120590 29120603
    0x30405030d060b090427080a030b03100b0111060c0a1b02031006030c0f140405150a030f031206060f080a0b04060303031d072304150e0709090b01120207 67
    0x507550804105403040341d804540e0062011820800c18141070203200e030390340d5840d8074910300100305021844005403082d201a00c0600040f403031a4056000307070700080341001c00400312088030202002c00b0300a4101988080d001031070400019916000000d059401131707540d00b1259050003034101040b41c50302c0c40c10441510140d1000d0040016131000e00c0080006100d0301d50200710f950550030100000c0e12503511400660041f01800c020540c00500003d5600b802220301280a4464a54100c42115180180f66022114040000402c45c0c02040660f5140c400d441d40c6142c0741d8030484110890708907126060201c1d1800300e45070380311881412a55400300a05000140c580c007030b0f0300400d0444a071f941085001c40d645801103ca121103101d618500000760300300910800e0301381090b2400c00d5010000030041e65082080ca84050b031b40d660008102c0703120740c01a00014540e10600b03c20700f1081901c110010a10b41c010100341e1301c01038020320305200720603169010b2507901030542e00e0007544210000d540f00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 29123090 1250 29121840 29121847
    0x605031b0103110d0507140405010c080702040902090903041502061e07090905070201020406020c0f0607080a050c030a050703030b030c03060115030213090b030706030b0306060103050414011b0906140403060203040503 95
    0x4070881d800107404d00d00d412080009007031824013005030100d10000124501440240820469030f0790280500500e2607120300d40c1602c5099510204000d412254002036200700c0e060308010b41f00da4000003410032520b5085c09162603800110040c0c1c1c44402c00e5402d0585100455015800300c0350946c01143c00c0280b07071801e00b69055640380c0c03d03822250180d5003200140d40005080001c107034108660103c501e000c0300c403c84940076440c0004e900b4072401000510b01d403000300b28120014050000d81d0100a5100b040e60b50711806030b071008149a02c401c030100c1c00b092404080c22501c5c100002c40044c108070240c010850f40e403c00180110200415903140304064003007004500502d0000f1180d0002c101d548030201710b500d1402d00301801d03c841900304000b0146030a00d404030b203541c0010026002202800c0c0020940c803542003403104d10f502089031030055820140c3c516856040d0301c0f40c3e00c950300007030307610844001c0d100c040842c2c980c0003500011080310410710043c00403c1859000b550018441c1d401c482c074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 29124340 1250 29123090 29123111
    0x15070501050a02130e0f0708180a03030b0a0617011a07021314090d0f0e0109030206070b0a05060303040f0312030b090405060a1416140c030714010c030605031b0103 72
    0x81d1181115080051030b0003041002d10780d43c010310050050320101103288071529000d0040710000c50020484c200300311060340480c2c103c86090310000211400360080d50f91190070f6050140c06008005005406020003d40000340c96100750710742c1000b142c4040007811141d20304103940c10750000c048205d684521040040c1c2006035247c07030b10a034404a174048081381c0307076043e00744604140d08008c01400280e0800341c1c4803104158040000c840c401c220b81402c0d041c3c4251800125100c07041504000d4000724001454410310261b074645610880400400b848181d039104141602c0b80110321906003100e03002842400054510401c40d404038446160025001c0ca501e80020000c881c1030317400307490700d4000006100f00c05020340240407480c015000806181e040044030015218802c1e11401c081000d000f1546d08481c10201c00c4030500c4001c9001c81e616001d05007808203402d00080c0101c3e44a601e815022221503000c0d00a1404403680200134005607521000c60200c040060103d860415585490a070b5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 29125590 1250 29124340 29124343
    0x3010f090b010806010e2203050d06030503030a0e0c01090605070213090b011716330e01170408090603090a060906020a020f070302030705060d110a0203070c23150705 73
    0x1010300380034108840903940352044080c2040011303003181e035910104004101d000022441c5c00c0c0701c1c2d007004212401d989442401c04035a14051b000320b0000c000d041c403600200340980003001d14050101d41c46c042200603003485e9400c1c2c2c0c45089205250100790505010080c040c01100030740b0540d07001070a800a48103411214008550024004960503840100144012100050200e9a410328080100004000e400700340200140c2407083c80e8801c2d9443d007007400c080900071003081d6402c0308035400c40b141e0740d408140500381606251820b40007c04048440708004e5011807002c0c0145d800500c4e02d0f14084042c010310415500c0142040290320030b200180c1d00043d001c0c400e03c0352041c0170311001a100e82000c14004e0408000c52004019503010000038005690f010030680201d800469480d980d0344140c0130840701900e00805100c0c034100b0046131101ca459000b0005003041442070300c1c0700da03107541c5408040d03071502e030040c199a02c406c8240c0050310150030290f91030014030102d5083d080c101062030f03a806 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 29126840 1250 29125590 29125601
    0xd03090b0a02010e0316150e030304060b041d011a0105031005040e0304170d090b0a08060f04060305011401060305010b040e15011209030909050606090102030304060515030a030207060801050915040b03010f 90
    0xa16046506c0c24442d00388a0380018002c1c444480e4034083c001600c400c00059500d0101510281803903948100f00d403d1341c2d4a540c0000b103020f08482074030791203500700d060b250b000b0318080c41510000b40d1141c3d030100d06036100c0c404880c8101c0c2d4201c1c424001e54108403d010041401844000e114841084041504074850f0003510b14024011f0040c840380340110801407241040c1d85c003204090a083c024405100d80100d6038540c0b1000980c3ca100d4105510f10028016254590000e0955483c0a1070412030641000c05241a101161014016079999200701080352046104203107070213407140045861f0903911151440410414944040d07642c8040d940c035011034200c0c1c079045020070a07095080240355207034001c0303a502c800c085800505203009100040d441e84070003800146030655030400a841452000340d02d951003400a011202d0041c42882c0203036581c2842d0203140c001c91603072000094280f4044007100c2c4500021441e0900140480050001810384800d8a80c0c6c503548400c2c050380b00007100c1c41403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 29128090 1250 29126840 29126857
    0x1170309060f040503010f020403080d0c140c010203040218060d0b070c080a020606030c0603070f08060303120915010906060905010503090f031602010e0303030709030206030a090f03050307020c0d03090b0a02010e03 94
    0x21a80e52861310040500b1079203d05114100c150042c0b00c10000b09035041c0076144200b100c03140100b8520b904c6101211403007031101030807040050110390146490015400b45115078400d84044d05420660341c0d288012110840e00158050b0601c440b4100003550081d141d0f81102c094103103a00803003041c1c0e95001203a00005c0184006170300c40700401c070440c80c1c01c1100400384441a1509882c509010034000c200427024031410080c0002c3c0d0000c210349441c2001124900c030f0314841c0c080098182103c0540e2548240203400307c041c41d840c0e002082003200c900c104001c480c010745804d12014640310054425810090134100c480c06801500210120706000070100c0389040341020702d09901500c005048000c4844403035010f5031041c001c10001c1a0016040300a40b1b07012a801d81c9c0740d9031511094800780c910a40c008000442019a04c1c0406400502541c00f0311107a8080e00e120580210030f0001460480b0400360000d42d038032030708004c960030241c02054888124400450740c006212010761843c2d000d02c11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 29129340 1250 29128090 29128117
    0x18080703140a08041a04171809010905010314070506041401030b100503060a0618030807080706060e060f04050f040813050d0503070303050c07031d1809010b01030506060906030117030906 82
    0x3004100800301e00b041030102020300c0c09101720705044c5c42d480303407000f4088060032400c00c0c0014130318112601c032402500c2124000f00000143c3d80c4a107083c40103458288011120720041d11150011582c012400c1c90070781d030000d03002c6410b0502e00791340e002182d079014102074181640c0302d4800e212a10343d813003000c0344558151149a83d81c01d0240610054038515032040c0e08020700808c1030341c242040c100380c0d2402c0300e0300007224075102c550606040915102e4030034001c080e24035003170300040c0b040c5840c03201d18820902194007070400711054052105451085034000700342c8050200060024400b5005451000d00a1207060351031074540c0d000c1000c880c1c0b03681e07040c2c505520125284007055414010b185e40540b94140d640d0030200396640180403401c07568098440840000f025182d0b80e00e6400001d5020013520034224101d040010710640204807044101d40004d0074800010070600340301c0215940078038003070040c3e8510fa1034502030141c055a03007910401507000030002030600750b0f0f840c005080c418950a5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 29130590 1250 29129340 29129357
    0xc0e091005030c0607030206010509040503190801050f0103060806040228030809040614011b03020115090c02060a020a0c06051b070c060206010f0e01090c110304080d1218080703140a 80
    0x10101441d2450f10121144255002c0140d080001d1b40400c0362230440d2400d0301d001c105c9880d90702e4400d085014405a45400c0402c0004c1014010f500c140c0c1c090482c0c8080d03034005040020700004500343e441500a801c0c85501407400305d001418048545000d900e2200f1500080010914200b01221440c0d441a0b50071304000c00d10303465928051040400501136002100d03407400701e9074000303460078403040310820480f0b40610400301454003c0d0003038031400400b1003001f0030050711140c801d40103110b419441001449840c001503407000d001d208032a08140b441d00c03144044100382ea9064082d03c0700500d05d4003200d0026110b1700c54500f00d440030780030f4144030b4090440c1c600c1c24064020b00c0c1ca02c0c140c3c460340d0a0700c46040c0406c030041c0030f40407041c15511540d002103a038100300704060344c004060443c80d007042c1c800007400040001020413080340c40b401c0e966400080e100030855030000e44955510a01c050118100044005100f120003048218807034107141030399590949405d0055081a0305c0034011800d4030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 29131840 1250 29130590 29130599
    0x140f0106140d02010c200a0e070809120301050f0111031204140c10050c010e06091c0504031a0721020301060314040317060111010207060c0908030f09040c0e0910 71
    0x7040c4099202522101201e4001c3d800082c00396144240161840700c900d01c1c946480f80f2449a41102402c0241c540061640d4423282d20400070412590040021104408a101d03c10042007100c11041010015030459080004014102e44001d10040c14401c0312194020700c0c52090014003c1090031906501403850b09080c80c1b217200e05400821210340d0019110000a2b43c0c0320140c0c041c0c40c15152416945a4961b5094140101155650710750742707100d50300802c007070110001003808008200211a454a03074a04806503110702a50000400e071810307a811101d1511801030041e42d010901d4500384c0b054000800c0c810400c141c1d414680424140c00000500109030540124043c00341c414042c0300a620740760320024124000445101000e0001c500401c01c280c2c8289072080ba0500010021503540600b4a02140104103010501d404201d02e1b050016440a002c002d440c18004040813840c500b0703500400300801410398080135018001c08840380420354990390440e0b840741c410b1442c1c0d0310000382071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 29133090 1250 29131840 29131859
    0x1206170102040302030f0d02030307030b0612090d03060815040813120602040806060607030c0f0c0918050607210e0307080c100b061305010503091e0a0c050307031101050304140f0106 80
    0x18511041410740c01026030130318023a80001203036845506850700281559140c0b001544501c141d2000f511001554024400c1e242c80c080b580b0110301c04551001c02c5280c2ea1411819214400c000340c0340c0805c40070f0000640882c549000034030002109403000e0340015120090400303142000b00096500c40da001c1000c5c001841d04100203504000308481050070161913540040c0154510b0600070281c100064900c000c202c1143c0d81704001d40840c180910001074241007115400e00c1d41c2d40c003070f202c03481454042a00759000c2d0b070003035082800c25003244805c001c080d05c0c0c0601400c141000b41038684003c12803140070507038150260807184161405840800d0103480c1c1041034401ca406002d201e00c2041200340000040c0761903600c05c8a0007820100d40382d51b02c00800c00e09140d0f803015811081d5905103030000c0b2104c004074407980428801d1120455894075030050556a407200d000080c05141c1c1c98440c42d030a903002d40007441e80300d031040f0840d40202d03102007456401d00100c81c14844507603444081c10301c0303003403034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 29134340 1250 29133090 29133103
    0xa080a0215060f06160c061206090203061507030c050607050307020607090501120b0102070e0109020307120207020609010e0303131e05041505010c1703040302150703021801120617010204030203 85
    0x164148000140c28800c000840984143d0142c921500d030000300c2005800c40390b080402c800b40c00c0000504071681d680300241000d00318800c580d01e464980440800c8842c100d03c00d6074060000a8004524803020315140746560f0700070b802c2a41449101c482c542d0014108010240c41030a250340d50a0316802d082c200079181c48405403444040c000c0340402803080382d80c80029000d482e4180540403070440c140ca40180c1c281020b0743c00c50341800e00464008110b00485400450065a00e552210180344009101d0000c80c0522000290b0003801040045465072282020000b500401401d0302d11b000a02c5030a5070510780a03a0000320880c01c2c00403040e42c00800f203030030b4200500c0161004d200b405141d518513100c5480c00d000d0701e41841984050300007405100c4480150380c0b10400a4681c2e40d050604001c2e6940c402102410440400940040d5825101e40280c48005c1c0011080c4240c43c0d2513003005480f06160f0b5418440565512003000400d5001c20501090900480c0c00040e666810b40c014141000b0b03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 29135590 1250 29134340 29134363
    0xd060c120507020f0d080c090409230303100302150d051006081501080f0a02040f030b0f220b1f2702030c12040c0306020309010203190612030e030a050a080a02 70
    0x10415a4407003070145000c079170000c81c0405494192910380d580e00601c0180e0160500d00340c0c100c0d00d4511b00004010b015464841a103030b1014801c04d11500b01d280007a543e2000300d84412125540e030304100014100b440340c100c000e080380d1032428104480c81c50b104003280c1e4101c0f0076030910b8090b013000700955070300001b680d86c01408076001d5490807803080f80041c2c402440a4044003450100000003032429140343c0c1664003800c290501d076895543e60303003011000d021058030f1101100007181c021035951941040e150460002401c20841c8582c5244c030740c0211250001d10b403901049000100c0703104800c80749404009001c000500141c86101400354a68042c01009940b0446204100b07002c49c401d13805040d03c001d441015a0811a651603141480348504958802040305001105000f0803005c190050b611940d0201e820304504d600b2030401109481003441410242d8640c0d51001010030b1062142c4024520041e00300ca94a85d00c035070f99540741c1090514180c0794658046820712206030305000429190 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 29136696 1106 29135590 29135593
    0x150d0e07061106090712150902120703110f06040e09030903030301030c1806030c0504090c0e0403020307050f070e0106050318010c020105060103140412030203060d060c12050702 78
    0x1c2001e90b9040703046016110002d200a400011807008507410520501080701c03880c1c82d005c1c60982c0303403c8500c101c161281b140ca80075032142180a140075843c08024102c00c0e03c1c0d030034040104440f41c070095118030014004004241c1e83c2c8030a45040d24200c04801c034041c1c9030301c0d40d9180707144100114160940030100c000414015a0120002150a601c504080c0d42d035070107164108469a42c00000e0403107484030317800d200030304065200441c50b61084182185164071380c4c0c02003070282412141200141d000142e59002c00000703101840005c9101401440700a04040460360800014042d810802c040800001d03030000e04030154040c40703038100307000300600482007400070301034401250070501181c14280c4a80801c3d181c4000c851040307070400d41d14030001300006800c801941c40034148540c00320120407e500802c00500c980074481a5a44500604031000c00d122001c0d1400200745a055 = true := by decide +kernel

theorem cover : BRFrame.Cov 28956840 29136696 := by
  have h0 := BRFrame.cov_init 28956840
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28956840 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 28956840 ≤ n) (h2 : n < 29136696) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
