-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4339
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:18:10.206874+00:00
-- url     : https://prove2.me/submissions/761a1bbd-ab21-4373-b439-f26673d5a890

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 780215827 ≤ n < 780395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 780217077 1250 780215827 780215831
    0xe180303011406091801060203040e0f07050a050903100e0109150b010f210609020c06060a06090902160605131a0f0f04060f0e030a020d030b031506120304081f090b040602030a 77
    0x300741c17602ca5a0b81c4c00d0a030041001a440031509004082d558800c85412600510b002c2c0111f280240f0000c02a100300303040307141003140100b040411a2010800c84541503805507040c0104400c2c0103101c0d00030108000242c90001000350510f003050100d00c44d404030428180d45c2c2c500d03c800c11680c1901e40245540810710b403480700ca090b0b400301100c984110340c040d0000c1100560344280c410403ca02d0030b040900303514800d00c0d012a00300136940d0401744203c2142c0d0701c01c1300541c03540c1c81400c0e007188424040401034086400c100412268103c002100c00201c0c1c0b00e2080d80d07901c1c0900e011142f5094408540c11000307408200041586040a2103195a01c43c0c03041e8004a00702508840d03d0084d54001c89055030103038408101b0010080d014000c0c40c0030500c05250810440c5508400241d55807030369020790160065920218515451300c80c1034060347c00c0c0c2c0e5000c5a07a15030392003078203e070390701524141c00410b85180d90549120048601074074091070b401c000181d1443d00c0316168103000f584060040000a5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 780218327 1250 780217077 780217099
    0x302040908040e100510050903100e0a02060c10050c07050a060b120a0c0501200c10020114042006030f071d0a0b03010503100501270f060e18030301140609 68
    0x16000c3d100d480b03105655600604140341c2004c1c41183c1e080350490109000d014080c0c4825034900040e1111410b14000e4003054100003250309038184140000044d400802c009440b4000b400c0004003842c88100b4508100225954055021694010040010f21070b42048002d100810700c1078122007100314004003404040c40101d04080c1c900100480101c40b03800003284200810768200401d4880d880e50720000c446943c0203d54180d850341c80b100274041c80340282c5070300c8041840c801d40c0401100c9510901d200c0080c18207090404120901550005c4400c0b003034030b0180080c1c101002507e02440d104034220341c01c0d0721454400d0312030105040b1040b60f0079041c000d105190f5a0f40c440a24000c1040541103581c95040c003040c5424400a942001101da00b010300400160291400008001c21000102080ca00d016200349002c2d04c24041070401039070500e0800700c1d44180180c4424050036189100050340110695042c0d00c9010901c24054000c44501011708541890300043c40301c4480100f4100c44c003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 780219577 1250 780218327 780218339
    0xa0e0601030f05130302120f04230a17010b0d030905012006010609060e091302010804081c0204051008040503090f0a0b04080105070f1706010c03020c100302220e01030204090804 78
    0x3d50045400040d008001c00611003072540500410003d0358425400b030703190003040c08982d0500e110320300c2501605109801140c201600300e82e412201d4480040820540d540c2e114000a1041840c0c0d046100301c0d440c010070005a450000b1181051541c540c4400705190b241c8070054401400c4d0180c03c035440b141e441c1a4401c41d40c014400240a0300468656519050401c10000c05000b420300c038880c024400700042c8001030034241c0540c61215030900c0c00003000e558603c0c01404a000380f084180140401f10310401140282e0b8000d03200b541c1c0103071180d003c261082d4100301d840c0700e021784024107560410000d42c0741c941800c6062090340c6002821106115658284c04444e552150f0300107021039545000380452240d10011402a100386482c041d1700202d10070a074954010006001d0a0502200001440c2014020300c545900740303200403d2001744a201309409000396103d1080c614070040248446010344071502c215800ba203001c2d02052007180c1c2036a085c00002c055000c1c0681e1448000c2c0000191 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 780220827 1250 780219577 780219581
    0x303090409140d03020715020c0a06050103031d060304150b04090206070503031503030c0304141309140d11030313020303040f1404181a040318030605100902090a0e0601030f 76
    0x580c0c031801c24100b4415948164030306006580c21043c04040c0100703d50404200601040038082c0801c03c401aa2545a081103600d02000c4402c020101c906000c000414550800e900d810f122182c8507410302605080e9040200921007168001d0501d1401046041c000e035041d480a0a40d02003e8400135403000303103030009855900861022206a8070001c100548214412007041c0d00803c10350041d82000e9800f24241c3c0c8a000b580074262541208100701c4480e035440b44001207000700100010403503010241801010483e45034030004441c803844405120051040d01031004507a4400046d6065072078400b1401000c92551101740d9040c4002d0000cc1a40351030161184003d0281203410760560709408280015030344402e41008904c3d852140200124461901150200c00d0020108620ba55545000d4450740d4040b24402e15140384441d01104000d035603480a401800d41012021000361b880428005034454070f0b064039084650710b171081200440c140c0e030280c0c118005040110b80c6407000303074810701 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 780222077 1250 780220827 780220841
    0x2031e0c011a130605060d050a02090a080c18072109050f060a0b06030c0304080d1103070e0a0806040305070215041a0403031e0e0607030c0f05150c03040c031103030904 74
    0x10503124503000801c540f07800103100c55010f81c20401032060500e0840003034500d00403c50031100e40c546800000d61a05c540340e040b13400d2030200500d00c03440581c65061540c0c0d0340c1103039200701d401550007041390b212841c03078160b03014030403817150b999601c00388d02c1d0810b0700f48e01c5584c0301c558044a90b1950400d9000902c2804140b552070100e400414040c600b8903880015a803c244100703000700b40c10411720a01c80b8030401101e80c807540140038a9a14100400000000c00c09110302c5400a04003005108840f5440f9480610001d8112030071001a031301e855030303241c031100f0648004010610030042d0340014101500d87c0078840342440c1e8120700f000e03512901c3d4411204400c9404101d2440000c0c18010107402c21322410180c2000404411b402040210243c000c07013107402c0462154102040b41801c0600c242c8001541307580c801440c000521007441d0903691a4140fa000303424007482c510003e80610b01120560303124682280321005000c1ca15181c40a035208520341560701800208015a41515107010f442 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 780223327 1250 780222077 780222101
    0x13080d1802180613020c030f0c1c030506040e120403020f0d061b090e07020d120e0102040b03010503010b032802040b0306190b0d150b010207170105040302060c0a02031e0c01 76
    0x99035280903c200110180300038031403200b00748140001c0b010301500005a8a504a04491607580c8508043c901c1e440d12041c480134024040c5000d0800c4c602580c50b40089005003001e0310b09000381d035100d552940e225850f00c070100d162030305c0601c800c001528004038620320080015002211074134035912003005544426010b103490300c180ca00c0d4020503d40c8020040000c060404003200c250818220080d1182c4901d4004010001c51000b4120070440c1340d40301d100d03011404802155660b03a14031a40020350001d1203490f109520300482203482d820b0100c7c106030303c80070781c080e001e4001d1414180300d00034140101e0103a0300140e40b18030521441d2020844c0f14041e0f500b03c00303120071000c140240403003612910601140901400080100058004101100c8141144001048000414004038070b001030342d9002c142654000c601454603c0c4040d441140154025070170b4982c981c3c1c07446c02418182c4540c0040e803006a0041180007078528124604986003001d05004609e00142090507500751514100302e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 780224577 1250 780223327 780223369
    0x1b060a06080c1c031101061e030c050103021207030207050c091905070f0c0311011b050a02010c050702090c1605330708180307020406031a13080d1802 66
    0xa10100c0d0080201060707440c0210b0706581120252808140b541c0b6a02c03000078240040b4090f03800c1c006201f9002075020301443d0559403103c2d0340c06005110004d520784170a5502a002c10000710399544680221038910b5913500000c049134484c840101c00961001d4001d44413401100303030442150741c4e40c001d001d00a2003011400e00c441d16511081800b00ca9000c1c01c1c41c07003404035058030500a203400c4182c4200f00f540604144c048021200c441502600080308218418603810060402e07068000001e031107a000e20b90700030000116910025035280c4a080ba0203540500d00700e0000b0110071100c40141200c0400c1740c050742c07100c000d030798030907250002c00d0100540f06400a9010a6460b00018515001c0940545280103a05001d100031f4500744001d8071011104003810290050410100121034509501800400a071135a0303090048150a00040c03000940081c9404500304c9800580800201c2d40c03c41d007020314080b02211501c004004030b80520100d500004140005039442240051907800b0706603031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 780225827 1250 780224577 780224579
    0x1b0d020307051b010501060e0d0c0e2d0108031b010e0d0917011e050603070b070b0a050702030c07050105090307051c0b06060a120b1507060615021b04021b060a06 71
    0x1000c80c500304034044030f582a81c07402004210041d4060012000c2880580304107a0056142c1480a103580b1117401440c038180480c0d0901404241618607105854200080c501c0d203c0d003550b10100012000303203d42070300c55006101100b002c180724029202030404c0c0d00c000050811801d0308080c01c25189441a001140e1804001c01080010682000383d40310304030001c00407014031122400342c114006580c10f80c0039a0740d00c0081c2964404000e160086c01d500396140303031a00841d1400581d03200e4229481465103043c6004a084940004185c684611104024095190400c070046545800034025181d040c440c9100c0000e194139001804400542e0401c01c001e84a070070380c14461344130301001c1d0042e40030710f10801803010425404818480c00907020030003c920640c0510020b45840d00d892a004056500003d00004014969015a089a51041d03040146039a1030005985485003091007980e0400d20082c407084619050b4002c1089031007103026031114440d8140e040b4a007040c00c440031082c107030f607881c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 780227077 1250 780225827 780225847
    0x11300105040c06031112040c1a0322050a020d051603060b15092209020909010504020406060e012001020d090308100e13020126150a05030102040602061b0d02030705 72
    0x28140c003920fa5428140b01200ba0032400304850312521507460343c0c203900d80b0081410852000349440041c241007451300d40748220340e11224896401542c80c03c18415000220b00c280016071000d074410300d40c1080c05817440d41d2068082c004941c4e6100e404480a01551016071201240341089d98081c600074500041c2c0e0581c0d500603c0007030070b0640110140c1c5074007484100c1c032941e14401c14490b8030014040011100001c1260351029080751103000303500031600010813219070f20551110344218000c07101408040d40ea90b0007030301c00641e605400e90010b81110048802d0000c1810643c4401080b940014a00019064007400b1158a2481200054104001d104940040a042c10040c118107aa45902c81c07c1500710b2440c2d680c82064000e05121b0215011400031400b0800d40c0040380c00b0310100c1038249014801980c50001e41c1000a01c504120302c0042940d041c140b00b0759040d0342c40707038000382600e88611080a02d11648001d4603150850200700e1030600c2e44090014600a80c1c1c1515480e46030705043d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 780228327 1250 780227077 780227093
    0x306030c0a080c280501110a2906090103021302091c030807080703060f0e2a041a09030a03080408040b0703030501090507030903090b1e070c211130010504 68
    0x501901101c13442e4940c01a281030811189100312030090070a03c8041c82c42401039800c05d0501a0013038902d11084040b03140144038035511440780d140401e800007950fa2810208010070400780400b0390040c2ca0456460400c80083c2e0061400c900018285c4000b4100302e001c0311000101f5440032030001714403006111001ea00840d10907000140c5040a012050624840442e0074402d03101e1592204081c03408210f6100c0e101020700c0b07102296075100060130010511521450380644035558010490703002011001e07121106030f640e1080c006000e0600400303162811101c0c0503001e081500c400c01d00300000140906400000d00d00d0314440e0b10003085541c540340410044840040c000c40603d81461038640000b80d100c640001a214503041c095192800d2015140100c0308030300b481e006280001442d8028004150f0200e01191140b42c4400d061900000502e1440e070b00344140102846140081784400d46828020030150094810340303141040310540107026412109644008036954841c103000902241d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 780229577 1250 780228327 780228349
    0xa0b070206040b06221517010b1809120a32122a04030501051506040e090c0604090507021c02070b0f0405040c080a06080d140306030c0a080c 62
    0x580040c007810701c0e0648803007801d05801001c040c89452002d082031145a8211094903030680016010000c100d5820340c40000380c0e00d2030041000c2544685600100c1200c1409140e1681601070241d00c01070095503501e086101e4060f000c030400d4081d0484000c0c2003844c0d44040e090a00440d0f075412142401c103000ca40042d0b021314115250540141d003800d1034001004200c51801d0310020940c0500d9403904030808140e001c0c0a42d1001040300c130070300300c408012132074081e105032402030000304550b4031081d884100e40104209600d400150905c81084412600c11445610900d05020350b85914400d03c009045640305802504c000769440050021003641002001c6155020507924007800e205601d001e0341e14a82440788101c11280003442c910341c0b1110000351030040c50040d0050104d6240004060280001142c498180e00d240401c0055100390014044a80c0d06d91900d980c041c4001c0300018000f80d500c0181040c1d050f102c0c02111640c0c0c0d17254580c0c04002854100301030080003c4030000c0000740028 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 780230827 1250 780229577 780229591
    0xa12200a080412031b050a11060109092f153714031512010f020c0f010606080f0c0702190602010b0607121115130c050102010507022d06090a0b 63
    0x500540000550400b040340c0b00030305c21504106490b110013183c00c45a020200b0405c411900822000180750340040d0002c5110a02c103038461588583c0c4020002854180a6040426064809805440b0b07092801c416410b03800303290b0303400b480c0010700240c10310b40c2ca940401c4104c45006100129140b6014032030102c580c000c042ca04400340f40484901340e000c5003c05083c14444c50521101080f40d80da4101da251103040f00034000f40700d0004c007103120070000d4028400e0f4050601508030412a050b00604c20582552400c0c1c4603042c1030b450301d030052100e41500414052003410200003c10246c0e40d04801011141c0c000051501881c1c180329001f420741d00060040b5008000c00e11003940021209203442900c4416480e0040b0b4051420201500d041c0300c00780400e00900c8040c0c203200750f03103816401395a401d130300801e00c1c8152076654034012400c8030b40032242a401030f005880e0300102000e220ba02280710b500000302095080003500708980c01c0003c10364500a403680903441103010070000c24480740e40092 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 780232077 1250 780230827 780230831
    0x91203051306081003141e060a0605030304060c06110702060c060106020c040b0a05060a030912091e06020303070c020a170304031509080d02091c0f020405010b0a12200a08041203 78
    0x1046061203008a0417400011320b60200942e0080080500700700000d400e4001c1110745015007100c040c80c5031a0388098130002c01d01c80c1000000314640c02c0c00402c95040791010790300c50718404995160040203040c090310902e5000401c10109003d40c0c2c41c40b028184108524003e40041c1d4909400a403a20080901d05800b130744c1410b4800b006a610402d81d1021079000b680c032595100f518000440003810b1500e802001221410412950707260710900c804140c3e841d050f044035110302d00c1c4400c0c03a10400544100401603100308006010103120700c06001c0800e10180910308002d44480c0384140d000c0c00c1c0c00105100e07500118040040c424600c400c40141403009608115102107034a41202c0351241d00c2000504a0f0009010031454480002c100c090340c1e8180c1000c021a4003604e0040310303002058100ba8800d074101000030519462083c03c560700c801c00e0740c90741c2c0d250318105c0d22140301a081005801e040e030070396a0040c40d07800f643c120082c9211001565004203a01d0f00b468400311740103032003022400b014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 780233327 1250 780232077 780232081
    0x16030605011e0c021c0c030b06010c080301050d02030a0b071d0a030210210906050406050f010503061303030207050102030c0c30031807080c03010b0102010b090c070309120305130608 80
    0x22040303402c80c0941c109881d040506850f01c0c00420103503480300d10041c8043c100088000c05101e90954450144d910070300c410120368549200440341d002c003d08020702101000c20040007107181040b9034040c0d0610182c04d448002c0792507100e402901c50205d4001c404141c000c0318580c800014292022000a0b0464000d034440d030458000c19a589010b60200007403103010741c00500381e0b110b00700100d4864207450000340b081144514225020304001c0d5004c039034140c104004100820b03050004281640c9021f40205009e030394000020801010002d015003e240d0f08020030000308a0038001180710303141c49402241e0f40c90b00c45489500c0c050505001100000b641101160000b41004c101d0111100003000281c13613850380381c0031103540c20120b4140e0400c0d100340540011322440c00b01c0e800d40c5000045000308252a411001a4241e40b860b421042e48032214000148646024501400d9a94080d142200311103444507400307801102c07100010390215401046801c92460b02254960150441d454882918 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 780234577 1250 780233327 780233357
    0x5070515070507060503090304080f010c0e0f180a0e0303100e010e190b0f03061005011b03350103050606150a120f020c03040609050307050d021005030714031603060501 74
    0x80d0f18030700070700c000c010000011403580714041003900c2c0035058060640d942d505804240038000c1c10024504400304800c4c12007058603140540311044c031342d08050613103908146c061090540064000b06030108040e6141e41000301c000c030800c080c51140d003031041c0301d1810504024010741c0940050340508050a0030b82c3c20446071007080f1071000b0b00440701c682c01042240204000901c550000d80f41e89030107100d034008005060043e05130450440340283c131550f2007040184240c0740504c40309280500450224040c1c1d6495880140c5402180407480c04101908c410180030b1200100c0300f030b40f0560307030342c0e00c41018884580f40c001600450b1070190800702d403800308000b402a01d02d00c00c080c007200c41d4a540c0c2c00c02c0c0f48030029580444541101c0c00054a640d140c4410014101c03516074001d0a0291180c4107003c640d070709154403076565090f0000e02e1900041e00c0f554040301c440d030000380000c0400480f07a010070609540310307002d14000c6056200da5000d40520b07450040454045038481c0f410000065452034071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 780235827 1250 780234577 780234583
    0xb06040c0c0b0402010504090f0c0809010606090b032d04030201050c040609140118121a040f080c010f090b0a0506010309030f200f010c1103070c090207021309050705150705 76
    0x941c580c40415012540c0d51400142c5050141b0f922020740f01c3e0070100d411006140c150720002c0c08200540318400f075a100c0c40e840d58200c0e1841c0c040d440c00714010090901444070001c0c0070355070000c1107911005e4003880414140130583d081c625000c20541d145818402010740a00034142d2000b4610103079404c0c40d02d00039005000c2d16444c80364181f511a5032020b206581d01c03801160600c5110000c8040504d6940d4242c841958104a015688425031580c032120440d06240043c0c05250401044070b00466161150649680549010304040d075032400c81c07001c2e061b00f50241a4000d800342202c2100f52034501c0400c000c1d1040108103604161608000701c0010341c1040030b03c1003061a61900e00c07160050740440b61400c40c1f01000e04546c5100c0c1124201300243d0540021601882d02d981d04045180201c1a5603a00e0217078240c020281c2598401c14440c00c01182c0c0601041800286458166040455803a0445480c08000d0b10103802c00071040c0181e0500d00203030300c5000d4104031000d1620306a61942170f1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 780237077 1250 780235827 780235847
    0x2d0427020f16060216140d110318030a0507120b090a030f0531082103070c03120903030501151403150d05030a0512060604051c0314070c030b06040c 65
    0x950b0686801c030790020301c0155030548580441d4241e1710b400380d0402d420284001540030402c003000d840b8020b100c1e0911803140c1c0840c0c078a02a0000111308160301c02900300110403032400115007601c50102000b0206404010920040007204a4001c04451340c0c10a0f000e000401030411030664842807140e000254000440c0082d0441c1d4503000d42c89802103004401e82c0b40c0e1700c0b02140540f000d200d160361260345404031203000312038240007154a0030b06034400c102580704000c04402c41680c2d0520009451500030344c91945514468034041d5510300c982e04e0010200c40c078109098000030f0b07075200103000d04210402075451004203401d010041c0d180c40d40354916144001030442e000b0030000d01055820b0b4032100c0b10a80402d0f40705040da40c68900c5890300801a41048444410030703070700349000c500103040010880e001d03039101a1100140000d05e44a25035101d5103650114208050b104140c0f000a013607001900715248540d1805500780e2a5040076038440034007a00183c4114544450030f400b054000749094 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 780238327 1250 780237077 780237097
    0x1030504020a0f030c0e220b0c040e0a1d060c070609050a0605130b061f03020307110303090c0306013303060b0d0f0507142d0427020f 59
    0x10400340ea45202242101950764010050075038024000300400c0390080c0c03403170281e0708200c0c0101d00030741d075119015000d035004243c4861901d2200504501196145400170790100281c032101c1e281642e00d500000d00558100e448284280d6a8007134146840b001004070301c2c401c03c1210040403941031000501c2c0241c031645000401c03a0750346081810402c10144046003245821001c00c10107480c2800e00c1ca004010140c0085441c0d08620b0001480361810315148010400381042200c054841078070b09800035032001e004130b000d014130178000440c1c00e0380420065100351860070140c14003016040074180307080d0041c0c1007000d4408150f403070440703004080c020310800b495940756108010794a440d0f0030740040449801484203103a00080029030503c0f60303004455000034540007084281d40740502282c05000c524401081c800741000046144405814040180c0122034002c400b484456192601c15502c01c0d800601c40c8042200410a0304070080303c0c0158103030070000254906082141301308400d00c1048042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 780239577 1250 780238327 780238331
    0xb090f070f0c140d030b1302120a050702030702100e03010e071203050703050f030106080f060d151d070801060303020f0d090302102a05010c030c050d27141c05090103 73
    0x109010241c40742040f490000c3d8240d48405560000c003c1c06003c4644081d4080d040120121200d40b01c20710071106504c08140510350301c3c1d29101d0300c40010b000082d2805c01180f00070b018800c0903a4500d0304a1062142640303540b40d0708150b02c401e06094890a01541440350000c400400c00c0400c05150800e5a40e89454840d0b6540110716054455001d0f0305c0f02d240c00d191007c000071400d2600009000e00502550003450496541c42042012050303d0000003041c6001c00c0f05d004030403000d2038100700d48a01040d5803008100b030201213100d05c0c21400b03a00054a82e0f4480e002001410380510444144c0f02a51010700528401200003800401451000074001c10040200400304d0344503074031010038400c400c4e080418414800c0502100c0c54100f49050300c580d483d000b903440700e041c000d21908800f840142c90300c605003044d40c50000021b00c1c5a4004503c8041c0c8a00d40e03484ea0404c0b1850360300360900c0b401154803507001f000540d52401c65940b2040750350240f954404601d007604802a0b40c06440c4c01d10340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 780240827 1250 780239577 780239597
    0x10516020d1707050f0309100b06040605090108102c090f120c03120406021306092d05030d090303030b010f050d0b0a0b13060314040c290d0b090f070f 66
    0x200310b134240701c0d440520800c0d070404030a02c540f102000c291072000320445d02050100450820070000309214900c0b408011507820442e400d800d5010710181c0d54080c180c081500d294590355024140c42c0b6400c19440c406c0304410203504200d0b0914402400e0300603000d000103010650200d0400ca544454014440e40401008908800f4051007001246c5420b60760241c00e40e0b2742d081610380702d0043d420140e05044600d890002c04960240700e103480c4021503005d0b01d116048042d0310100116481d0f90300b51241e0301c4105802c00861245c078100410b0a41c80140e9490400151860070014211002e01070900d04100e05d4020324000c2550003005d44411105042000808000040008045001640c01140c0340b01002c9402101441103103003810465019032414010040e032462000021542101c0c02040c001030704109000683d1036100e0412a5000290410840c212a585460468000235000030710581c84041c2581c95052000303040b608a520b1a116009504051320042e010000300c428120401590b40b007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 780242077 1250 780240827 780240841
    0xe01150c02120a02030d0c0312050609061201090b07090312051c0f1e060f171c17010e01090615080402040c180f0503010e0a0503090f0d0501020c010516020d17 70
    0x14241c044d402011900240705003034018100703d180400540105030740360500c1442850318001c640c0301c0c4000500700451035945804000583c0f07401501c2c23500540da23407881100026007155500b405143c031501c64100c144e1641c502500010a00080a01003000610011880100f10034244240d04110322010883c40407520504009000204003c0d81458100304081400c40c8582e01503401d40c1ea00d4080989041c0d02c515180d07540300d00d40f40c910003d0f9440300103005d400300c5010200c580c03204001d103030a03600340424402a1803107207401c3e00040c074420b90302d00040044600b684142d00040003207030010329252a0a0401601c803503030003030010b40219164061400018441c3e214445003810411800b00700c15211840001c000c0d8080c0180c5000398038107091040b40f4080040d0508100d81e0200c000c0d2710700300c00d4001348401b45c2e280704038090300120014a00070010303100b030000d44051000c0100000c0d5600e0800710a003241c1180c04004019904007802059503983e10869440403000c0005241101d61503c40f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 780243327 1250 780242077 780242083
    0x61c051203060d061b090510050316020c030a11090109090201081f050312040320030d050f0f0c0307050d23090607060603051b0402031501030c0210060801060e01150c0212 75
    0xf06008210314039007181c031802c004030784071605c8403072845680d064041501c4034140003580040c05103034001319800b80001180300310faa05101002050a00c1528041a6104007003460705444000c112410150a03040c0c03845404c00b080c0407801001b400e000ae002e00c2081d40c0001e03040e070788060011512110000102c1e1a40c004c03100c00c8200a101c05400c446860071001d018900035080740c0402c40e100c0b07924192510072204030a142001c8000d005026040c203260750242070340c280d44052031001e6451014400e10a0244020010b4030314000600b001c1c40e0b5800ea40c0c034160b4103080f16280420240070440b12880b440307180040e00c0481c050b4024070590341d1103180c000000c12038010144002c000a041400100820201281031410407504624500078091250100f000340e000c11120b21045102a071207001c804d611030f411803100780c001c07401900e40c195003080151054641e142c0182100781e4540104001d989450310000d401040030f4110b5510b01c038010103004101110460000c1d1180328090f0a1681d402024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 780244577 1250 780243327 780243349
    0x42a0b0405130b0a2c0708160c0f0c1502121603020a0602180102061605030a1d0a21020703050703080901091e14010f08010315020c03030c03061c05120306 68
    0x1d00c101c0001d0f9590803600c03401c1c1c0304192480a180700c18541c1c2c40b030515203000304c90701840d46e035220707001c00d40c0d540c2c3c0804100f9002612401c0801400480074004220b88801e5108424061b2948808090410740e8500c510f21400d4044000c55119895030510007054409545250541040002888a65007803ca280c0060020040c2400c0c1c030000307187d00064541c0c0d003140c5080c5020b8003a00d809640309003040e1424044007080c080800c10400c0042d198801c5035110913800c070048003503074203004504080789103401c403408003c540413440481e503011003142845207451020060701c018404c80e400d42c1e03909615020796101c010054000410380074802d03030060300c40ca000350003843c5141c00701e901010348140038400d461081c1044c50740c00b029000740301d51003440c031003140150a0b20313003c9030740c0d1841ea61005012441c0c1d003440c507215800c0c4408014000b080c4000c60044140c0b092154032818103030100019603c296079103000b41001c070303850707080041d03400308035603078100751051095072203079030b1480850390180c42 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 780245827 1250 780244577 780244579
    0x308150130110d05011e0e04141501031e150e0a020619120605060304020108061c0b0906072a0302070b070807112709070e042a0b0405130b 61
    0x14554902d004401d018058588a680c400040c445a40c0c2c54001080c10062a400540242e03803030507041c000300821a42040d00f2520030000503004085030a00e840c1410310b0303100fa103e41110100010424010300d520342004000a00900c2c40710240c181d81c03580003651f0b0341c40e600800700c1e817180c02c8810710140601210340c0c40e503009003d0f50b03524040141580e4050a82a10040210390b4150031449003a205215040949901400162940e00ca0350010340d0080d00040501d54084440780f07450184421810507118920300c100200304503810440b04590500030018004800c0091a228a440d22804200c005001c95404145041d040c030b014201241044400d400032504180c0c0056201e04200001c0002c3c0f04850007141f0414005104000b08403000407010440304540410301143c651050f015000150080030007001ca6810903a10401d1380b071440c204840580e01d200044003160b113000d403403861000ea118203035103010305002d04040300c52100307000c0d40c0211406400915045088080258820342c041c0ca4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 780247077 1250 780245827 780245831
    0x10b090c03040308071d0f130e070503010e0d020601060810050303040e090c010e090109020a0c021c030206070813030f020f01050a06051021020319090303090308150130 74
    0x1500c00101011a8001e59044001449035800940c440b803048902e1810f800321080d481000003550410400d4034028002244c0c2e103c414450b0320400e000062052056102c00351020380006032030304003058210380740f014400c03a251700a4070341e004016901107001d40c1510740c3c41c02c0628490316140b031040300403410742e04116094400083c011031901e0030b01d070300c1603c1615031400322484040c0c6030004682c079494000b8203942200c16800140840f10458000e8601012185400812001190001002880b404000b040507112002d015814190b060081e140d1200c81d60a0042e00d0307040000d200200c00d0b2480c0805401c200141b00305003a494403e0050344c1b100308514000b80300700d041020507600184180e100c1d0a21030340704034440c14041405001e494003842d003108030300220041e5040040c0041c1d440240506101070281c0c00d8120f46010074813524248600a60f400070f40034010b4500a0080d58000d0141200705e49036155810841e81d004c20b101d4008100d112103070750618412144490400c2003401d110141c28 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 780248327 1250 780247077 780247081
    0x90f06031815102108030a20030f011e090c1209050c0a05010207060e150705030712080f13030c060b04090812010b090607080a090302040204180b06040506070204090203010b09 77
    0x902038035039160007400010707843d201040c2d0307800340e0b5102c070400c44080910320540e404825022941c900040c41d0f100e0100300010620a04504c0d0003a0080d4040012030005400170060064600b10b02d41c0c014054250349030500d40401440600c1445d00c1154400c6c04042070715102ca90070030a10852680a4600b4520340c1407084485501e050703a1100752003440e143c010354503000001340d0b41d8400511041100c1c01a1140510720482000b408002110002c141c083c0750700400c0100300003203081000703014a5009000c40c0c1d8031088003c10040145034084c0c01d00710420f18000610150700c0b10146208107103681810030300760305c03c0c4900c0c003600580b580480c1076510a25000301c11080c41001c1004000340f0b01c600143d030300660307290220401c1c01d0086294440e0006c2e020302c454000503008100030040e4140c141030451502d0759950005d03090f82d009400480d0100c00744034884941050a000d01040460200c401c03a003410b0801000c05d20600401101030322540d01c0e00b030070b04207640b0290700285000300b010708201024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 780249577 1250 780248327 780248353
    0x120302160609020f0405100911071403130f0b0307030c12050c070501050c0304110621071d010c150f020706050103210f020a020607030e0d0c1a090f060318 68
    0x30b1042c440c003640501c07000c01a440c12031401c1e20425100381e00d280c080c50082c9003050060b0b4001d0200f0304001400c40e504014840128000103c0b8103441e03074160006566030350a50540c10a4680030b640180c6000684040a00001c110070080c0c07640306149250005004c59607040844074800c401281c419414905018400841200030007403900600400080c0001d813110598540306200803900034140c2811000c00714841c0c507140005004c244503900f07110002c00608114003032120800c0c1d6040004c901112480d5410f84441005c03921110350908001403911740585600d030760386058100c10070140da6030382000c0560a00a07410785210765003081c810011580c480c6400f098581001116404903603004000031031540c8615100b40c58840c19502526150140341d0a004444e044003108a05200c1074000d5500161036901c02c0c401e81074002c8542342c29842c504546038150052400b00c11030301d848100300807000ba440e10a40d42e10400c009a80300c560b40c4ea10144116150b5055080b00700c0c1900807868a2511 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 780250827 1250 780249577 780249581
    0xf070c0803130b0f040611241005041e0b0616080912030f12041e120f11060414160909110a140d050c100203040e090a050a1203021606 59
    0x4844040401d0740510f070b01c40c460020b10340140189079a080600300424029a03120356030003592244140c084581e0200c000306000510721030b124881000d1103520080124a203c1000080c00030130065408200070142028081c2c0c0c03a200c80c0d0401d00c68661101085038494a5500c12101c5d61210080804203c0e489450600c1c01303039004002651084803180c40310009640c000c4121171b5900c10400c001844d0520301c00c0300c0e8048400092090740c5441040741c0040003d0b43c00410300c1c002d1031041d00c0300c070000420701201500c0048040d240100704907406031038211440d400120580c22135044040300d0000d500302496145400307100f4481220140140d0700000744103003550400202103204070344109100e0503450612032034002c0c07441100362030030b91000080301d00d00b0624401c0445074011800c1d241400c903d00003091103444440316000060f48005001c028030201c040c252600605c8140c00f40511341c03500d0721000d90f95030181d9070180481d1400308a03100554002c1e03041744d1019000c05c0c0ba001d5044c0710390402c040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 780252077 1250 780250827 780250837
    0x1103010e0309031e06070f05070b0c0a020d0e01091202150c0d0905010201050f0402061b010c0c350c03040e07050408010b0405061302130e0f06120a170f070c0803 71
    0x4041e103e00200100f116030304d0200c3c240c80d8000f4078000c10031a0754100c0125600540025540e051103030800200d80030805181149220700b00c00e60140c4c0d981c040481c00280f9103519801c0e00400c0243c51448000c5680c2d005101e402100c07407141c0403038400022800010814205a40b8440144000088000c9840808140760410308065203503c00c180b07a48030016402e850044555500703800c4242c00060040c80d000c40500424061464569486410071ba0460300b1070b81656150b001040025044000f000810320381b0034902a8110704c42140034030107071004200020010790300e103d0110041102e01403503808109550061400c4d056500301824280c4024280398054010099503500386000350b01c480c00c083c00307020f00403030001c0c0017a203109001105d840d0081d0488001c06030b003101c50010004444100c0c0c1c2e11540141140d00800c089420304604000203072842c4403c0d03c425810541a404c00315000780c81400c0784c900031028550fa5060112182c503814800d40e2001010345110500115071461300001030300e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 780253327 1250 780252077 780252079
    0x30c0601030b01061d0405091e0309120a080f0325050d110c0a080a09032003060709030f0201030216120c0308090a051c05040317030915150103091103010e0309 70
    0x32281e602d40d01c0c100d0300b009280c803085841800c80e1114404a080690101d230b4040c503440241d907650021084c2c625141083c24512200690010484070410f10f03002c00c0c07c000006a080c0109070041680d078400e50107000364002d01c8804840400004d900120300d1614aa1160000d0b203d42900e4644020151154100002c54121945840120758445501d141201c6003503c0c014010b0127644601d94030340a02c0e81c0420400c00c100007a040380000010082e45150200300c0030140c58440101c00a801d051500d40010200e000300494000c003040070840c1c1a404801a80c0c083c41c000d0703514001e60381284c01085035540024a0300c1c1002614000542d80071109a04c13032446075072140c00d9901c038411002ea81700b0780540082c160741c009040940d07060407400d00e10342000340c950811070b04140d038a403110060501c40380441000240004100101c2500a01c80980990400307403000b07825044c00010f00d60304148407141c01d41030550701e0400105110745494002d4500030010000c0c0124000c48643c5512030304010300c06 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 780254577 1250 780253327 780253343
    0x51507031407062702030606151b1c0302030c070b04020a03020d03031b020606060405010c060b04020a0f090801050c070f0f080309010f0e030901050304032304091a04060503070501030c03020903030c060103 90
    0x2001400c0c00000300384c1e000740e8009001340610b0301d44404001510810003508079584138200b145680e0002c0c001c40001002100101400c6804952103142da441c1080709030100805104104000001000300e0035500c0d41d540254400072580e589202003a0100d0068202942c084000800070041680c181c10402d0040b42c20b0760141d04004d24160203913074640054601e01d6100e01c080c041400345511598060f030f40d65004e424080341403e011800704040364000c2419a0001e4030021407021007582207001c617002409502c00070031442c80c0020303603100c0f6801801c0c001442d41812010242c20b00c0786074240c0341c800d5034100190f03955904102401c0b40c001c0c00751050107580d090511002e4a0100c0d030110680d00382d4101a1038107032450756280c1e001c40303840d210b000041603940c1310407450a00c0c0c3c0c150342000d0000341c8008280017a401c44258171322152202ca144d60680315a0600720140040d13180881c00303d044030001c1c2404102c400d00010154068080c1c80c104a4041c440883c000006d28000640241200e02504070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 780255827 1250 780254577 780254621
    0x2070f0311011116080720090c040e0a0f020705010515100504030519050708030403060c0311070f15020f180103110a1e0c0212070e070905150703140706 67
    0xe1076007a2042c2c1000b4000d00791050280980e10b600f15101103041038800c600d0689070100d81d80c2d50003001c0d0000e00b8000421400100c1907040f90506d00303041d9070400c06a4a100b1704203894842804140c02000704407060b01c0391950f8892100d0b4071340303806171001c103640714000b4402840c28070b400d44000c1e01240003603442000140700c1120458000c40440342500d07004005000c040d100302c58034004542c1400b100305d4891080c2600055104801d102030800307580324640c0890703500708040004040ea840354401c5641076808002103800a81c0f94514030000310380c000c4294021241c84030380907000740580c03403001112140021b100340750704041e50340c1c402c000c034000d0b00c04000010b01c8031007200700782c0100700510b07012a4107c081458610521011452407880c9841c281c4100982c0d82d000c1180c40100341040441d69210380e07014060401c0359101c007035000304140b510b0580702d4600400034280343c0000504055a41000802c141898421a28070560300309860341d4a42d00d00c0280f400c41d00600262000140c041c3c840c00c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 780257077 1250 780255827 780255857
    0xf0509070b0c0c1509030604060b0306150f01030c020c060c011e02040612051506212d1f0e040302010c03060b121510090e0a20130902070f03 62
    0x8151100301001400514070b0851a00074091481e04201312810011414003000788207644c108051840b551181c600070610054150505143c4a40500003d440b0400703181792201d5604d0b07680303010007082000d28001c180756405500a0b0705080f035490301d581d00200000340d2035026420542007446426104091100308100c0d003e0380c1800c83c000c0f8043c4000140280e1004003905011ba00240d801c134081851191020000b000003a089500440c01c80420241c1e42c03525844403d0307010946640846483c103240c20908040c0034440103c07440d14154500b010514001c9500c00d111850b2a06c650506040800903c0d0b440d00440c450400c0c0c00c0703d0840043d030074200c80d00d000c00d1103400b81c0c1045540c100300e07031814010840710810001400504a02c41c01c032103103904459a940b660b9107881456900d4a68440e2542003a4895820f100010b240041041c03c00880003108022403210b081d600268051194850303514040c0d16048242e684e1010311340c00c1c0040740da0424841d00ca15000c0e91140300381c032178548d9109060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 780258327 1250 780257077 780257099
    0xf06010902090f2403100302091021060908030702070807080304050d030c081e0d0c030b090601180b0309010606081f03080901050418051e160513090f050907 69
    0x304619030400782d0b00c0f04050050501103002d0005a008031071201c03a40f2000801d00706250400c44040c1340060441e1000c00940c00c00840b1039400107410342120180c2030503c03000240c0c2c0c86d070000b500c5ca000b0403907444800602c1001da001039907203940800354654038108418000c1d0388110f540140511401340080008501c2ca0000c111001c50b60098401c50301e60f141d945080d01c81800c50041550b13491010440003c1070650b41c240e1000d0071101d26070054550745110040c0e8116030003200070400340f51900f104c88115070f84600300590b0240e82480c02d429040401d841511308441d140e80400c419207000b02c1030001d44003040d001201903898035a02c1d2002c543d150a0514010303c104001030300a10300e040710920200340d902c0000c19980006040c0540360560702c01044402c1403004210303400c81d664900c03d001c0c4120203c044d0400c01040201d00582d10308241c036041c00900d809401c07240601c60002000140c800840c03416500a0005100409c24010010789040c0527000444180c5194003030520049000b403109 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 780259577 1250 780258327 780258337
    0x150c0d140f0711070e0c190f080109090215090d0b040b01030b060f061801031d03030603150405460506070f1407020402070203030418180b0c13170f06010902 69
    0xc030300400d50245040e291a0f170844000e083c0c2c0c2d11401040120781001e400000428280d40e585580c0c1c000c1080502200034020316061300300020040c1444640da002d41d032405440701307140100341c405035610418000001e0112444c1c400080403a0058010801800103440a040c12240101c1c0100d56580d07038402049004100414010f41c40314050100224010301100f01c41d62580c41070500140b599094140000b081c0901101049a580300108002007401d0900c43c0c5420210403180004d60340c102581e0782500c55891078500d904400039580b0451950a040e40381c800c0305080d49842c402d800c07889528200601c000c204c3d0596a5101e0740e0040345000780b14101c0c48030301604503a584217942000300700c0700c003450344007c00c1660700c03640a00c049005a6000e20090005003000c240f00c521422444010500741c2e00c2c945042c004120680805102003072140445079848421210f01a50364810075010886c012525001030030501c2c0410f551040c03443c0d000a11249440000c421500e0a0b0fa95600c84010781c414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 780260827 1250 780259577 780259607
    0x402041508090d14071214160302010b0f0303091201060b04030b090d08070e0d051203100501020f01110702010305041e03020c0135070504080105090606011b020102150c0d140f07 78
    0x1c20040340000c078610301c4101c11503100341d2074414940800d4481f46145500080c441d00c00e42c51a60340b03a41d003010f07024407076040c00744000d68582c00800b40b03400010780c481c000c100039980103400d6080034184161302076102c04c020b80365411226481c3c81d1242810111080111855019807152000d20441540501a094454441c5039540784247c260401484450410844102d030301d480741c0c4014034004540f22020b941328004d40700c8140420b03868900028a821000d881400140e4035114058114068500444200c50740a0034082110380790380c50455401101c0420410151076402144410507038041041c0b8524842640d032800d103000c003225030a0070740b48038170800c6c2002d48150840041d510340007040940c0c008420304007541025500c8885500b9076000700c4410b0301c01c3d0000c20030080030390380000c0c040a18a0070425072840d4000d02e0342c00030f55200300801101080e441010005105100084220742030400307604c10511840e2500c3c2d459695401050303540c03040a18603100001c54041c4104254591309003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 780262077 1250 780260827 780260867
    0x120102091513030f12030c08191802060c010b1302090d0f1a010609030b0a0e0d0806060c030c100513081b1e0c010801080316110402041508090d 63
    0x4001ca50780c150310801c0c2444030707180751a6000011074032501c900f56141d8000c50320081c0079881c0c070000804031060031a4203024003901c1401e1000408442154866044591000081041419020040c1254032910003548100006000c020950043d0001070480605803507070b0314102c1c0c0c03c2d1803541c03d078010b000c00c243c0c000184030081000704080c5450070722554003440051138000c1d070301c0d1702d5400703d04000d0300080082680004201b00300110f04420aa00240050041040b11500000c0a0315500d402418008000c031640c0440c4096541d901261400000c660131282d441c0b0000030803a44032442400491000361402c40011841048000701c0e20405500a60b15464404020030b124580c00e0b50941420070f0344182e080c6003c54600004d02601c0c0d00b10004c0082c6100603d42d000141148416004175020b80c00901540e440d102d0041038540d022030340602e8146400404502107002801a42e1000340d9500b02162007034442c0f500414401e00407400380095400584400e00251141c00e2480b1104a1603c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 780263327 1250 780262077 780262099
    0xc11090717070e3312090c1005040302042d32040f1407030303060302130b030c100c1b05030706020114151804120f08010e0621120912010209 62
    0x83d00c1ca01d07201d44c042600d000c500690310b0001d41c403c1107138114a501d444018001d40c184003071080d04001c5805001c80480f13400070022840b420040031409603101c000e000b03d40342c00555118004001007621111110405000c403a0408881103000d0941c000c0d120045038000528100089042030101c14004510b82c585040360719142e4400c0300380a1082c200f5602c1920b08520a011000103200d07201c0158082d98001c00c49038198010000403100d81c03041071700c145140c890348941d59280400c140446a408650114075103244810944480c080501e005210040c03915200042030311600105040e00c0c0309504035014152507000a03400c85942c8030680240820f0580010b406006451908e800700d44013405503240c54082020320402c04606071001c503134030f00750404000c11041d400740070340300282407600e4070100c294506040081034040190149000d152101c10b00502810074070b2105491001c1c1074200d0707040c8095009032040e0342e000003903082d01c074200640c03824002c03110500a80b03031852002072028a80d5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 780264577 1250 780263327 780263359
    0x1204060503060a030c061214040b0403050d020d0207060509070519090522050c01030b10080105060309013315080a090203010612031205010503030a08070c11090717070e 74
    0x1034000914a980c00250b059022000a10b00c5c01c2650007860a52203d03201301104a04140948050030240d4010050100030400400c4640341880e4005806062295842015001c40400391048920203200c903400000c0010410546a100c0c6128600301001d840d02d56845408021130162140d024400421110720141b081d900503070f000a802c254440c02849200840350003840c0c802c0700e011800d0766a50003c003154419035801d40622005004c0846414045030701c508006055002e060080b54018072002c000a58489000d6000e855140610080384c031101503020714000c0c194020001c031158500c50324900103480161003540c41d140c0f10b803545600000f0781e101007203640241940c0b44213aa040d034075860001240c000300c2e051030f03402c240030307588104014a403402604103540040c1e0005020754410410320a5080c0d01c0070303100e9001b00491a0002440081c2d0919042a5100810312580f01d0071032424024101d411207060f04402c4081c0c04648959511101c00750745032140c038000c1c00d40001c2190107030410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 780265827 1250 780264577 780264587
    0x601080114011a0d0903050306011103130614041e14030109020904140703080409150e040b04030c080702040c0818010905030a21051302120a0f06020c03091e0f03120406 74
    0x2003c1040c0e00c50341d00305030140d0a824207031403003d0000e40100300000140100c6590114801080f61510700c011440e20814201e4001202c000d880307840d04020420220781c8080c400c10040701c00030a1680d010180890646410110340082031091f80c072294101425102e0504042c0619441035800a0250603136544a071109100301e0011007000c012401140800300014100d20b0103800944805000000c00f00c5070201c2d0b01c0b90f07031601604035000d0345110408020000e031880403560341c0b01c1c1d41807503d02d00d0031099151112050007102c030025031103030518108065055000884521074085110451070b00115483c000b82214008003002d0700d6600200404460940690700318042040c030003070b0086c4074980c1c0c594210101c0d4001d4540714038034000303d003000703041d0718041c50400c2c240c1159a0107031581e904203030384005c1209a0540001c000a40104580500e51000c0c03003950b9240700050020b4240441801513001703210052105036102e4521466a40d00c1802c002481d0390010b004503010514050a0000c140d80c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 780267077 1250 780265827 780265859
    0xe19140103020742022d0706050405030d050a02120727080307141506130204032009160507110a0b070308091903050901080a06091d060108011401 64
    0x24000108031050000c05002000c4440038039080001d2070b4161004804081080302450b224188850060000264207a10650000703080404006100c40b0041e644404101b42c1c0243c20f406000d0740d24000411040c0400400207000c0c0d581541e4040185555500707801d0128010341140d40720400401000600b0035003d200c855034004922854106028401c1440651305201600610995003010410038200011411440028401440074002c00c0031010040400f000004203418420000321410180090b000d0317044030040c5800c0b12001040d8501500e503603000c0b40039030960720702a5002d107001900c105407101c50218030204a60b50280b818006403100c0380180b000203146680040c00180015408180000529996100342c840c611146010038409040010b560540441c0c4c40b0080e1403480001d5000b4122011281e09007400e101311f8440c003401d04024030f9145c0040140f203180107030380c00e0030f0302000d05890070810780401212084da0701c920340070f03090360969003440c2060250040180010015544405 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 780268327 1250 780267077 780267083
    0x402040c030f020d0b03010e030301231503150120030706020f1201151101060302010509040504060e0304090b1e01140d0b0303070b01030303051303080109020f070f030e191401030207 80
    0x4038644442c0050740040341e0061603c038410503a10011217205040070300658070214841c0c4081e5040d07600d04006400400908030005c4e1070303249210b0105040b59101c010300c2c8195905141115102d02d42410b1081403403001240301d03400b044024041c1c5403d4040901610803c2d05408055420042d03180e8922001e5049080c420359640810f019506581c0921b2084d03500900386400c6c40e200d80040004c001e0540c0c00c5050940740203034102001400581d810808503100d0346400c0d1030001d565907807824081e0080c85540f843d01c036280000200040c0d44440b54001c0c2c440b00408440340c0c01050604984560719840d00039040740072943c0f24440321120214400503209000c09841c1c003040d01e8900c0c5000a0035980800c004550543c034450051003450340c10f02c10705920070300303401d6031080f00815500d003e020000144602192039800003000340b8540407020030355199561000511203100c442e403901a1800812500c554012007203001a02e020039035004203e4101c0314440040d40840088134011000f80d1702c00c0400b9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 780269577 1250 780268327 780268331
    0x14030d05180106140d05190305090114091f050d0e03030105040c0206160f020a1e11030a0b060f010e03060c04030605060108010f063f0c02010209090f040c0e04050303100f0e0402040c03 81
    0xb07c41400301c50f080440c092081d0b941e103075241082c02c00034180d42070b2101c0000c03c0c07000500100b00e10b503d4400034000c0710040404040c1d00021501e80c21500c911407280b030304102c142400d00e28114040e002001d103060703440440b0144072803040084103e96415046418a5008003d8200c1c1c0d9010b03402101d0a5051850910541c0e21444c11038990700302800039804805080d20031000c141003800920740703a403500c02c03004a020b000090020384a180d003801018294900c5041c020041000390fa0048520b03a00029002d401c0d641c0901d0040c03c80c2c41e0980061000303490b201d040400082a543c0b19400050685020f01e2003104a01e0408200300d54802d00501d034410f4140c6603084091100e400c0d8481200d9502108c2d0801e500b8014107000030b02540c00308000302e0103580c010f101c91845070b81c924001950048a0040c4c06010380c0d1103007002ca200c076042d0351050903140c0c170000900c01440001300c015842041d119810a80342665200c4a03098032029104041c0207a00e5100031900501c2d05401c00c4070452101d141c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 780270827 1250 780269577 780269593
    0x17040204150609050a060f050936150406030c0905190504050115080705130b0d1b060f0c080703030e070504020f1305042714030d05180106140d05 64
    0x181588801c0c0d40040011035002d440410103854110103250240a5903c1c201c204191030f00030151050181400551040c8200d030040e1140a141d001140f10740c000b045e4408001c0000040341145854080c0e81c0c09007000c11400440c1d0302ca0601d070103901e044a034001c003100b1040d8a040b840302d00403c400303020f440c480500c3d42d2a1142c48106c40c011103008038000d0000141000a041d401078818020382d2004c81c494004031410885036484c4000e0175002d2165000c0070899080542c001840800f906400504081c42c0311401c403078001c0406861029240252518600d0302441c00e000d42d100d4000c0c110050882c0402c100d5000004d2080c0c001a00a064a4003114112030b15040002c0c240d03004402040502c0c1c1001c900352240500894610000341010340d41084841144038507281008a20000d552101445642030300802c0240c81510207203d281c1c0b419030343c64041030030440340a407038145d906603d180300c1512441d00b500018841e44d0125000b986900010f444c0c010140082031808001c00d507200d0080404c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 780272077 1250 780270827 780270851
    0xf040c03050a08030708071719061208071a0c0d0b0409050715020c0402090a0623070b04030305010608190e100207060b04270f171b0c0f0117040204 65
    0x2c0b14614882c54050340c41c0d141580004248540083c0210100301da1524800c540401200c6d1468004440d0502c22442004803622000900b495500c20704000300702e50451b1b828080442c0c0940f0354144a034010b030b1244003c03410341110156060320113840704181040080e94900282d40440540d030000303013002c00c100724140c4442e4103100c1982d01400d0102e1160051500140d8113103d2106c1036602182c04500308900c0b1008600c0c078400e00c3c0600d01c00d00c00120413aa489000300c2c60f8440703144903607040d11a903d1085150000c455070040e036048003c241840004950980100c02e400d1140c003040d03c000302c0c00c1d01c036803180030080c00d52208400054001c1e01c0301e94038110824001001d0740c034050700d40441c5403609201444111513403401c0c19007001c10032210407150b0a2400d0100880f941c1c100080040003030241c00c21410094181802c0840507800107440b03440c010703036041e01c14096140c3c1d105a03928048010203011860f0810305030140002c2e500862444800003845065800600242000462410404c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 780273327 1250 780272077 780272083
    0x100213171f0f140a0507020a1a0a150b0904060603020a08060f130212040c08070303090b0d020f0c0615121002071103071d0c1215010e0a0603150b120f040c0305 70
    0x1d01c41440701c3c0400e400c10900400a00401e0340181c99440103000c0c46005481d001e001d43d002954800d059a0f115001c900d00d501150404111101400c0040700081c1e9903011015007544650302080c01241000780014280340030380700303032200c101d01502e0300001070b6540340401800c0105c1c4d280c5207500000551070f004013808184094003508800448040c118140780c10031001071002907004005a82c0520bc0610020b07501a1155040318046003203541c4039807044031510040e014224112844000204420900c0400041c15034000c0c0402e480c40c200140420051001a5007441d40d0324806e64030a600d45448210a0390080010900903604074940c01e5140c80080e080c00d0325640300d2608045d00800c1c0240c600ea1514035075402c09501542c00e40b4108280070034032000c600050442d00d14044800070050283d014200017a80d0503801411000490b450b100c01a008000c050b0690508504105012550b150500304840b8544525440c1403d641e4801c03a0100b00e10728010800c46244230404400400180c0c20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 780274577 1250 780273327 780273341
    0x20a020a15060302040f0c0509090a0b100c06140103031e050405090f0402010f1706010c020f131b0302040f261002030708071806051605100213171f0f 66
    0x500020410a03e0b6004100c203030303003840158180b05031500b6002c0d14002d4108080f00c0fa0003200b51802946540c4400ca901c0c014031450300707200e070000c1c0c1404940d914654403400c400b209503c41c0c5800c00800c6205405940040d00c240801804100350f9010702180402c07011200403a8040d51500d545002e80b242e000c50441c0106580000211b040b413020320085607001680651030b01c5451504403501e100c0244460101c50000c2c2c81c103814410244902000c0d9111283c0010003540c02070413819410180ba02210000d2403458000c54501c01d070341c024100d1691090080b20211002e03010180701083c03d142d101c9460030b04115480700c0412a070030740c40c0045001885100212450420b0068907032600c850060141d201c001d09a400f042040c01c42d4080040a00162109841240c50181c0d10790f0702c41c014000e460940b401000d080e51040c0c942d5240796001c903030001d0080c4401900a07a00c1e5960b038440a090741c0c05454042061900962508100b031100002940f8650505620200340c00c1e000300340300001c071414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 780275827 1250 780274577 780274613
    0x20d0608100507020a030c020f0105042403050606070203060412020109020a03060e0c010509030303162a0c1203080c0d020906040315050603060c04140a051f08010803130504020a020a 80
    0x88421444105810301c039040d4005800c1c0040d011070001030b1b030020005000240001d100301c108100341401c5034498015580507180c0f4504052890f000d4004030400260710b189540c000905200010784981408019960b856602030300030600c94881d40d81e048104602140c101c401c56603582c001c0400b51303035184c3c011001140202d1000900c001411141c0d801c281442d41d9a6060020802c5880d0558400004aa9200486111284083c108000101c50b03408400c85400b4070100b5034100040c900152001044c00103201d4004117964503614006203071108035001c0c001e00400d10001c00104500407050081c0084c0c0d12018005140445881c00035003190800c0d0801d85404096100c81440041188607440e00000e08130020010b03840c043d0205856441a07000380ca08203191140d03602d0140c3c40b500404405808014030010a000001d00da4454a45440300b04100142b841000018100c1e00841299042030403e0284100d042c00c007011300003c3d5024268000840c070074140650045126100403008010b8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 780277077 1250 780275827 780275833
    0x1030504022b0b1f0608060310020d0209121c0f09050a060806030105090c06030a0f090203060403050309160302010906050f0c0706020334030c02030f030315040c0807080402060d020d0608 82
    0x2e441e0400092a810090203c0004480d8600c6032502d15134422860080780d100d0b00c2d24840c0e0365a10b201203810302c0c1442d24400b100c907001003030320b41000d852174026040c104010740b4528500106901d206130381c1c2140d60140f0b54030381e401d400d41d84641c610520181c80580018208440d19650b9940480c001c1000c907846100090703030020a2041c0c40c6004c2c054039810024039801030099090f1440010160710024000d814500d5a4200d0001c11011396049841c06980003000e446041c901400d0185c03c0780e004956900c410f005021844440c04c014050300806d9a4042e500c000d001030034440c0170788070b59000b00214004000c06002c078104600c3c081080402410450340a0350301d405013849221520740e002034254894082c0b20010b10b6113516103d02142c0390681628000030a022103001080c208031420b0348400b42c6020000411894030341506000003400c2055804114a0400d40c10072545040c0680700403000814034004540075141c07200c050619685496001490000244d114808481c1c555100c241150 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 780278327 1250 780277077 780277159
    0x40e0a0b1002061014010c050123220602180d0501150812030a110702030d0201090312050606120919050703050d0512071202070b0c121b090103050402 66
    0x410710505400110401e800109901d0030480c9030001100c00602885409030340d4442d08000d1a8401c00203004040d40090081041c1c003c88003000800002142d84030fa49030010038081001c0b10101e015070151031021026580c3c60700e080303669420103503200400051080238075440784001c07030740c4200404116034400c03c00002c00e18003024440c0040e10141e400070640d0703001203201000440e0850300712a880f13031441c031000401089081c00e40d2107a000710f9070081d4152080244800c0c107250154881c4960b40e0280e201c407001c00000c0d03045c01c000c0e40c00407a48240c0060341802a001001544410385400c29081002d1756441030318005014182c280b045000e42e120307440903404000784101840192041c143d14580b803840d05503443d03801f0800c0c1c800582250100609060f50032a5420694107981a0640c0015100820700740807007040d8031500054001d0120091500100d000411a603004540241c1d2222001e41030a000500550040c480188241d0b0011400034071075082d07502c15205c0411a10300100c80401803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 780279577 1250 780278327 780278329
    0x2210313080c040f050603190c0b0f0d06080d0c0b040c08060c04030215070c15030e0d030c0f0320091206040308180a03080a0c050d060f180b1e0105040e0a0b 69
    0x4d12120107102c1c1d00c0e90300d13040912900e0b03100800c5e0b54100d540e4041c120201d1051600e01004111155442008003c0d4042031842180c00e41300010080b0b0100c0f20000e2010356218080d05450301d0450482e2000700d0707212030900340003c00080025074001d026004510a069580700b10324104101101c090980d8400000c5c244114904003c0c3d060003900d0f03480c50b041c140081035450740070040e601d00030484800d802d0494100c2891090f0054039010030141c00ba201e0341c0c040b540f8060040e100301314a44000c140c5059480c1010b034402e202d86c0400480c951017000e00350411916090681d48104203164100e00c5006c040740c0c0c484010400305000340e1080da61000f37146400e19581100400e039401020890300201800070209a0114016410030500c480c0013695100280040d151031160024001701c0d142015400180d420381c20388404101c0d5416440410040c007100c601e00c08039034800c07800651011007401d800e04e0300c0361803480e02420620103050051426445043c6403c950388100d41d4511190b8590313906d4001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 780280827 1250 780279577 780279581
    0x5070f111e18060d141b01050307020601050120150a110406050f0d1d0604030216050a090209040605090a0b041a03030d0e01061706010806060603010302210313080c04 73
    0x41914007408021080e00c01c0000160166500c0980348034451001c070200380d1980c1c13076400011140e6171042082a03818003000d00142c43d0142d90302501101900307040202c1143d4010803c89101e6030803507001d080241e0030500150380500841c9204c0e2048403440d83c585803000400c08c0101c4d24007819240000e4186007000514058500fa1955070441f44002d00080102c540c01170f0980c0c540d410407060081c0c13900b00c1d202c1494006c0c14181070560f020b400319207200d0081c03200071607490b005a00030741c240c44d0007500010200510140f2485501d800c1402d00804001f19030f4117501900c0140002040850034968480002e100c803002500d54200790703aa41c0800442e186000d101d05841c0350a01c0303072421030907068040042d0303c901500d0450791216444a0041e5a228020742c082009014031444c000c41d040d0706020600d945030024001c00c26240303c1d100129202e071920741c0c04d0340e0480c3e07401855915010440c403100c009003440c480c40d050f0584400e100108400310f9110084019043d00002011840a40420041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 780282077 1250 780280827 780280849
    0xc0513050409030f08061306180c0915080c12010803040f2304051305070602030c0609071202010c0809040c120b0406140607020f040e060403180b071205070f11 70
    0x4499482c2401880c0001c1e00011030381c0c1c1520082c100700c80c550f41c943c0701140c102c425801c4c41c50030301440c1c4580450445104c1018010000203120100610300c94500140e494025034010ba082a80c031181c04050341600c10405d00754000d00d01d020f03241c24005407040051079454281c11405164001142c01d0011081c0c0c260710b64014698124210400c43c20110620185064601240e01481d00e5000080d101c5c282c40c00141010b42d48601101e6000e80d503490000e4032500301d40c0084449004500100e0001c260000c5d01c10143c500301900008001420360040d0f40d1a061414101d840600078080c00c0020350b40c600c650714011209440f04a0001c4880d2940b008452010460310f00c25440d0000c1804146a00408845908015142203542d101c1e07a00002d10441ea601c41000e41c0941881d41e442e040010106016018034401e41b602d041c400c004da461040314608030300a04036245014405500460100181c030010036040b410607618003100350702c03445000c1d005814180c4a12a41c121505020304185600c0e81c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 780283327 1250 780282077 780282079
    0x2090702031c0203090a050f100b0307080607030c110105100f0e0907180204051309021002060112020402070c030f1b0506041d060103020405090103060b040c1d0103050c040503010c051305 82
    0x5103401c94191010b0100309030080c45880c015408400a81e06810801403100b20039041011113558000300c440c09a521a0b0305030070600c007107040000c0102103040025a0308251501100900055565444218010502040d40381c2c204403241c0d01d0000d1030b00007031040314014044420361404503820641e8a044920303103540092009941001085045807000c110001500d0300010080c400011a0910001a0040707800040c0d20000880d0175050f601c6103540300c4980315200380d5004440313600802c1d060b80c49103001d201e0040c0e0702502c42a00c400500e8035030f0050150b180300d29000c1110f2501c03030b25200e000c0700307030140d085503660f41d900700d01720300444134002041c0204000c668003031819050100c1b0143d000c000101454400c0422800300c5c0b2a40e00a4060303901505015000341146d42e540d043c0b1502400c1001406400f80d031134903500c00d000b10310070700011800b0f040c81c8040f1440c110b00c90004400604004005105071034042c4030100c4c6580c1e00307000b030803c010510fa030b81d0782d00c40d00b0301001e00400c220907620803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 780284577 1250 780283327 780283333
    0xa170c0d020108070e12030a03240303080403111203090303060301150f06120608060c1e041a162003070e01080a120c2301180b0105040207060f090f02090702 69
    0xc0060ba030003152203038005414a41135120030121408100500e00300003440d201404041942c0d964546d25901450110310051054504050760003000d170280712084c000034000541d46000180443c1c00358070b2040d0b00500c40700443d044010342180e9801140c00c29035072101c03aa0400018499580ba0901440da01011540f140303104a503c0d1140154a5030a940b0031141444202d182e0040790107116403040c401484610169016843c00c0c18412689500404058080031500d034450384800f2a9401540d0607201d501d54004a854100f40100302c042d00070342c04610030010074010300b4001500d00e020030324246804020300180310700305c00109410401c687c2c0289501080540041000420000351803420681060840103542c0000704d0448006108090150400d0529541043d055001980000911980b40c0c0200044000b04090407443d00d4a07020244c002204070b00140851701d0b060303005003841846079500243c2c0e0400e10114500742d0b08011002e445100010034403000b58105030840f543e00000c1384c406 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 780285827 1250 780284577 780284599
    0x201081602030904090305070b1015030e0c1e0a03060501080d0c110405060d0506010605030103210c17090d080a02060105012607051c0e120427020403020a170c 70
    0x200035964040d0f080840e1240391a6a145018180650200c03a94030340c002d0801c001c0791414000b020044544ea2080d03003003051070301106405551191003000c1c6804407000c0500000340c0030a0400c4240c0c051501104070091503078458504580d80c0107941401107116450201c0c1541c035200050b8146801152280c3c240301c00723a4006000100099000c5039031034001c9074005159201c010100341d008400b02e800030400e218500021915a4001c000303503040703910801a40070042112458a840b08400207416030106d40c1d0310b549003000030038821400640500450071035041c90b074a0710009010503e641819200351a00055420100d6818010300303024140a00f00305410080910342041301c0c00118842c0000c0800c1403000c0b5406502c600f0840e2030b0b441c03140202c1c0311206e41c14115803000303005a0580c88214801e0800b84806420711105032000c951801c2e010107540c80e02010b4459881c1812601644c0c025030802000c00140c0d03503040380502030032038103402414124944001074234180c80007000510030a0b030214 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 780287077 1250 780285827 780285871
    0xa081b040308040b071b0e060913031707030e0106270203010501050d0c0e120105070206100b040e09190f12090e0402060a140d2a200c06031003020108 66
    0x1c0f2412100104075103666500700b420015501443c5000c1d121384140080740018891500d0710106024481c201c40501058907800f10030546640b007024001d020070200003031040c1d005d041d810095407064103800e011a14510f0034200a08480454000f48080104c000d0703d040c030f5040c038004600e417011039441c04603d954140030001e001401840c0c841a00980c03604c15161740c2a05c10f11030a40c0e03418000d041d0140b2501827044880c06080c040780e02c2e100610504002840c0c1c108014210304c101c0f0451404036240c1800c0540c81d003c100f0f402040d40d9064803620078140d980d034022006108541d401a101604010003501e0400c000400440f00e443c2002011401405018450382801e03400c1903046a0b90784d40c40c01d071000d0030760344201100054642c800c4003180c02d41d045076107034000c500001d8001b500c5801000403001003100061201c10700c68002150988411280c3c10081c1952070708004000440d4034011a000000c1c000c4e9100301d40c001c1ea02c106428040045581042c2e81e2900070000c05c2d0b11211040c5945 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 780288327 1250 780287077 780287093
    0x14010f03021c060207060b031c0e1003180b04030f031a1017041401111c1d0102070c18020712080709090203040b0412090e040b06150a081b0403 63
    0x10102034401c07600301d54100314034420b0296240d495580850150340b01d0942e400c0030301c010940c0c0506540a07000b0070f08a034070800301419010382035455035201c0c0c0580c1d02e01c0c1d000703101204040b03400740410305690b9100310174140416020101c2261007042450402c0c98603107001840e075480100a070050500b00440705894281512100d40d0300001034900c0c01c2450000002122965500d0348078495985c6010107110900880c184861090303c00c240080c006000d1064040040b44104950707050380081c2c0f11254a08400349800c9850b00c400e03a28646010f80120b100701310308aa2100348c0c111400140d1120402c8101d0101c01ca8005804142d0b200310b052003042d44038152403001200303124041090441c00954200e004181880c09402c10000845d182d2078140381c1100c0301c800c01d660030b07039880202200f5110b04900c903840000035030b500c9401842c90f50304c03980d451900c26500175200c1c81e03201ca1040003c1c22070098040140c051040c20359198152030508290310400c65035501900b124414040005201048140d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 780289577 1250 780288327 780288329
    0x2040c090b1c02090603040c090b0d080f0d0615090e010f0303120b0312041403011410030803060303160620032412032a06040b04030309051c050d14010f 67
    0xd19000300b519903812800c50000e120780ca2000317500800100900044c41310306a501001d8945100c000c0000005580400503070700303071980e4010f08501c020446a00382c44583c4001e841c1d0303441a170034041480c0d03886500c1c40d548120119400b000044d40c04100700054031001c120b480c010143c0008102c0074509684005140e005c056042422094507140f0180490300c00304450755101403141c136499229621810f084040002450600d80310703609002d40c5541744802150498094104c050320b10b90700070b242d0790740c0c1100c03904003c004942c140001e001c81302e409201d0208400c0090f100b05400074100320750780303001008000701200c003008500c4240100001071806880941380d50440c12440c080141d00030f40002c0031904002082c000601010840400050100280803441c000000941d641c070030000c080180d0710f120858000d0000c11940380420f001c40d01941c403801c04e05000c4c034140c449140303500c184210380016486104001800000e2400c40c0122184601c81001710300004804641d450000c817a101c0b00300d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 780290827 1250 780289577 780289597
    0x6010c11150f04240203091203121006111506011d030709020a0f0509010509060904020c0106150e0904050c0f0a2102010905060309150603160b0702040c090b 69
    0x34018981640e640d01d911205282045824256540d0440c100d07400154110f440358001c0d0082c82c03500b20121060110201c495610306074000c506000041040101c4051030304074240e07090208106101d80c0071000b03c3d1051240010400140e40249001c90013000314501d400704000d02e400000c0f640c0c1501180d13283c00c0780c1241c07027440c080011410386210890312502d02c02026905110301603000516082c00d80280103d0a010344590841b04034050064549100b12410140024002c0264203d14034040d009020725a4002d030005041c112500b48050848440c0c2c4c02c070701114030300100100394207503201c43c84420311030043e0f074161001c0c1800d590300781c2e452010810340341c40b400100300c0c04136054030f411182e44028000f40200038250120a17542c0040e5074081001030380000c1000e0408607103420010200c03405101c05d0700c01061441e506c090885007803540038003400d40c10b004905907072082d0300003010a040a01f20001c15559242c0151040204032082607010741d05110826000304144100c000958481c1e800d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 780292077 1250 780290827 780290843
    0xc02010f082710050907060e010c080301060810210b060d050615010536040504031d01111519060b030705130317122a0903010609050c1e0306010c 64
    0x10301c03102c56414140d5400c90311000314135100410510500005081003100c146803107124044920300300440348403d10040c00341c444003040004000051207641256440340001d01949000c580360740c911190307108a04601c1c002d02e08262090f1090220031032023a42c000030116903081021049a4881d0740f41ca00c0240b44803003801858110003081e034015801c1b219105034004402c10000c082c500d144d0030148070746a480d50b0004000c4e48140050906116550203103415482e140422800d00515003103041c07042c240c050402c41c158900c2804480c00b0403e00100c5400c107000400a40b5045443c004000702440d444040b0380c4c02c0117801c02001e40c400d821260006024a0310700da44045031400c00e001203642d503200620580880c4440c0c861440765402402000e8010180100d403504c1d075040c50748510303072812801c60b1001c214034581010b408a41c030003070581000c05000490104e564602c0c510444100b02c440c0c2c8404080000c0c10b10441c481e17402c2420740c0c041a0aa10380c158100b140008000600c3c00c074000700861 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 780293327 1250 780292077 780292141
    0xf0d0518041107050f150a0b011701090606260c0f250203010506030d3608071a03101703070605040501020c0c03121918060c02010f08 59
    0x10600e8031262000102900501c4a101000b0b001080359020000699190040000208084401207014103103201744252140054441d058484018490501c045052000000032120b000b403000c2031090007081d0b092030002c2d010381f038104041e00c2e0000c080c2080d9900d0040540c296500ca0342891040c0e080192104882d0319040f02390f0000d406413245608540030480c01494440c40d040b4004180341030b0501c20740007071049032910410316688070010040c0d01c000c905401e00039051050b91160200181c00441201605828503000001110a81da04419400c0d001b40506015510f800c50072007090b01e080c503040c0c4d8a180307083d20b074004040c512402914003a106101c00403000050410960313200c160007c0381000346051a2a1083c001c0d80005090403c1e405040d81e011301903d000301d4021400000210301030b26000c0c030001c0c1450703c40d0804201d9800c0c064078000b000d0304085596182c6014040c181c46003482010540000341601450302e035007004000202c4200001d9401c05800a05d1021100105494070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 780294577 1250 780293327 780293347
    0x3060408160606030b0601090b0c06150609120f150705090103111908061f1706061e0915161401200415020a08071209170a05010507020f0d05 62
    0x4a07000c290240019003010008410f212909003183d008000c00d89030355a0b0542c3d113001301031701c501800e80004d100342c11030000030360440c0c1c40804194201c040200104d150010800000303540350405580c200955201d41c0b500c100040f0104100102c0070091040c5194510340a400141769200310034031503040540310280c00000400f6401500e11414242c22403001000d8000c03401001f0210880b80c1c10b1003a030440030b04c000841c1440d03070b0f8000d490020790341e860700c01c09004110b81c1000710082e1065810000401450b4156110488a0000f400d028080b0540e00c00e00181000000c0e0b404003075aa01488007040f070a40c1d40d1581e241108482e0354005400c0085040c0f171a0154010400d0030810301c5400000700c01050382001030750003803050b10704204880413985083d42040b81e03504919000106601020040280421640403142c0c0e40036941d440c2024419894401e001d2100e0030801032001c0700e5210000b01c104104c800c3c010300d40d21030010310040c0582e410410310b003551072450f2b5006c9803e0001c0040d101d0300c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 780295827 1250 780294577 780294607
    0x12030c010b0f0d0f0c090608060702061605042d0305150a18020f03070924080109020306011a070c170f15010603020703050c0f0a17070b042306040510140603060408 72
    0x21b0003035900800c5500e81e81d5004c00d03202e0608851850050150400090100c3e0b6910010212000c095540d141010b0400d24025158070582940030b840d40c9001c503031004030164120860015510072400f0b001e010541048808500d074000e04210151400c014206010108049511109030380482d800c8041407400e0002c0ad0900c08a6000540c2c01400e08210f241005513224050020307020701d00402880300e6a42e03808600b01c8400d214000d50681101004201d0003d10303828049040d00a42e0651345440c1c840d6440c0005440740b075014001c0c14050240100354903d0610600c00b1104221014102ea003080008a10588030140104d200389a8045035400505101c0c00503680b10641150480d411601100855551a0b000010440369966100040c00300c6c002da0302e066079800c60b849405204c00c0d850710364a4071801304d00e26171300c5604181288415828031500708105030040340110f010300116004c0c44008001d0b19102203400e9150007002040c8541c5843c00190303554095040007202d9150101c005090907 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 780297077 1250 780295827 780295829
    0x8030406230403021b01080c1603020f030301030c09141303081509180f160b07030509090406062405121e07120b120a030f0e12030c010b0f0d0f0c 64
    0xc150385580c0200000c00d070700010f83c00c0d0b01140d40301c85d00b03045496500045600e00c0003116500d001740300030700c4000540c1c1504080c84c2d2129100307005a80108203007840141c0340d504242c1c01902c0044842c8020080400315120707100541e18990f03c1d031440c0345800c440914040e50f23030035002401c0054500000700c01c10503034004110701c5480144001e0781424145400440110101480b2001d070041036150020381e14000380c0c1c02c0d666200b0400b0302107013910b000130501a58004007401d500380034003040180c2c12681c3e42d5803554170a5100b1303040064828100481044801da13003520b400030840d00a80d00154030f0303800401303030b0f80c1c020074a5129000a0b9605580450b401000c41404004900d0075010f000c0c14070f4000052850001e10060b040084400c40420000142c040c1100300c02203410200381040400e116074082c03400001c15003005540d130301106011070000d080d8080e000304160030214094480103022b00680e0040c21081350700004e44001980010108c51100f64020009404074002c80704000380c9001c0c0d14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 780298327 1250 780297077 780297131
    0xd0b1e0d020a0f031115090d0f1a09012306060909040f050106180b10120f0b0307080312100501080c030a090206070b1f150f140d0207150908030406 65
    0x4030303200f035036403600e160b0160070401011306c00c00e002da118035114030010040e601004001412a0140e40b031790784800021980c0c030401a10a020320302c11a28801d4503a608d83c80c0641d00c4900001494004030403010621100710382c1c494000900c4c502808a9541c461003540c40610080352005015221481c2c50308480741748103402000e5500741040000c1c3c500902d03414001801100743c050041e844500c0401c6115602c1401010114040d05109459561907a1100c201003420750000106074002c200043d281980e02d911445440c1c0c0f00007840100c1081c00c40342250001c0d1001040d05880303041c800041c01d84080105039001100c0c0210010b0000700d0241c000115454028103601c0c1d94120a04140200350401c81ea40b0300000c184805002950710a10584011900c8005030000e800b802c800007100d0210140050328104080b000442c0402c08084d8001c10f00312012135001030380c5010b141340110510321a0f40f0700b40d10340d42c98400510045031080e400c89a000e070380f03c0c900040008191140009a0680413100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 780299577 1250 780298327 780298349
    0x2f190b0c1c0c020d09090c08040b0403030e010617010e1c050f27090609091b0a170708010c18030204050a230601020f0c030c0d020102030c03030c0d0b1e0d020a 70
    0x400c00041d0040b4a07090314004603074880c40301c50b4403000d21b9415074812054110004250341c4c000b40108a0607e101078000b032003894007142010301c4000d110b003503a009070030002c000714a00744001c1070070800340310f455036445600c0c001d440560324a14110f00d80707071a65441002840000540f030f01c200c1030300108030342c41c00600e5001c840101151036113144079150a02070183c081c001c0721001c81c00030b151001c0000e1061001d038004101d640c02d2034104070b02100c9001020740e045a4180b00200f240c492800d4081d00602c8010004c081942c58202c1250030344244020305000d00c601d10f41007806050390b50400c002075a80558012440b52201400d41004210707407481c9085003c0c0b100312580300e15020f2071031103005400c00d1742200c000702c0005410310b8440381040c03074181d41640500c0480c0c046042102c0c19042e40c500500581c1d040c0a01c40c542030b411603004840c00c0c00340d100d00103541c1c244200248102800010242d41c0303200d003007022030681c400b00500d1031100d520400e5006450800c5582d28525240640b401c0b25007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 780300827 1250 780299577 780299591
    0x16030513032f06010e04052107060e010216060f0518151b03071112030c18030c0d0f062003012306160204060909050a0b072f190b0c1c 59
    0x1401c000007001c0d02c088131326014110141d031552300c44045441ca10111100514648082680c461008004000e48590b103950280400f100140040c8643c801142c040c200c04070358240c182481ca8100c0b60018100001114505042074620700300140c860301d1070186a1320282c4a4860b4000300016200302d007a80700340014000200441654404030030301d602c01d45c050440720405203082207109a4001110388040c420f4081c008401e5480c80304481c88800307040907041da0320f004030401c003040d000503000c0800c1d625541c0c421900c004005c060b210b401784003a40c110003044404009600006244410305c06c0d402590280740308a030b440003074468030b00c1081030010245130303940103140d03207065501d01000010303032183e440c252000601d80080c4c0100700c1c0880e4800083d080d504500da0b111002c3d0716015100808001c50740b8a071051100341d0101201802805800d0303040d025010b40401450422074403040300f445000c1090140000c0e6000a1240e0450400181942c07581100402c03280480c241040c54007010b424402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 780302077 1250 780300827 780300839
    0x301060f0e09030d15180606080c180301150f060f0203121e0723070c0302150f12011502010219030e03070b01180501080708060402091e16030513032f0601 68
    0x801c16041325800550700a032034007280c06007000c50307c03d48100e4001c0f6405000064400820600509610400705a11541c581030000401c2c03c44146001e0f100655502c0103040c80040c142e01d170600d0081074640b130400304980e001540207440c5d024804091f6054800000854240103a00a0042200c03407003650913000c1e0724110b07000130010400c4001e030140d084030419010000d08580300490340320a42042a01d1603aa186038240109402c002c0a409140c9005000040e400c4100c0802000d00503200d40c4100c1465041c0905280c2441340c5c03101c1a010740e88104004078640035200f80410114040341000540f8501c802103260031440340820061642042d0000032407000703141040401c084480090410150380c0b242e03004c80d513408582c0103207455030f80400001001403a10144999002d1058481003081c503450503144004030005841145844241215400708280e040c89100c0e4021041260040781d0501a100034001141c3d041d08209000310443e4910454030760411150040c2e101003084980c81e40c2e40e21 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 780303327 1250 780302077 780302111
    0xa0809040f05071806020d0c2303030108010606090b18130b060a0203040305060601020a0807060b011b141005100303120b09090703030221030601050a170717060301060f0e09030d 78
    0x140042c40040c04044d80414a2440090040b070841101e07155a0b032003106a4540322000c40c500d51900302142801d42007445d0801d0140302850017030902038000f086090078510003600c100c48680040030580e009021100307110440e65001880c2c031806031105040c00c43d207060341d64040c01490041030340043c0c00144141c4010350000050040341c0c065425100c160701e1b401c004a0702c43c03220130406080f440e0140301000210b007550f801000c1d02c3c0014100744038101c5259000075400c0644950176503c0c03014104c25451554030a00c1400744500c000c1000304140c6c40c01c4020202444150300000c1c0400c1140c02201e02c2e490301c4e075030040ca000c8100505e8261140ba050f088541d8651a41c04110b0044c0614900710411036a120400c100c06000c0c0060036045556101c0115410740001e031100c801c129210403d42c4900e42d12030001406604150764030078041c0781007801030700003500c049c180e42d010341e1602004010715030805e008401682c1220054490584808005030f00d540581c08a11901ca8940001d55640324200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 780304577 1250 780303327 780303347
    0xa1416020301180605090a030c080a110607030f0c0c0309140303070b090a17030610030e1507050a02011a0a0312090b13050937020d150f0b0406020a0809040f0507 71
    0x5004c05201c19658150b840362265540b882c000c002c2181c0b031540c01c00184103200a4009407925203084e0f2451104010040c3c079160090b9030050209070344200100104501e40200d80c50341c803103800c01314051080e941c4c00600c46000e91240000619584a20049036501030044600b015049400003200d8145480e060b03849000310002100c80423000e461680b80c2c0802241a2841400c004104411010f0076500540241561031103030441c0d8007600600c0210040070002e0300b4010000e0f076960340d888041c805070107400c4450303c0b03c50341c594038884000c0c900c01d40e4440d1034513004e030303540035600444500c0c01d04810740346400641c01208004101040780b501d501c20603138260088074030440761004030740c80c1c1032102d035000e0000b071120f130f080b416003c2e0000b10110840301a40760240881900185045070604c807040842d52521f400c2010051807403420800300c1100225000038003043d40d6100d00c0c00d8542140030b503442c202c0b544010309400f000b280c180590f81e990b40c01180003c0d00d5144c1032165240c104001001c01c240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 780305827 1250 780304577 780304583
    0x1401080d0906080112060504021203031e06010e1f031b050901030c111911130e0c040608060a0506010302070c09050709290c010603050d050318030a141602030118 71
    0x74418000351031481941e881c0d04807146450510402d4640b51500e00c040d244c000c00030b0340c04c20920f001031850500104003d521a141341400643c0c010304038024241d40d8100030b4215810084480091140740d6140503443c1a05a4100c25080e0b181c49011408d40183c01c00c2e040110680c2002c1c0c244641c5a60888010319818809aa04104d034959049050314a11185e02d10b0307203a960b129040b0326161079900084a4000d900a05280b01c80c0d0412000282c1c5881035002480c140c603448814846001004004071400d0b003104440030301c429402c03c0d150340d44d2a54000c041c0e43c1e800d51208041801a40250304440c070a940240c5107040c400d803915925005020309031013080005440c040c000904905807420b01c1003000080c0d403000704809075191000030640280e070024034195a6a40008001a01042020b09400c815114170f034403450040c88c041c4603d00502010030745504200320300b00025034030889140310304446590b01ca40b901244140b0110f1143c29070750081d0550320b4500e207503000605250804038103030700c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 780307077 1250 780305827 780305837
    0x180b011e0503210a17150102120304020315151801180b0108010b13121101110703030f0c1506230301090b01120503070b0109020a080703140106080a1401080d 69
    0x107580c8091659440c50103040154840452910501481c40100204609211460580c2820f207030750040703100e03855040d541d00400d10103030550510f8558050240c41d0b18108072031046411483d050300401e0301c81d03c42d031b510500590481c800003190001d0b009030500151001609850841046e4122045003034028090103000e0685425078000101c007034011440500c406a40300d868036460f115806200b600080000390050510344404591980c41a140007095405000011082c160b4031001410388401280c8042180e00309c49401d00c08030382c01007003039a04c0000501e0301c005051350b03d040c0583c00c10b030341c0c2d500301d0403550a004000901c0d03091039408184c61211003254100803c0003108050813501a80002030006042000411241e0349141d85074000a00500030303a440d180e40c9a440c4080c4000036080213030001d81c082a100c030041e61050165a0207103043c00c0410001c4d0244001e000940414880c0341c0401000c84005030400703501e40c000c4400021401150121075864817003403503c401c0803081c8039000074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 780308327 1250 780307077 780307079
    0x80403080906061e0102190c152a030e040c0309050d11060a0b030a14100b040e150601050d0e071e0509040f17030103030c021305060112180b011e 64
    0x10000c0b0b151405201c00600c1507044082400f041030304024401a52415030007020350b60502034814101440a0601c52642c911072181807064501c1d0b4a03039100480710804c1280300100300c2040c030082c02c9004246c942c02101c2311813549484e00700c42403141c240d01e980e04075041c045000749513070b015009005201d104400341c458000050008032445c1e2a14074078440541d0014021034200219503100d43c10b44d40000e41614418011925540d130004025110030005600085000864148078881c5d040c2c402c40446041c4916421400600d513101a0f240c000202c465040c80440c180b40e02031011201d03102401c042c18841d0306580411551251014412000c90514042d81c00c803000c440c11109c0f00542d1402051849030380c40c2d60b04e030741644480b071020032200c6e502700811141c282e59031240514000c500ca903480a4144a443c418804120140c0c01101c04e05400c000901c140760ba00300d50390603041c582046002800313060000450b001d0740c128a0300905400e0840c000800d01101980d0841c031010364681100c10f6203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 780309577 1250 780308327 780308341
    0x709050618091308030f10080106050901050f0f040e0109051c0f11101a040e06010303080114030c06030a050907080d0c0602031512010c020d0c0c0b1b0a0308040308 72
    0xa105240303459050700e28007805030600b072030a0000702d604030203281c04103401d4014a03618401194030503151501c1c0c02024104000070b0b548052190405030110800074003085d0711341000700ba107201040c01082d104803001d8190f04541c0d11a441d801c88554001441401b5011813940c07068000e11030342d403082e1054010180c4641d00b1445c0e02441c2801a4908ea466010f00b140c1c00c20125103040072084000701600034080300c0350a017589405124000491101030014451a0380200320840381300c03101c5102e450300b02c03100420109801045140c1144d0744951203515480441c0c000a0038500c0240640d50700a00c048140000300c540d90b4031141c403644580d0201c60901c0d031104070556a602164412000280090140703400240075a0003640d000407598807544180c0071090001040003410f04004039403a07548141c0003002690401401c5070081071410402040c200b0b42c0c681c1c005420840c00380700746042c4005586045001024088010780e804002510012009843c0c0102030a00c241d40030f8002513101c401003000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 780310827 1250 780309577 780309589
    0x303030b0f06032401050f2a01091a090304080a0b040605060a14150c061f09060e0a0b01020a1b05150f03270f0f0f010c120e01020918070905 62
    0x1030707130b070501807882030681d400c0700702a90b030b00f01d40350641000301c1800b240c1d40324940180500a680302c004903140c06036580e82c0880044242e07040ca40e0f203da80c1010041008140280e101541080401c0d82c204416900d1030b007000d00d188581d90248945104522043e0284400340c1c014500852041405100c1910b81100704016030380103000c1c0e603010340c440c4640d132030662a01205005c0941802c0314414200301501c2c80083c185002158030000c414059602140b003609100f58a8000e00201181005400d041090140c0d1a410050950072034a80d2541c440ca05c070380c003c01c14070601d0380d07004a615170f03182d402c1c0d2072520003042c452140303030701501e000f50509030008a80016200e40c0340302800600d00307541c1d9011081602250304880c4020000600d20340100c0da1074140420074013600b0940c001c01c100b401e001242c03440c2090030710003102c203641751002401c45264803800b00c0741b100484000124042c902c400101d40244101c000095018200c0102d9040c0386940514240c81a607140d20740211b9540d5078814040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 780312077 1250 780310827 780310831
    0x40f08010b150717071406060616020f0a0305010e100b0d1104090c05030f1e07050d020d0302031606061508040c1512050705040e010b131406130303030b0f0603 70
    0x684140706501400d4040c8200024080b0030380101080c60b03241602e4048502d0940c41204290f0362411b0410650b0805001004200d8018800380d941da450b000c00540d440403030f0b00c0c501c48004d100e900c0407285140c003a96005401d1010f15007120003008842c070140c40050361040c0c07403901c8000341424103d48100600c0c2924608960a800400311412021407004020040c2074585d170440380c2214141021030a0b03201001020b0340d200904000f40348a9100418002d2400255070b841c121550210302c0903c25030f02c2d800141000b880d07041c1c0d1003035595142460306a05500030340140461144c60004400c061104580201044404046002d248070006400444920341d08550207421401440c0c000c001d00c0017030750400030b074a18640c6001d0380313099003008090003035440658070000020004103080c0160070f01082518014140400450300c0c003034040c02c1007136504116118244203416005091601c9840d5002100c0d189030701e584404500d20303200d00d0f01070f0081c03200e4250240101c8691000501e1424944100d034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 780313327 1250 780312077 780312079
    0x201050f010504021c14010f090e0a031812030207030218090a080a020705061209010b0d0f08031008030d200403050a150908030103060f0b0d0f0210090b070305040f08010b 75
    0x240300e60700780414040a0340c032041c0011149400404003a21112491003a90801910f0180401455150111900318102c45822110429107030182e0305104290004004840986c941042c082014801e066811240404d502c0f1610380341c24021402e0030141d0205254040d24400c0392501c01e81418034001000c0c02600303c500f0f0106038407901641c1c0104440c44003501e0071041510445070314a440c1c03000300d9525044032201c40d16911460040c4000c0c02d03c01e01411200f941c06483c03100d0140c000380c60300004454080030181000301d00001080b02d60711262980300141410f2411a41e0b190071a1106900401140034075442c0000c0c007100d0b100b210001d0104903000c498004006010000c44e40d25020381840019114004070380d0f40e0700c0e0701d1001038000e00145000310b014010014058159441100036200c0204055229040110b2500300103038408021803500e54042e00c40c200c115581f00070544280990341c00c8086030440201e0b81008056001c80100261a18043e22015203591070010509840ca044001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 780314577 1250 780313327 780313351
    0x70b09030408150f0f0c040f080a0203010e0312071b0f0311060f01050d02043303030206090c0109090506040b130609240e130c090f051305030301170f071410020105 72
    0x12801c8030205c8010307941c00c80704110744a442d255603101c0c00525110a42d20003032480c0c00400c0c0c0303107080d440c007807041208002d1504091442e01800003c55410407800400b5030082c401581881c40c0d1100b010078042080d50340c031101580b6861001c1c240035060903a0010809103e201700030020310f01d4001c0c2004181240c0000e0030600f29080d25900700009402481141000710b0b0b6a151041c00301c1c00c0034545800b00380351101e03c491b400390550134020308010b402007070017050340d003ca60aa0f0175640c0c00030440007100c05680d07001a81e6111400094054126840fa0036400718408100c0440841740307038803003411205040c0c0100292000c80c1c105c0046000c0b44003c00c9003162040380304004105810b08811740c400803480341801a0f90643d0703604589000541c003c120302940c1c0300003404020b00c807407091a80100c51003c04c11b0700404159981d545d2480140290190807004100c1c00d80321030410072401140107401d0081d203111030f854103001c400b20b01110705128881d1401d0184003849078018400e550143c1c600a00c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 780315827 1250 780314577 780314581
    0xa0603020102062719030f0908030d090f050d0908101a0402400503010203090a0602220e07030b1503070e220e1002091c08070b09030408150f 62
    0x41c00c4103103c07140b01039040a02d000d08007130416a0103203c2e0143c0d401d02155003400c8814182001001c2d62a5100110144500c1910901141c500042038803088080c107000400c2c9148036140c84d84c624424880c3c020320b144500aa18040c0940005c0c8040c03c0e40c2d020b40490304102e041c0048041518910080d07100d220340384500485403810150010103004c466581107200d215414644100c102e405003140e03c40002040b666000d98040080b0204020a0308400139800c41c1003003043c030b07078407154061402803901d80d0029468482140510b1161400b008107000021610340e031310f1400608203400c4800070b000a01d012410301461501e400c6030750303000c0690300c9141e0035680c541109a031141d4080205691080814030b000d1400c1c19411185680410a1800412849241445145400703069224181d0803030042c420300c075050b15040d400120602040c0d0980c1d18001090400c00c0d00352281e00400351007045104100a20b4950000c002c200302d4101e10202c034807110351120041610101920546891805600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 780317077 1250 780315827 780315841
    0x1030c05180f0d05010504020108070305010b0a1125030506100308041a16120e0a18050619060216050f090610120f0c1205150105160b0a050f0a060302010206 69
    0x125001d041e0000e012400520b0b1440c000408422240340c0848090f03450304200411564007580c8140c0000450806100d45d505086464a050058601d18000c1084c034403150306050703008004400084c100c0c10703580468420481d071000320303000d150300041d40c442c401c11010079040d2a940550400310303600200504c1c1868203061080b0240d010201c800302030103000b4010602011840035120b680b151240d41540c030750504000c005440c0d03500107100a88500346200c02049490301d000c0c443c0c413040211000000d42a507409000071240034603080ca0210a001ca00c002066454000503010340302c040511494143c5a5030b0400c1120010034220401e801800e0180810924140745c0d940e0b040b0140d80303013400c801100700b16070712a08030343d00280407074100c03500c0c0c0d03610000c400c1d0030441d1003500c0d802c44034003070149250202401d110700d00e40b05a02d50410400090b80e01510b103142c1402c0724260f41c42131213008075050a0412002801066405401c0c144c04c0d6004900000c0b40c85c40f54504495040c1c020b0401030f55680 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 780318327 1250 780317077 780317107
    0x120030105010c030c12260c0d15080f0109051002090a05130921030b06180d0813060207050a12030f08280917030411090a24031101030c05 61
    0xe00318103100901030031400090841c0764074034031051035648147d0003c82000c202e41030528500e101c0038502682c1c1c4103002021100c0303c1140c412a281d130034007060340d0100c07440c424012285d5500c01000c42c0111840e21094501c190400e255041c020f000b1a102c442101c981c90303049114810100c2c2d440030340724604014600302074424049510f010800003074075107000d8a401d140e00d1309c265000c3c60300c401c3d0b030180040e03480c1d00b43c0304003003000c141910418103000080c01c03c0132000d104004418461080480c80ca070802c09403a0880c0c0e4010301c4c030b040b0b030803a0994841001c0e545011b81e00480d40b0403170818601040003110740c00c0c3c109075107400d80c0d120010400d12070011341c1e4212024000c001c18010115a096800c109e2100a010200b0851000100b5910701c0c1082880011144010b11002c41c0c01c00a1001007001c5000c5609002c07802c0701e00c500c803615103099080091110103006920610281c0d9502c0c055443d0b81906411030340900c0a10200900d00c4004500322010f180600e00401d1045c018149044a05 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 780319577 1250 780318327 780318347
    0x301180b030a11040501060912060f29010f0c02060307081503011104050301060b09030d120b0a081608010c0f05210c04062607030504020409060518012003010501 71
    0x5000018004454004241028050b507419100c1181c107030600328050a2600c1079500628607450444c0510303041484d450541d60170302501030000354860400700314104031940482a940d15114a90816030519012a883d051101c80e6403404100304800300100180200d06490501d58000d11307981c5103036602403040e00e8141000e070000400342c44c40900700510f514240f0400f0140255a00300c1602d65242c2020507080d106290000454000d0901103010340362000600d049001c401b5082003040c010240310040000c0c110030001d40d0b807100c140000019500c00100d07540d90348401314078143c0052501c07000d045090f00d9440c5014000107840d0310312245044e1203800600403d01d4078200510708212001484d411205081e1410681441d00050800406801001c5071541803a0744203194800009464610041d2034018101014180c0f20360024085540d1030340004002507203c3c00c1004036040c96840580c54018808820f440c642c60108040d9114403000307084070381507083d00300355480e40c1c1c02c0c900111142148 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 780320827 1250 780319577 780319619
    0x30803060105030a0905030408010f270314210603010c1121041206020406090f08151e040809010f022a01020f0105070206220507050402031e011e17030301 68
    0xb5170300c02d20001880520040000b4911070002041b100a0400f2a1b422035891107408804000d41400b0b882506409070010405580c25007030100842904580003400b40c4103000c0d44484c004248400307a0bda006055019038060401074000304007c01010303500359041ea525080c062030030360201c000440b5100c100d81c400c8410300c0d4031018480c10a5134425128140c0e02c614001290210740201c1c06122a65200081c14000c2104040f03800116141001d00e5856111039001c03a01c1c8440b0002c001090f6030540900320001101c124800805442c01381440a4a50005104140060314082d49044814070024040395000a07130300083d40d1180e00803014131191600c2881071415030007090041f91482100703205442c400c0f2420b8000d00300f0751500b104030b0901e03031900c54410900d240380000301001280000400d5415a00e040d1f800603501e4586104245104004014401401100030004209030b80c91602c0a60003071140b40d60071804a403079a06240d41e9404d0010790b007050364018001080900c1e0552402068100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 780322077 1250 780320827 780320831
    0x51b240610120c050405030303090307020f0108010f06080606190f0e180a050901090206070c0f0e0412080a0b0d2f0315070504090e0312010e06100e15031305100204030803060105030a 80
    0x59241b0200341141c20403070761040c060704081505c900398100142035034889202403814480540c14516003c0325070045019a030204810b180024146845200c2154611080f40030511a580c0c1035040c01002a20403020343c0c000141e80e072413102c1260500c0590b408189498540101e000d075180b9a990005220003000c0c0b00003036480d1010900542c64010041c81c80f0307406001c00c01d400a09000b07031b9207034116280e8801700c0a2031020003004041160380d0070200e14910a0710b004074484e10740500c1080540055071415a101c0e031680004010018404448440050f44420b045101007100080e0502110780451668041d00f01c00b07441e44424088501446d4040018180039040c1912401003000305c2d411140d880c48207610008104c0600440d502c40107005100907602c0e071280c0d2820b0008242e0784c10301511040107000c0c00700e9148050340d07503507856103854800e5001450346a250100071840c0c2d203000c4140c2501e141c055401c5028510800740202c406494011048a1a41d1254001101e144c2d200070400c0554a07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 780323327 1250 780322077 780322079
    0x10504060e040b060f21010602060f04031b0b010b22060c080d1b03020a45030515010302120a031b02060d051513060f06051b240610120c0504 62
    0x4100300040c0864200c9490786d0b10400340007100801e1140c1d410f07000613040d980b2100030041c10f801c00c03c80560b40903901d4136008211251304041141c007250b00590042c08a10483c002180e102422000391020f2190030708896081c00704800c4200e410b1540c0e00882000900e00c82000c0f0205040c0e1004110100e6808d0000440c2c0d409881020740300c031201000c060001e500003d02e01c1c2c6165105001c0b203e04444e07100c403a0f01038018050700002c003042070000020140314403990a0b22501004012400660300f01040d07640052401089614008090208900c102d000503021400c0307610014400c0161641500e0361402032150410745808040400405c81c5d0100c0204009130310302681c0c0c010f66001c0d4030840f010381601e0504030100100342055003102c91009252281c104110601e510510007160071a0a00d15910354007441d11002c0d1081e01c00701841d5901c9401a841005d40311070114156030360b901d0001211507112941003005903101c104081c000078441300449440c00b9401ea10003101e420403400c20602c0c0c6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 780324577 1250 780323327 780323347
    0x101e030c051909031a0f0402090702010b040612050d090305070608040c1806050f04020906030a0207061d1f02160312150b090906030c011215120b1005010504060e040b06 74
    0x51100c42d0407080024002e42c03420001c00c400300d204504850241c1803d2207092501e030035400310580d402040a0310480710403012540e003500030b60011084107000740082c410292110300150140a481300d0840703151042e11800c40c80b503445105030005a80d40440900b900b185010310480300d01101904c25120042800400602c04141c281480300c80c141c0d00038040342032860030040046070404604542c0c041e9004010b03d40d01d541d114000c50f0b0780403588007801600ca2100381419001000c501c003424210305031031083c0481103000060807100c1080c00c1e240c050403100b020600141a80543c02c8e110030310b050304101c5000040d0090000350341410080400003055041e0900e546401c0681d03601401e40c1a60000751061582014200f807a0301c08020707002404041071100009140c011101c00c2b0600440c0d0305d008100318501e6209032680203010200c07501075000003604040000201c25100640b0b1403202c503c000032194002d0060b14103c84194561814558110007070001a102d02c1100700c1d44450200012214 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 780325827 1250 780324577 780324607
    0x50f011202030313150f0e032d0d21140408160c12110301110307121104090c08090a031e03020d1d0709060f03020f03010b030604060209101e030c05 65
    0xa2685c103a05525130031416030040d2a0750004c150f5503080042c0040002c1c01501e001440901c0000c0c4421000c01d81c8510425180070180e0100d251b191900540d20208004c65002e85030450b0701c019129401000c403c0c214040b030484903030304d1200407102c1035500010301141602c40034100304150010032440e0495981c1d50a202d52480d07411518002401c5003000c0244945000c00c1080080150000c10403800442d00c0421070b0b020080040041012003400b0905007000c64100c500380f00075002284e501d0303d4540916001800921003264001a0752400040c0f44e00300000e45998001d07050703119809001c13061688038074181c101e107803400c05154080182655108441c030034a500d101d64040c00043ca8005010282c0c20010181d102c030401a040c08404d1203100f1014041c1c03011030b94100c421443c818030720404680540095941c00c0d40c5400b0754420002407021980040c0349500e42243c0ca00e00783d40c078103001610000002d6403004403826040c4540c0b91000d0203644031400302a01030138058140040b510407804 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 780327077 1250 780325827 780325829
    0x10030b09040f080d15180501031509080c150703052212170408030f0702030a0203030c0904090204020714070b041404020309011d0d030b06040506160204110c0601030c09050f011202030313 82
    0x120031708071801c100000d51456412102d01020f0306010b011651441d15025018681e2070442543e880e52010f01c002000099811101360b00e200c5001e4446c3c003e00ca40c140399042c4011105400804e00307240001c0d40300200c0c203800c0a80c10207107610b109130201d0181c4070741c2e070484400704907401400500041c803407504030f000026500c030300e00c500007a1366603213002400d4040da400041c200006540c070a002c0004d00540110507640e211140380381c00c40c1c440380707a90001800782520003000794001c1d200182c081e040c4a405020109640420011113124560320031a61071144640e01c55100f103041201e0319094545429001181c106d0003080c0003046c2ea40034201c0743e40545c18950b030207150036400701c2001c4481329054025241d40c420100c4030706040c2464040460040d01c0b40c0ca1200d0024007960301820219a07640d0b001c00b868440e8160540d40301d0a81101450b61010203000640c1c03001c0c61100c000615221034082c2d14441c6540220101882c0d10b08070185c84528840c11040b070349030005200782050041541d1105c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 780328327 1250 780327077 780327101
    0x3110a0605010305010b0d030c030c02180903030601091509030f02030106080d05130509040f080c10050c040905130c031401021c052d07050903031c050610030b09040f080d 75
    0x580b545035103002421144030140319401281400500c0707022030f40100c000034810381c05007400c01d40ca444a20008400440011035240303407082030f83c00d11101550000245216040c287c8071403203065151804020312001e06030341e510000d624004240001850200b009200a2000e000416125100c0c00b42a041a114002c52000100c02280c05c03168002d99950b0107000349010780f0244a02c0c200754440491058400201400b10440012410b046590402101007044440c940800c001d04041c1c0d804059036009100340740700076042101041d580c15140040700100390b480808a0000361540c0c4d12546114400311403415155424043d0560348054072007020520f44904000103010b2400d200218203030701c0400b6903118000240d0b070a101c054a420340030544c1000e89810700f00d0b01c07101d02100285c5148103890400d83c10003900c3c410904007401a1b00400e004010840e07a02a2105000f5400ca0881e0816882c040c4d05c00b420720082000720718400383e50a025801500e071149068020088001030302c01c40742020b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 780329577 1250 780328327 780328331
    0x2003063912010312141206060c03070c26060f060d0305040b0a0801180e1b0f1201022802150406060b182103041a09131406100f0c03110a06 61
    0x2071841117510804109800c5000008181005441c2020000a11005060900406000030b8880110030b081054504081d406140342c044940c481528102203e81e0038281c0032404c03140382e0010880307280480c07401d00c110707440213001c1942d40e1020208800c91489010a40c141b0404000108820500100034016040c0f02c0d102c4039015403502101c6803e580c1040601441203241c8910850301c01804036085810b0301d0030803140c0b4503680101001580300880038003031030b622103020301d0401c100704070640142c070415444901c411b10b000071b000408120300c40d4041503800140c204c030124880b01c50740c1c02d0413190018066000007404036121120f610656000c40712141c1c04c0c002d958460ba1a924bc40440c143d40301440714003d0b0f2200c26004e0107141e44e40540d009030910404901e10b62501d2b283c0300300546149034002010000b003080a20300c003000030600d000e604100440840d00044039420000300f03085598105a0310640d03007091540e42100d800040e1202102004040310489450441c10010308900c00d00070840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 780330827 1250 780329577 780329603
    0x8060303272b051e0606150415020a020a0f061707020c040204031406070518211c02060606040518180727140601140720030639120103 59
    0x208602d0074001c11003804c41c1d45140715041150010125025400c400241c40884241c1c034030a040c51028052508a4007149007044c9142000c40c1c0d00180010703400c2d00a50f0221f12098031048407500c0302c0454090385001c1012050715014610030703495025840700b820700c16180c203800e24030000303003ea9210360f2082c1c40401101485070207000e0103112407504100903040c41d518144010329035000e5180392015107031085a00903448800f60a000818000080c02c400035a20800c030580340c0300d400026482d82c110014480c003400529242011070482e401c0d035131300601d2460101d500108804400070300a02c2c60101209450055500d450108910000741c14110301c6403501c0c039480e1040d510f603c04442d501c6071800e07042c0740d45006c4441040304001c0c1c2200081c42c1c010a071120a540c200d40500c9410f000134891907036035401e5020042600615031000c1000c40641d9060b071950b80d001c079600d0b00703030041c03400303c04000036030048060752a81110aa03035000d82e03441904250510012101406d000d030f005484080c0e130701072 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 780332077 1250 780330827 780330833
    0x9110405030d1d060c2401031a040b0f09010e1e1002130306022505060703060504330503120414120d0806060f0a0201060608060303272b 60
    0x41030b0b210b5030794149031840a8003102c09410a0401c609921140150780001300041e40b0501408407070001403100c2c00000b04000140305140c0220800d100950321110458081005006440f0030280184d030000c04014440e241d00301c0200e0303007290180c202e1050750f58916002c071850710140801032540252204407000b07030040c0b0510605140c0f20071030140c3d5031841080188a2000040609801e490b00a44010b80341d1182040c0e9440d1048007048103800300d800c1c0088002008400076000e84160b007640d6050000903034031030602c410b41d04140c1c80c00402190140029540c14400c041d2407103c00c40e8810808083c59036180460304162804e8140319100800140510880020402c1d14151a07419074242c40c940c2c030944e03806a110001003044404001c920710200d001651410b00f03031760558940c0c122081d0340341c0782800081c0c0240741034410b1780c001c51004c00c0045c0880c42c0c00300681d034102c1c404007a402100e1840440002c80d407181808115485902c03186c5088a004800829070240300b00301460516040b0941 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 780333327 1250 780332077 780332083
    0x4030f201b03070503010e0307121106010f03110f062d0f0d0c050a1e09090e01020304110f0a03020616061b02060924040c0503100c030e0615010f05040911040503 71
    0x50404c5020fa030404003013001103400002100d000c150405041404144010000c03580c0c0c6950f450000c8491088000201d5917042c5c011000c01101c2c8181c40c115402d00c00e0038144601a40310510090713005800b8132158995000c820021094200f24044032502d81d0228640c8014580002c1c0c0c200c05000030100e6406004800c500c51281b054480d810585d00f480e00001c0002c2c140040800840003000400040b00780c9240101000d4000d400510300a000440700b1000280c002d4200325000c2e580ca101980301046142010940b804545e07a018116142e801d0454080c81580d901c500d040300c503401c48070003040010864a1040e0b0051880481e05541b400c404420009d10b000c0000d480324603540c101c0c01490700c004405404442e801d200c40714182c1e0242e03a40c4d0628000003161540480c2d05030241c80c0403207045844c10b51028440016680f8104008007103064144d650380c40884071240c3d041c0c1c40c42e11068440d0300030a0380003481855450890700c6d00d5110b000c102d090b92060a24015503800208051203a40740034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 780334577 1250 780333327 780333329
    0x10031b09020a091a040521070b0301030803070f030b030c1c0b01080c0306010b0a0f0f020c04060609061409091f171f0b030604150e060f0403090b0304030f201b0307 72
    0x6801580c205414440000c052087c0e000101201c2061100c003c80380c681c09024003030003481000903840d100d6035207042c2051a0381c02214450b0014403062030723600c2454041d01c10321081440c090b00604000c03201d80b0905c0303200d40b8290240140c8907509941007001542d40005a4007a01c031202c0504900c00c27100091614140301030b00100c14035001800041001c580c04090710b076640c1c06030303c0c299810800c40c8400341c0c02c08000824843d085410401c2c042029500802200110703181c0e60384011000c66030301c02c108110700030075080c3e590002c0000003260a04d054003c000c0d031031207e12071001c901e4940e15591300302c41428105c4184c9807500041401c000c9603072410344100e40d401c038070107080c00000c802d900026103c0318000d2000b451100302003903900421310243d102065041c2c1510485032a402e003040f000400705400c580480009815020201d0690712038001d0342d018507032584890055160145c0c040e50700b40000304400204078110200d09240034410860b80c0008640504064040079000e014142800b850b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 780335827 1250 780334577 780334619
    0x303190605060a080a0504030521063d141b0c0108091504241a0a030c0b071e110414070207121e0c1d10031b09020a09 52
    0x400d00502c108503070881081580140281d20020380760b41d988c9010f0f0f80d18003c5072084240314100000b25000b00ba8203c19203809407a0498801d01e0b0490920760b100d0348251719150103051000300c4050901040c0c10000c10580740d80b640c3c1820031245100c5400e900494110342181036240c0b81548003248078500c01e000191440500386001f81c421700d0a0306078503549801c001d582c04a070b100d00400040071f122a002e01c0008640d403141a04003802d124080b0f02014103070040c140300e102c2d54058041e003e40d10f88003841c84100e0f644807402104642c41c04100c0c03811504000da003901c185a00c2e41d00c2154845d00100d034410010b102d111181c58440070b1000b444119000050342c10038101c600800c0c440140d8001034144122240e40c010104001210306d00091680404046003551010810703010080003804115001900c84640218140c1c6c2c0c3d060020116640381079501010b115031400c414000b01d03210b5000d001010100044101c001c55442010500301e07404180c1100c0040c5254400307025801c1c046109024041c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 780337077 1250 780335827 780335839
    0xf080105010510110c1c030905030a0b1614270103111801050f0d0c0f020304031e030507120306140d02030601060c02030a12021c021c120e0303190605 66
    0x2c101004543c940c1d50b40389a10090191111140131116070030099803100003400360048406112004034406d200003255800c4004c20b5511402045a083c0002e01c0703441107401c081d03001015150b114440c2100d50040010f102042090041070160796010002040c03016280b0f8580215260350004c400020343d0342c0c2003554101400c0c10b400c5450b41e032a00e4282c40441045219001031000e1003001a0740520401d08030b03180488003c21001284815640024040c00440e210a0000950094200c0e203e00c00c5000081600c105149001009040c900f00032080358481e051840c41c2c20003035122809181c032601103000c0045e03200c0d4014011080c1c45001e5035001c0c8029181021500392070750010b5107a10f014002c2a0030001401280b80965404000303e111464029900d8407090b00c00010080d165050800a00d00d00440b030070000043c0380c40080d009d401c00001c02903200390207880810480340741e5051600c482140c6d40b50030034003062050600065000d0381140480700503c11040040c00180e46195200a210390 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 780338327 1250 780337077 780337079
    0x10e030d0f0e040618050405010c0504030b0411010309050f0a0201020f0106030302030319140a02040f1403150702011b2c0916032705010506031f0b0f1203040f08010501 74
    0x50704010700400e01119400d01c41030242558000c50001c107010b030f00002ca001031a00340c2000d000310f291700c4680520301038802402a40b00e4504141c3e813500c901d100080444540034009804200c6451050a440380c0514000c0341010154607900d24084c2e031120950a00c4e000f130640d9070b085680402401d0260180000288100f618585020b5140d00000300044a144541260450000b0840e80201c4c0801030b194459481b600b4409583d00c002e411600400410034075402d00890000c981d0031440051841c000d00401c18038520907070180c0003040141494082d992504884426a1b201041c03007500c601c8903a0310b0001d00031280204038422428800118003000701c0420f80c143d90744458295075800180e107201800301700c0190000324024083d1800700141c0d500b0403282050001610742000c0100d0b0300500090013261580d84c00c060b00c4028444c0d0300045403c4c0780d000011a180e894100352401c5800030108041c11040314085551100041060b5800c0d03040010180315130100d5080c010040c2118100810243d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 780339577 1250 780338327 780338353
    0x305191109044505070312030e0a1e020f03030412110604030c030f0309181d0601051c050c03191a0708040206031503010c05192a0f051902010e03 64
    0x11107256140d909224000500002410f0341c3d1070361403002c082c2c0c4101281d02440d0f40781002c54940d00902c1c40c40002904111803c003941d040095a84000c80c0c000d0010340a1559582007030031005101c441c02c0b40c200d0100f020a10f200e60302400a0802050b51205010001c0c54501d050011246c1c0024200e106aa0a1105201240310302200a083d643d01003505142e101241c1002d42c0c070410594450040c11010850780c0d58400b01642086104e030400c0c03d00c0c400c2c0c40110502d0245c03590f01c24095143c0140041011001038920200c40c02c1046010301c00380d500300d0140c8400b00c4d08000f00001046500b0085400e00e10802c418186010392100c0301c660050710300d08281000411140c406000640b00d07900101c04255222440c0d000c1d403403c444010000c0025510b0442d001d0700c181c002c0f070224030310a91000e4682107040d004400c0c3c0c0b0b11601501c45184000d5000c0382200c054100411000d40320b80c4042003c40d4006a010040c0c1005411400309426010400d84001002084040340c454040c3d003000009000c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 780340827 1250 780339577 780339641
    0x20309070b03060d0606090b0a0b0705280605040b1803030702030304060207020a08060906040c0b0414041d1905012d05060103110a0804050d0507080703030519110904 73
    0xc0c1c0c0c140115890b80c0b81c0307400c00010441d071100400078203120310b030040014041d00d855000c520244000e88035441855944d84084245000741c2c0005411500000c140c2c1d442081441c2080c40403004d0320502e80c00c82c20b11500c0340022201c3c1103c0031290f10000e1421b00c9040140b9800f00d0325651903800c01185985084403009449000280004040b01d8001c12004115510a0300e00c80250540c041290308500d030002d1602c5e5034031300039102550701c845543c8004c503500760300074100ea041c0e403401305420311003607900804e0200400500800d010310304161580d200d160082800700c1c030010030001001c072445035414109142160320050300d8162611002c443e550020f490040c2c00100c1c0c41038564001a117a90310ba00503006412000c03031882c48108002480100290004480f42c000c0b07002d807003118108081d400096540d4400c941000c2c0440d0300601809001030f00c00d800c110352005510081e1088010b003206104d083d603400000f0005522030120f03152516040c58410030b00b811404040d0407885c7c040c4000c001c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 780342077 1250 780340827 780340829
    0x71a040603020a05070b0405030a0e0102010b01090302010806030703060615121503060f0e12070b0f0114090703020c07230103051b0906041e050102070e06210c0a06051c02030907 78
    0x18141c01040c40b4000c503004d141540c3d691a001066846146001d190045e02d903031144e40176002064061010391001e520510462040150603100c889003182942c0066038081d1000702806d81c1803049040c0400003900d40e000381c0c0c00400070349032107949036a22280040c10156440302e259070881d1070505903a003184201340300b4200f200d80206000440f8141014014060102e03100506000d2050404640035404d40307000400000707002d0712424000e85c035020103c2426140c28451a0740c681c01d446620130340d614180701380b10f42080d40b50800600c2c01e20020461414080140d000d0702c0c1ca401d40c260f1580c5c608014400d8102d03550310902e0200001c3c680b0950260f501030038480b03145045080480c086490f42c581c00103d03005003d00b0004500092440e1410410b81d603080c0c041d2500502a82c00b000420b1a00d1f0b800781802103074010001d20080c42c43d010380d514900700125a248544c802c200c05894541c0750304060074080e00d481ea41e000c1c1d40301503074100b420350070040c3c000f9401c0d03452040040003a400408282d501c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 780343327 1250 780342077 780342089
    0x10c200d0c03030b150a11120a0305070207030b100303121e0e030c030310172109040b060c0715020c1c0f08030a0632010c0c090c020609071a04 63
    0x500341c004500702180103200401c44941c2000000120851081e20000030f4003200041359207000804d02e03403004003501d41c019241000c840e1102844030f044001e000340c0040380c0c8807030580304545e600340e034948940a02103c151600c441e2105030352020b00a06900c0780300c6104522007481d05000044016072405280900c03030031b001220359650003801c3e42400082c0100c505010720801165181d00386401364554100300f03449807144c1250214a92140343c140421100002c041c1080c032180d104414003582c884a5104040041d0311a84c0d414007844c0c01e42e1024007404903249003c00505483e0309065044030440101e000d00c90540d403142241062503580da8102003034a103820100c00150002c0d500e8601c1c0d8044921000402000e008010420307a441580d0002086880b440034099240482525402440c070003d240540b0001c0495100501340d40500001c0f1a0103220345041d1403082e6444400c4801c88100c0600d035401a0040e105100d0700400c104103180c00350415110000004101c44074240052240c0d01c500307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 780344577 1250 780343327 780343337
    0x203040201171b040e160e0102060112081903021308060919111534080703020a08030a0b0f060a02031c06151220030105131d010c200d 59
    0x4421119000d01c841d440040040250f4944da01c0d05800111150708450500f44240c001810308003da01c1500742070030401044c1c000d040903900703000d0302c058110010201603034280410081c04030309200c10f20702d44031102581d40e03006888585000c01c28601c40740ca0303804081075901c04014003240410200e9a001c2020105161194280c01454100b1030700c0c43c19000c181d0300c00710310040e80801131168402011420b0b111020041b03198101890b108000600070f04210401c25030022210008803d4001080d8150081c0110350942d1300699940c3d0090b0b104481c1d601700030752614450030746805c00ca81444616401200d16904189030054000c0d0f40b402a080d001b46800c59036142004800140c0e400070010f014106104c98600004680140c00014035101e82c02e02c540c034185042c400b4a400c1d4180d600d50f0861500c2d59172869182c0001c000b401460140e50b1168039a0301c05036503a9002d50a401100c01c8144080007281401084001900c14054a02200a030b108901040b00e03038903001050031542c0d10414180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 780345827 1250 780344577 780344581
    0xc120f280e01060f05090106030606120b1305040606090f020903030a0315030c0b0a08060f0f06030a060b1810020a0506061e091005030d170103170705070e0a0c03020304020117 77
    0xa8014110400e0a000e0075481d281022640b11001c40c1c1c40c0c0c085e15010b65100c4802d9980e41d00850484846202d0f0070000760210001d04d451403041e4200c21002c8000a05250b50b003141c03800b81c0000c584054504840a0342d03a0b00041010113140c2c0a03414031200b0062085042000d100046034491082c0d00c2c0c06001c240d91140810251400003000c000550740089031071110325100d142e44000c642c01621007501299484000500c1ca2910b01c000418108000d884540800300b00418800c2d15000030b44100b510a84840300840c01d04020b0340940000c054206241c0d29102c500010710906a080c824444210b42024a803240841d84c0015001d41004040d80d000d0492442c24100559403110f40c0d0b030299200801d101071203002408000050f01b55041181039420040740c2c08002d541c140160600110800401d000401c0812035141d030725140403005091162914485139120350a043e00c3d84c01a0301241754800c00d00030724110900c03901500d5a8582000c5145080c01d0f00045c0840001d1100000501c0b00080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 780347077 1250 780345827 780345901
    0xa0c09110c03070f1505040519080d0c02032d2d0c0d080f0601020a1104020c07030b07030b240306130c020c0916140c030903060c120f 59
    0x8a52140e00e1a01c2920b495040c289055051610344550540f40c0303c20082100b40c1c0d11034188a100d000710b600900401042041c88544e141c407400c0000e0a884020b000d020000010b105070190b02c40d002220b034040c42e035035900c42c203000764603101881c0304120440420704504d070381c0344c1c0740b500700e4a103209046540354111a40810003044600c11007100c04000c0000b08040601d0301000800b4501c240c07a5444101140d900d40a51144840302120010b0040c0d11500d010808646100b40c0f000070b054000c0e0004d4581141112220f280c1603655104030380009542c403c0086040e030602c5010b1030b900c000c0f20707010703a542c0c01140f11049952107604140140348002001c00c0c00c4e41d54400b00c00040c503000440a01040365959006500d030564641181d005120030000144103140100000b60b28005070b48900e0111700b84c28107030400603080745503e001c0500c02000380b070840e070742d04000e11407080483c104004d0f90b800b0603038281003c220000c0d0405080c3c00501d020702015075903c641400308200e902031407a0101c0e900003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 780348327 1250 780347077 780347111
    0x1d01060c15111c0c110c131b020609070807120b150409080309151009150306090b19021806030624040e060d0309060c022b030f020a0c09 60
    0x1d90b881d501d204001803901c032003040806044000c5114504100480c3d007200c2c0b020f8500318580094000181c205c3c4d40b04510924000704054801500c0c018001400d0301c140600f8000c03900c40070b202c0d0015038020f004108002004202c280042c00840001e442c005150040200e422040c005000340941c0d012400110002d101c070780070b04c40001c0010004e02c6403500509201c402e40c1d0040ea0180186d0003410329841080d100c0c005420700542c4403000c01c0c103035145000601c400500701202c80022a8104110010100d2580d001e000201c6000f41600318181c2050010203001103850740f1200d00441c0107201c0e021448a030b020801d1445203003510101d56035503c500008134440b03148106140e004031410200b01c40904010041c0003581e55241c4511440d0300c401c01006200f03246094024001000410300703103d00f611541009203064400f401c5050002c0c103145000e44c0c1d00b501d619403c413001c0100e00c410000d1581c00b115404000c40d450020307003545141a00e40e012401031074001c884800d07843c0c503085c40369072100ca = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 780349577 1250 780348327 780348341
    0x605190203040f02040b040b280b1803070f0305210c0d0908010b0d0b04140a0b010303080702120a1409180c040f0806010f0501030507020114010f1d01060c15 69
    0x84003150303245802d20344010000c2e0101c2090340101d10302130200d400d5041521a4414084004010342c2c600c2240d001440081c0152030044204207956850010b0030030303403c00c0035001e1412000549110300e000711062614202c05980195035001c00c612041010810104440b01d0700107007000240041c2e00c00c5001c40c20280f244130805a01031103403100c18041d640d0f1084050701940c140000900961000c0c2c010044c2c42c111915004c1c2141400d880401c00043d14420019010400142a1021040315407504044000240d0040c0d004c00d801c2c02c2007200b050742c1407041e010101400c602e141d007010b240c1d00d001080c8403c01c0343d14070b486041c0090025156503c1c136980341e6103450190b061588501c1c0900405000b03400c5446050f800009a500100e0b5010000c15614140e0304582c051510051410004601501c405800041595a90305801400040d40301c2824041c2050000c11030899190220f4120340c0d2140103031010f8040c1040c80107200f142d500c00d1036100d00303542018409441804d0302440303200403c4c0c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 780350827 1250 780349577 780349621
    0x15030c1119060b09040819090b1c0c0804051009050a050a060b0a15050a0311070c0e1501180e04020111010c031b0e0a0603020d0608120c0d110a0605 65
    0x3a21906541c4040c0c401e102624284125814458681c500c0c081c04880348068800038100c0c4020b00400300b50661682103130510044515146200755078801489030342c2e500002000040355220700c00c0c2001a036440c09010b46201c114a81242145007a0300c8203a241d0b0f2070345003071425a81e1600d0780001441410020086060382020a03108486030354074160004244c500c1c070840c094100c900c1b0008294121b1929080040c0558030303a54549144240d01f200203160300d428480c1d00712000c0c010a808140b000c00c0c50f40242070039080c01001824115046c120a8645403c5035040152010751f40c40d0285040e4051000c5607405201d02007a505c4605c016039201242c131450b14820b600c1d0588900156515411514102251200c140c095060010044495070218140240c1005000d5002c00140d44a90b004000030403a4080014025440b1000b441c117101803841c085988020108010170506014009400150b149060500641d40c4150030b281d03c49140c1074000c0d180544c2e80c8000740400003440112141104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 780352077 1250 780350827 780350833
    0x10b0307050d050906041101170c0310081006050411160206070203190506190911090415020d020928090213031e0303050703020306030a1b08070308030a0e0715030c11 73
    0x41c00286031a55010211800d803407d85050864900b00e5000704103481c0030710140b1407003c0b103558032011303104c01c079500c0544a442198900382000402a009100b00c81c1c40004800001c2842071800c0100400c1c1c0e5104640c008291340f0802c8902c4510408001d80c00b807999044c3d503a1600c0300c000b80002810070082107400360800c0210300c0c040c0104440410203610a000d03080e0098000e803048201c110890b00b4080340140311211803c910481c52500f030380802d45c424030505880188540f8034956205036000350004d1060181c0104103135203039184c154a40b11074200c1a20b040c10307800c404034240a601148601c20303a600d0b2603000a00108031030b110b030745d40703030156030041e000d095415074008040a140310165000c0d00040e1a00c00410752507442802200d003d000014014841001c01d5110803000050300100400c60400300200005d00b40d1052220000440c080d4011a40382d1910038048401d503114861622400e030080201030020314200d141015441e07209103000110114024003d58482d4400f11041040e44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 780353327 1250 780352077 780352081
    0x4050114010e010e0f0618060f15300601080a090f030e130e07170a0c120203120304050706050c100914010c110a020909100501081b09040209010b0307050d05 69
    0x2510a10300b4101c0c2da03144134160007541c0703840c0c0d00300c2044010350b0342c1d5600000807603986080f4803018400c980c00c0100146000b800b242200c001a21130141140320b0042e80c07801103106c1004d610920700c1c0404000c10601100c280036040340f00907680020003030403e4140421040803c1e90489a5070010900c00d5200c80710100032406400c000d0721040c440d402481c828040c140948002084500441241c1c11038840204107007401c003c0000c840a821046d031620502c55041c9003c0840d00d017a00c103000405c3d0140154171803420034010706040a06503c02c5001130030080092000081c0d00194802c101c50750703860300b603071140001d0020609108182c000f400840703003000340881c2441307a06556030303c01c001008020002000d602a058400d00e1042502d804160403002010f0302504141690a60010980003900c0c40c0e60310141800d01150002e030000d080e268041080c2c4124241140c003d0521410704440070881803602d9400203180000501512864000204c003145107036000e00191558880056020f00040c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 780354577 1250 780353327 780353339
    0xc0f0c010213180902031c030b0a0e0f0c0406020d030b040603052a0409020906060f091c020a06050f03040f170703030b03070504141302270a05070201061203080405011401 75
    0x8012500440314140f4003039061190768589841069102035018000d030170031001e43c8449140d00c0c402a4104800d05446050414160f514038180f240070b444180b0844285091a03540c0c45801e034001801c41ca1607000400041c03141036000154407070081d9603447c001c2052811000441c018000503440200248a0701030384040308007425010760b032852414800002c0440810003048261444010003a400c408400c010504501b041c600500501e076071080460f11300400440072600c0401c0d010005403030701c0301e030b0200d0310214908082800001c102034034040d030402c15812101c0783c030b80c400584010712820745101400100078003440041000130b40c03112407540b910707420300f0040d0140400696451180c01540d00100d100d16141c0b003805288844102c0064150365485108080650360f50b5090b42d0150300c1d44d00d809004000a01180130040c0e910001410b42d08040040340300346e4002030f1201095904049092203000c40b0390480700810354240c038010700c0c9900c0d181451401403080d40081400707422400c0010034a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 780355827 1250 780354577 780354607
    0x130c0302120a0c0c030c08040305151e070816030f0204060207050310051005062d0711030604021f0e10020703031106040201091701180506060a06050f030c0f0c0102 72
    0x1c1540030991544a0391442e660a04807a05249110f0200d070014200d403010034440c10100c46114810407d9600d856142d07191246400c00303002003100802683c0e0700300204603600f60f0406d1190140e1a92409460500c1c0c60041d040d4580181700c070003074103030218500c680513100360000181c0c4560618115511512080002c0d160f4000e4080c0c680244070b4805800c508240c10300c01d542c0300e4200ea03c03508009500741401c2005a034021816420107602c8003c400000090301e900000480c0c0d07011240c01da0b41d503d54903010f61000781d00080035100b074012000700405a16801151340c8100e4462040c0508456a09002d40d50848181e01c1c558100d500c1091480d4015000907448065034001e40380c140389d103040c0400c0300755101c2084800a00085038035a0400090341c003100c032281d03100c11410002c80c40d158075490100c0101140d04041e29280e0001c0c082c8034640c2090380c500343c042c102c1032030451715002d210002281c8034400a8020a14100005a42116460001c0c1620004101d040096650b0b0305041b02c0300704 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 780357077 1250 780355827 780355837
    0x609010f030b3007080c010e0a0b04090203010306050f07020a02013e070b16120c050d120e0d081501020708120a031b120f0209060714010b0402090a03060506130c0302 73
    0x156001000a410300401d0f40001c2c451300311103001c0021b00c661000d0703800454034861031461443e0001341140c401700c0c0684005000e0000390800a600607104d6145042000c15502c001d4138881000c0c0e00d078420f005000e5800304020f21511f030203091190072100f110354030002d804101198145c0381007800780c2c0030b8180501c0c2100c82200594000483e5181c0e5240c2038099040c0c89600c5840e110301c0048074070800000d0390b01e0107004961540d0f0402c2c50b01c18a02d601c9880c00c01803500c14407000038180180750722540d99107124500440080d0303001014412154540540100341c0074004421803048000300604981c070070000030015025080c1a00c3c40480d825800c21a1500004c50307200209041440300c80c01000007601882e4181c04540e18840003140c00350029000b00f40001031300c85416000c10001c2e586860b5000180f191030b02c102c4451001c82030a513040c178216040403025034482c0340104004501c0360740e4030b0189400c0d031b07811480024158543e000022003101c0140300d8484090708107520143c0c41a0107034043c0c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 780358327 1250 780357077 780357139
    0x60906080c19380a1e02101e0c030218041104053a030e01030905010e0d0e03010f09020f12030702032d071a0f041e0317090609010f030b 60
    0x54202d981d1202088018003400450744005034917408080003500446640c5000f246060044e01c096041c80b250b61015140300740d4400290300c08400c404d46615103248261702074000340d413408600b4884002c200c0030003144400805072141d81c4a40740010100d404108507401071000412041c51051180c0780f84e689000401c1e01c49828103141d00908140c0110f032046015008c3d49a03850100311455040190028200c1c0101070781c1c15961018070900910342000381001410407500c82000f588080000c1501303444001003061050f50500d003000005031210340200301d00c200102e170589149400341d24854550b00031071a000e941803007000b00358291310f1440810b84191641180007000c401900c0144107964036a9882076085011040740040c819a4660b0090b201e40909a440945400e42d185005411003001c0c646076610710007292410410410220100001400c00100090429425000040480c01444c5034141800035945035820344c0c43c0329520841030b101004000800300c400c0c0448003d18000f54402c25 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 780359577 1250 780358327 780358409
    0xe210a031d060714030d0c0206060a0602010b030c01030e031224120a110a0e0a0c11340509040f1707050a020d0c18050a060906080c19 59
    0x205070003035800500c0381000c40a4101450000319a6502d00d0807114032210080c0da000a200381d004800c60360180c104000d0940d80108628202032041049246c3e407903024100350380c03415100c25019140410b40321184402420f0010308601c1e060201070540c40b81501003000c2140800801c000041c004120088a030351076003403403c109610000740800c404040076201e286038005000b8100243d0030402c04443d105001d80640101ca0b9106207500f0040002d8030f42400b038584640480b14102d5209072034960744103518004100401101c1040c40990150007150388480c0c0d04480010750241050a03074000405014011860515260805e0f0005810500044030403d104402c03442d07922000b17500381d40c0d03d00e03042006400d001d5941d9080020b5084480ca080b282407164a20025060040b031006511407400c00c2004241303480c03d805040111947c0d0b420000a662810505221200c40041c031303d10342040c2a100c900400c0061072a848220010780d0025400714000420002d0fa415910000900c5004407402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 780360827 1250 780359577 780359597
    0x1407020a0507121a04050c0409030e0f040b01050703050a1803061a011d060c010e010e0d080105030d0909150f060309030e040e19030c0614040b0601090b0306010e210a03 74
    0x2054000d640c0d08201900c3d003507013803080c0440c1c03c2d444940b81c1e0300301d071050044440c000d9500000c00e0640d030413000291701040002601090a08101070302c4c284c0304501701d0b4200941e0244000180980c060b620010381004004181e046e800c0707024480055813115503551a17903074a90f4918050000d0000c010074510041c0c001c14140040754001c1d500d0101c0d10164066050703c1a200005001150304807654560041d0749a0043e1403010304288144203020300c4200180480d0582240043d01040341a44618001c0d0701601100100c90b034022164015100b483c81c02144105074042030718107400307031034008035001d401b2800b0000c1c94a402da1b10030000644207896030800c0780300d200b0403c4203d400040c80c15100b42c00c09101410702804001d07c52804c203120f81001100304500f0b8441c041107890401c0b804500c40d80381810b100a1101d024a2241d010b542480c00074443d0742414002d424500019056505000742560380b114641e80f04045400e14420b0030916a420588058a081e0b5401d5803050903004107802a070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 780362077 1250 780360827 780360839
    0x6240206010b0a0f0302070b01030807051203130b04260d06090216030c02060d021324020a14120c21070b0606130509090d180501020618011407020a0507 67
    0x1156412034070b003071441c03c2c1004031104040e18083d01010b620000c140c6d0812840c07001500040100e8041d60150a081c0c0e256140c6282013850845064680000b4403000d104200a8a10b115590082281e121a01e90030513111480e0051003401c8400b074600d051040740f403c2c0105040d03c4006001302c00c2c80c041090124640e250f00d0781080b4400c1c603140c0809441c034007421902103401070400c40552031011b0501490044112021002c030b0304108032003414000d0104042100703a040307040481000d600d481400000283d2480040e60707411240d44002c002566020040340d4455051000700030715507880d038005544074042071820b620780d44c80c0c00c400502400c405840403000424103094070a6643c1c8072642d601e0581724007080200c01d401228205140c04c50200000c1400d0f02c0b80e00400d4050390801000b06038494000101030301030000080301b0002000782c0d400c06c0089aa0010722641c0006441e440b5078904001c0b001a00d024003040c8502c10f06015078981403214140e400220131048078011001d40c0c0003c3c3d241c01d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 780363327 1250 780362077 780362083
    0x711030a06330512031606020703080a0605011d0a170c1e010903060e100f0b090f0907090513080a080f130c0b160c09150f05090f0a0b0301062402 64
    0x2a036108078441c07882000d00030303401c0c6003805101c00c2001e04e04503810701c200c06d061403411112800046942a80209a0108050304800d902d500250141d40034800f060810340000e141c54921200031501c9648091021740640314003040340c0140040c049158030486000b805240e440c0c4a41c4c84141c064101c0441d00194404141c000510b01c1405a4556410700c0c41c50300d4035409411400c440d415030307020f16003544070803209921440340035a841d40c0d800b0070b981c030342318041015508c030040c102c40c011012602004034911000c00c01d08169221200c0005864640c40240c0011802254004020190004503000526000501e40e03202c0c01d040c02e80c641c2e0955412031903540000351002c0003030414002042c203206040764980035060300043d00f4000000040c90f51601031840c1d42d1503002c0000142d40700c2078651201100c0c481800a00301003607034840b40614220102d90060030040801e80ea1080301c10114030012015000381f242204020000c1c040d8a450320048030402c112500350054070f000720411031011358008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 780364577 1250 780363327 780363401
    0x906140609150309070e010e190506010e04240b1201080309011d030c09010f090b010e2b05010203090606011e0806210319020f030708040b0711030a06 66
    0x9440070303000c0042e05600005075007000d8068581402581c00109142803242200350082089169107816420081e40b011004150030001c40110760810040110fa0398001940d819120400d44001075074414510009849015641803207000b818008400584800000c000c0d140340182005001c4880c2d130f0380c10b019503403403007407003023041c00b1801050401c1d8101581c8805150015405019513040030341410024602481c26000501c0c0703942100000c0c0082c200522071000c3d004000e082003080c61105000103032082881c800c0180e15101d042f4021002200c0e0301c050704c0078081d0300200030b40d00c90822118541e150300044030118009481940e40c07903800d003502408408098210b882d00c4059807a017006008049210705c105200d00a1030f090450585402080140500540980714920000403075000904007045600d06950a81c0140201e1011519040898003207601c01507001e6a0341d10b0a280400c075005001c80401c0d410b00440410310300788042500441c8d0307854041c140c3c441034840f003008620500b401ea = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 780365827 1250 780364577 780364579
    0x50105210c09030a030306150e01021f0b03070f0524120a020c07120b070801030b150409080301120b16020d03090804031205070501050f150105180402040906140609 72
    0x1620040e140d003104000540d908038082400451502004901003482d040000ca01100003994070141088a45001d0003201d02010491074040e00e00450b040000391b981c1e00d1407414940380c0e0b4504000c0002c40003251302003010100c002c1d0640356495030b07840090704605050701c134941c044d031080f502c400882980c0c00f010512550030350025a081c01e50b03c0e0f00504480340d0080c18007040301e5081101848184041150320001c0043c1c0342e8080390040585000740c0c49080c060100c000b80030210006000003020000d44a500c030358005854190030350320000081c00703070503081e80280c4442000000490215240020420aa40260350780e44d0161900c140055200c510000c0960050700580350340381d010340c82a0400e0f0000d5011b06c00c100c1c2400e80f40d0311001800c00c5804001340205000148000c2000801e0151550001b02031451000301c2ca0204100540707100030000690421000040981088982411030402c03440c01402c1191100e07201d1801d10f0050041d40540c2d08400300350f40025446160000c1101e926541c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 780367077 1250 780365827 780365857
    0x80103060c0f1403090705041505010e04021218070f06090501320901030e1002090306091b12011d03030901150302030d0305060d0f0305030f01090c0819060e04060c020601050105 78
    0x3070544071002e00313508003400d0300056010b100c1c1c0001c3c003a9110f0140d2a0b0342c2c02c0002440e03031001c1c5000005080c2c000e0300180c0a010314010b10465489103120803203180c0c8041c8804c2c0c001405050f0969441c2042901e4004402c0c50788043d00214038543d11a5511054400030388880d1f40750803041e03a03140056050542d0440c2c0e2040b40f00340c2e14282c030050001501207800103040100e00c0304501113949040c50300e4188641461a40405d02401c0d41c41c04110139a00200358074050008007107101c40380c003486458142081c0c080c024110060840c0c4009600401ca80c21529262030b5542d0405540540c40e039000740c480101a60078542c041507449865141c100440c0d5006006000001034a44103a01904004116941c40b5103400400808240100520300002c0d00c265202580d0b403818504000c1304070010b80208914607d003115041042d90405580380e000001d00080017030b00031a10f5910001f5001c0c0340c002d20007000403c428802006026001154217856036001d46255070b8a81d030044603103016144100310640 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 780368327 1250 780367077 780367097
    0x918060e0c0d15150305010e28060c2105070e0102030c031903060e07030b090c0a121d0109030e031b0a151b080d060905160806120706080103060c0f 65
    0xc0c001441e41ca000348076088081500260500c1d004602000c1d1780c010313038060b51500b101101ca00024052000745034540c40300940041462204441355010110f4000c0c882540e80d110340307560b01d0040c20102c01e00f040c032002d0068005108103149025060540f5044c01140725290020000d60020080c0c40300364403113000035401d100c400d265860782c0c00c05068010044c581d580c8400b0416492100b02c041c071400c2141c80200d41040d000040c0b1800c07241c02803103044a0002448103883c440c0e03001d8262034840840402c00314120000b0b144100251202c065004145e62138110007000301038002c0c240d818203030822015170300c8c07442542c0d17040c0780c12660060340981e0080601806029502c1c003408183c1c861750240c40e00782480e00d4010403008070486130007800d0300c003c1380125010514100b20700501001e04a1290240058108030201844140703500040000b40901034000505d15200c001c0c000994440303401c12582600c1d910340d4003415019080c001614a10f0410100801c4140120700da241c0364170403540c03029044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 780369577 1250 780368327 780368333
    0x12020f090108041509050607080912070204020711030f0a0611030108070e040c090614030d020c10030e0a21111507050c150a15050927070918060e0c0d 66
    0x5036200400451308000b10b04402e0040721507510604096600c40e4000f04498201454041c01014005080c0b0341254800744025000e01116802c0d145460303410f503405a15201203103000c0300d08002a940340750701882801c1c1140d00e4201d00080c58401c241c021081000080f602e07808a14140c071090042030419445000c00f0080d11101c002d46d540d1050144c803519403659202c0d00c6030010790f02c03140e018014041d0054081400c3c0d260a21075000380c0305d0680000c00c1082c00180c049840d031514500306206069890000303041c40348086c42241d2403141d1004005212100b504688a9204000a2190300007590b4009161030007000082c0c042e050001c403101e591580d5545541110240c0c0700112010050045861340c1c13080d80100c03488680184103d000203d0300d01c02016180071080b0300b41e8070440c0b159080000307012006a199981000340320742039030540d22034180c16691718984100c65100700c2e0041d01c1c0c515280e5004560f418210b00301031083d0000d02018900d040c035941e03680c02d40148950301c621042000400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 780370827 1250 780369577 780369587
    0x50c0702010e060f070b0f010801023405010615081b07080331140102040605041716120b010e0c03180c06040603020c0c01090308070f060204030215090112020f0901 72
    0x102d0b01c0018405850300c4010100c0c8040d03500310480441e20052400184016a8803a440440c09401c040c0004c6041084c10001e1030080b00c101d0a1881a41041e00e1002142c03100204000074416081802806010b942d001702811040e081209100040c00c98000b18003100000040e5000303400c111001c041c100030054a07600200d51018100030700c1c10410340703409001d00460b64005005040045880c460400d51814050403015846691804503441004140441030b003100a5809803400c3c803a45a0900c5480300800d45000c400507084042070264081c001054100080d00705620382c845c0d44c00c0221039a0b9020003644820054030310003c50030052000070030301c50000504500740b03844c0b44102c43c0386c100c031200814400c3d4001c0c0c00c40400290002005511742c0d00c10014004c40c02801e1070900150751658070307001107a02070032030001d01105005018000f03116198040c0da01850b0000c1c0b800c56440140c280c881c00541c0300c55000342c0030981402c40560004030038400d0310700001e900300c00c40c1d1a060b030703000045070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 780372077 1250 780370827 780370847
    0x41707080f07030b0a1404050d0f08010f030b0a06030501050907090b0a0b120603070f081605090601050405060a140d020405040f090c0b1c02030c090306090607020d082224050c070201 80
    0xc5c074241e40c1c0f0f0b4450303040240e40e2141c5000354010030103498a010b80140040403540c40c14803500a00405000401a03410b40030b0403c0c00701d81c1c000300ca4100d40d03101c0e0b0340d440000d05080e17417000d8920341c209014009100d40200d41e4404440050030b042003404001410301400c422030f4814815440d01c188500004900c0c01c0f5091584013800505540c18981c8400300c0c154562503076005030b011540b1245040307140008003003aa0025000840ea40200340c038180300000d245103d18050103005820200314842440c0c015841c44034100046c61504c2d45400000b1107000c025005440b445100c2c50510340e03000302c6980c641c415080b220b50031003284858513080800d81002d60b0b0000003200100c90299244490200c13092001e0760046400001c000d5a80080340105440c112014118442da500414288034030540c0004031894640100e080109895441005194180801480ca60242002e0003c24420052101c003d88807030140c010241c0c20f000b0140400300103c900071143d58240366004c201820242d801100459 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 780373327 1250 780372077 780372091
    0x1202071e030b01090504050f0d020d1704020603010314100501121a06030c060a09031b03060b0307210f120c0b13200d08120106030c05070302030910050d02041707080f07030b 76
    0x1400680e00c0545c0c0c527203401c1e41030201d40c0c0160498485000ca255100a1101c03042c0d510080240c45c2e0305103a00021418801848014411805401010b078041c2c02071101c07181c08444013000304038560f50782e1400f050b808125001202c842103e0304890030210420b0458a000da03070050001e1028841c40418406c485c1d004a080005002c66083c00200081e41594a01c07039200c585200910342602c1c6203402e0040e2410240e41034802c1e00400018044038485820200301101e101c441011440d42d030f810a4868207021142c00741c204200c0c0703444107060a404c4072801c0209071003100b00c1c0c15203945046030b4500c1000000c00003090003180e80407000d804204526101d03030001c0c0051040c48600000d81d43c842d540ea10120340c554184080c080108421609442196608840343c2402c03071070009240d500079120b115040352a13118080300d007050002540301d0070582c0e0001c0c0c441c09046585940f542c5075000f4800c965400d000d02445850804210001c01260b200700c0d0012305401041e90034150b40e51350200010090060b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 780374577 1250 780373327 780373333
    0x1507020a170f0d060302030f06070804150b0402070807110a0635070c060b1008040b04150e03070b06032e091b1805060619020a1202071e030b0109050405 67
    0x40042010700b42c0043c00d850303484400002d4038034035500c14142003100c280c844a4a41d00914100030060f41c0207881c40398411780c4482c020141250480e2030500a000c21100309402c10b01c045040c00410200600511146000701441189000d0840030040240d8244c0203420000355018603c40c1c1941c0740a220000da0824085140c40e0050220303024803c03103804560a42c001484600540d040c094544904484106c040d03564507403646807000c000c0d0002c440940000e140c005044001000d1102c3c90340071200c1d03280090300c103010240d8081d40c02566601300c2c0c4c0040e00c0380904c0002141c1c8610340040c01d040c0b031a03407845140c650385c084052600005408070940c1c44443d034880c904840041e250010080550070003103014402030713040115a440c0310411a410b10241440d00c8180301c115a685000d40e4030100c102c0a0858010f11444001c07400e210000c50300418000100701c40d01e80050300450782805035070210302007200211002c0030003010072001d44030142a5131911401880f038011103821140d480345c0030b0011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 780375827 1250 780374577 780374587
    0x5011412070f14011725030203130311010f050c1c0b13020903120705030d0b01030c14130f0f0311010c030c060510030206070303050108010501150e061e0304030206091507020a17 78
    0x40000c2c45041103038031048103100c51b5004e0b2401c0000042c881e045207000c0c0350031411894010940880c85103412000350501c500b081c885001d01d403094220302c0c02c00c82c01c0c01c0b0034061814091400e501d16040085541d48075000c9a402081101c89840340700d01c1d143c00140511060300d280440040294820b8ac0030a400d4001c0308001c40100c41c2850040c91030707905c03403c0150b03600c011143c100c0c01156190304174141018240003800014541c0303d09900184a17400b82c901d5614103090f00075a038a00e00e42d501c003049001c0310060008030400004030704400c60340140c6088041c0d500c0180110381100e04004000c001c255140001400302d041e5074031aa034001185035240916549a07000250b031f80e004210b007200041d80320340c0107205c284002e015140c010f0014a02030f4404c400c4256003d0565414842c03e24002c0e840400e01c0900c1c0e0b0001250060300f640f403407280b0f03542e900302418000d440f0701c001ca5004003148030328000a030483d90849034043c801c00f207560150514151035a1404e440c80c5401900c000e44c80401d2203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 780377077 1250 780375827 780375857
    0x30804080303090118050d0f051903021b01091e0201021e030c0d08012d03210e0d08030f070c0501061d090a03050f070c0905011412070f1401 62
    0x10040014000c124029616880d03c84445401d40d40504260f04410182d2206100001c070002200350343d100050a01d203010a181c0c0b401140c003401910450a401400e0040002c4603640583c0204008003562544000c1c4030f080d200603070b090361029400102030b4504440f004002540403081685071910510540344903005416560b072010040f0250751a076074100180644401d04100648440a682030800064070340c502881f111a1400301c8503d602120410356a0950064860b4515809954016842c4034100031510050140200081200000c1542580c0d201228984406140c1010303900181c0640345035646d942d4103000f560050180b005001080090b500010403e010344406401c0800300e0202c9103d444480100500e806098103c583d0003081a8101180c0d02c581101c1c00002e505103c40e55540181c64944c558008035072100107101d02d8117002203000701e00342c0008404001d0407603801074070052139550b89031200303100d11643c44914a07664041103440003a50441c102c0f0801410b000c1c00503045c0e031b5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 780378327 1250 780377077 780377093
    0x51f020c0405101e05030c0f03152805010f030602070f020a090515090c07171207031a01020c01080106031112010b030a0c0207060207260d02060621060c09030703 71
    0x920b0010f15083c2000e014018154040a0254100c14060740c40e1201480d00012070740b11088052028000c035002406080c135502d0820aa040448040c014000c040c40c1c220110f0503040203000d41401010341541f0040103004031402158140c80c9022120000240380d0b07900c98000703500c07500d0308403041e2044195100150b5200229000204000040890300c5c0c60002c1e4100210060240c1c0f0358451848441400094264401038400c50741c0d200326140a1140170043c1c0f80118010351031100280084d0808014242e980354000000c203103e5060000d0060030700100581e2180521625940006c810130b00400989200b50032005c3c44040c0d40a0851400560510800c80c0c448260841403800038004107100c0e040c4030b10303c5042c0040025201800b112410b19900944404c0d0a07c628203108a40200003154104400c04405030050314008842d0706407070364000070f503d5490480b00720380318010525018005440f00c644144004400001405480c5e03144809c01e02603410081405030107105030640132000032154 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 780379577 1250 780378327 780378331
    0x23040519020316031b080a02070314280e01021b0f060703090302090109060e040b09101a0906100207170c06210112020906010e010e150a090b0301051f020c0405 70
    0x1101000d5158180701005010303036084034608481c00c0400121588102d1b800210f06410140683d805680c0700c1e52810125611240740400756640724001401280d140c1911500b110503100140350a450481e400b1020340d061a82d10f214a030160f00102003d4030030324a10138070085895002482480300c0900707040418115088200b0860100d034906c0024404d51a180740051f005042510040c80164109064044001800780c002040001a0000b00da0640c03428410344021044c0d40f4800c009000071000011785008651180d980a84449001710300c00d8213020010800b100e0b21500146005807030100008414001c82c400310a5501924074401c0903941c0700c80c0140354180e11889002c01c080c85501c40300c260340300103a1202e10b10840c48400c2900503115002c006502c00000d0a00c1c030000800080107035401d42c40c0c1000e031755010806080540740e0340100da000e00302011031603480b44c0d183c07912111035603c03a220070302805a100602d007100d541c4c0180e4100014541c3c0201d4415a0041540040840d0079a041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 780380827 1250 780379577 780379591
    0x807020115090608070e01030804050112090602160b160e120f01020d06260a080306040b0a060206070e120c0906062104170a0906180806150109230405190203 69
    0x1100010440c1484c10013615000c0c090f400a00426949140e035402c0781e61265114060600a90350b40054604020b58440c8a5140e005070056555500e000341e0310141c0142c24900701c4407128090080b80c600c1001008814401040352114011b0300304040c20045981e2210408030300c184141300c03c0c020840c0003800074201844100b18082401410300342e800d0b015141c03a1000c051040100c100003600d81c8030000d42e04000130740124040383e40b601c40401040107050b80c24490750b00b181c003218000450aa000400724854a80340d524000340c04060b5003004800b1043c00c0e110fa101c0d90200384030b10707514500090103a41145e002401e442ca07095010091880390240302c660407102540e510204402d102c501d0702d20b40c1100b1682c40341c40c1c2c03400d100da100190101c3d42c507005900c10421400d0385d0150900b1075501c28006001c0c054200d81075442c1c108841c6ea54000c0c0fa8039002d0018032600000294030300d4000c8440c45203080e030551811140241001d01000b040c00030015466103030240031425510300e45200031400390350 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 780382077 1250 780380827 780380831
    0x605121b040513090c051c03031d03160318140f03031213020139020609030a0f060e010213030602070c120b09010e161e03020a0b120105011d01080702011509 69
    0x841d800c0000c03100e122584907e0082041e490401d41403110f5462040303c10b039150600007030141d24115003114140c24840d01d5503051100041215007108400b9100003814421342d2101c00b410780c440e00d60502c0c4640ca225140f602c291039141a0b81fa45401c41c1650b8041c00e0207801c582c10b01d00b2000014070280000c0d5291849124107034417078415940d200110b1020358100c607601440e61812004859012281c400c0f13004440401a50180b007103607980401c0b50240c03400103045950407841400c049000740b00c208000c6503064070300240900f5901040c000e4071b500443c015058905107165889400283d41b12800468900e10319043c04501207000700882c0c0f05407401144505000d250084107c0d0842da29440c1d000b5090740166500c44120251401036015122985003198085405d504155440c40d115003000358010003c000c08265a5a8400034180c01242c0b50b58825059076501c0c01980c803203c1c0d42e5844240050901088a150f50059000c543c00418601c0002100c240c004000c0310340300c20315000002915 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 780383327 1250 780382077 780382091
    0xf07050631180207151509020d0c030b030c0d030c08040e1003030219200a08060c07290606210a15080f060109050c310605121b040513 59
    0x11428481c14000e4104508214613200c540c1e04c0e1420850300007001c4151490b2a900c2d1401c1c018003c800020042c18071280070364440054000c03103030160021402031030010786000e074406018900002d80103848000948030a440c49402c0d101120a21000c41c0309035003a00f020040042e0421210301401d2140e100d141a41c1c04550861078000d0502110809a04410b10b00341d83c04004980c51680201419401424803020800b190002ca20480c40a500680c0c0750301490013080440044070004003a104d00c00c561000c7d044481014200e810703103040030400d0070b078245140002d0160030501d00924121040d50000030700e2681c040200c04002004444030004561916010980450152480c02c003034034006000e80a9510384104295441005104400e905030b03c03600422a41e1403e0300843c3c4955a0a042081040b0f2200c41c2d0f038110030391002c80714140c40440250001e03107103203d24142c81000b104100400b0894541c12403200c081200044125010130040000044658641642c6090b403115480d01213000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 780384577 1250 780383327 780383339
    0x80105040b010c05150916030b0108061303020c10030603050d0314010b0f09100e0a0e062e0c021f0c02030d080105030a0b0a060e130c05030f07050631 66
    0x303a1440989941405440524100020320103d82017580001d0068981c0306079499299071484c1140c07d8012091400b201072011060048070888a03068400c0f503021510303103465495104040c0a00d10304080c005811100e1000d0389860800500b130468002481c000c0340c03150b01c0b900d4460910304003041a00100e0381d40c14982c0d5642003d00389450040ca1820450341c10103d0760b9407009124402c40d00f40c648506040220103c420b4020a10400d06c1c54024000e170441c182c840a0701d112080054800c58413a5a200c0040304031400115144000c40004040c58035403181503500944201da01c0c0f81c4101d0340254041d41d51400d80c403203500180d8040d4220b80d20803034140725a0062500f0505140005400c101c0240b0043c05107440002d01c178502e0075030005c0c244215a56015000e40145070b150410140c0701e070b1840c1030150380c020103407540300c281d40185038100c0300e02d9840302010741e01c0351118034003009504404000c2040e40b4003603000c1c00d01c05e030f102c0049541e40700c1c0c0c1d881010002d10842c00881030030004050140701c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 780385827 1250 780384577 780384581
    0x1141026070e0f0301020f0f030a09050a0f06110304120e01200a03112808160b07081302090a020f19020f0f120f090d14100c090e010623040608010504 66
    0xc801c01a8021031400c510f540c10300b0b034107202380c08041d200e1400000c04030b00c4045041d40f012102e03640000a540c2106c01c40d1904900c0b8480b400000e440312401d11000174200bc0b001d400701c030302407540582c00141e5140c0c01c90082c2d52044040b01141d0510162161a0000042500c4139940f0504030741e0240c03c14180d541342c05030000366141d00d0791080b640118078103090140f00400c200c04290929a035220312040701e1624007a94070030009244000004903450908201d4543c001c01c0c09000b15884030200c036540d261005001e041d140d04065444010340380401c43c0007205600034241d100700300c8200d9141041c41180f210a14141e8001c00005038448416203031425002d1000440b00d000004c06019080020031a07031040d401010441d0004000000380c140d56030340c0700d0b0100d441b0386500031041d148420040c83c105448540700e02d0581109400c00b40070300c8200b0f105411a00950361800000040303a401e00d0000c89007040e80c103403d0009410185050b01d0b500300f621014100501c010780e5042c40b0380d070500c03040c002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 780387077 1250 780385827 780385849
    0x30d030b030d02030f03010b0304050f0102130e0c070b06040b0a09110909340302090418120c080d15080a0501020a0e06090f011d120f0601141026070e 66
    0xb08541003400302d034081ca000c8204a0b81110b485500254030381d2118100241028010800f858007580b0000303400781400c001410f903074121007200300110345680d10544055030710710070210000c4c604800074001900300e00e0300e80d0010700d070410068181068a03844421001c00c541c1c1040d0b650161020104021000e0301d000c03102d081c0d00c0f00903803400030f4001451074003910f00400120f80e03e0ba11111a0080c2c1d03900148680e05075980880020f01c20b018605070103021040c45800c9030001e035503e9812104207021070740a81c00b80c000c2e0700d5114000c14038142c02c0348010b40c001c110340b02031120300c071481110000c0d011408108050446001d20001039540c0d111403000340451201300c3c0358a01a41044c081403c85070748040741b40d0300401c42070a10903103030070792019400400c184000d115507001110880700d0019080c005207204000b0041001c6441503600d031680c1c40b0022980b1041141e116103104540100c140c030030741070360b41c1d640c4041081702d007a0f809074540c2c0c10032020b048034620000342c0951026a03003131402d815184 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 780388327 1250 780387077 780387103
    0x30b040f06051507020301111204030201060f080c15040305010c0519090605030109050a110c0a0b0f060607121e08071e02071403100e0c100905030a060911030d030b03 73
    0x1c502c0e01000c01c0300c0c40d0490501c10b2441c2000b080400079910300303411024010740b00660b10380d92896414079104110030156019401986040b1001c03954085100983c17040d00c1d07020004144404660f010060704021401c4882e441e06810300c40000000d009000e00501c8c50820b0701d0f41600c426014031a820105c07410000b9604000b03102c0d504101c3c0e142c010301241d05486a00b6404181540c58002a0000d400e56505100f00101d0000310070741b2213100428003400203445141c0d05200b5444070950200001019a02a07030b1103441003024500148030040a140140020300300740990441c00808030818031481711400c07001c140058208581c030781d07100c094000c080700c0840802c1c1c081440c45100070740c0d0311010b0040380800200d10941607003640e4200991b0340c00647c0d400040c440310f40c298420a442c2d0383c2c400350080c06590769410a810041c0101d4594040c2c500c040d0090003c551107440303030f002800254000361203503010a54918541c3c0c400b40501810b4042c42d031804518144184117062500c44044060 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 780389577 1250 780388327 780388331
    0x31615050606040e04050a02090f01050a06050903100c0c15020904060e090a12020c0909010e0706110a062c0f0c040c051206120f010e06060607080904050c0d0903030b040f 75
    0x45600e42da00c034241c03420355109079940346540c0e80306e26000c1d18200b440203019500480e000c082200800580e07070317000d040c3e81e0261480405596648010340d598040c01c0d00c01c0303505400c02c2e80c400c0c410b0030895106860140f00385ca84501800398980302c8401c14180c207003400c0000c42c0c0021b040d50880c1824000c400040c184030340d0488041c41e1516003141c8448080384000c041b404103480c07506100e84204403000305a2401001d00c051030824040e001e000b00000042c0c05450b009940300000c1c0d403800b9051651030a1221030250450507540d664030700091194441c0c616031482c444010f020f40b02403866a20041c0c1320454014035078400750800075450401700e240503900c640e040071005403110ba03104c1c0913900b2801842c0204600c0b91074140c0021058841801205040d03c00c1e84c100c04030303208054000300c0e01c1440ca5021f40d5805e40b01c140a004040c400c6000203003210908010411807410168440795102c240f901c0003034240b0105101030400d44507280030681c0001c2e04e40101c80045c1c0390078030624429400030402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 780390827 1250 780389577 780389581
    0x10b0f0108061e030d0809101b080c130b0901030f06050d020f030f06040813052d01020a05071d130f0201110322060e0108010812180303161505 63
    0x307090140007080c06000f50964061400740c0039958002c08154200101a40c941c10741c011310040800000303d411040c03078420340050081c605420710503241400310000c400001c4180c0c02c1c3c01640d081d440030f03240c0ba815190401240c90000e0809a00e200a0034a80c1480c65031060040001800e90324090004442031380f801c05d003002240c1c0c0c1c550b072094281d0b9058505103000545440003d0038205010940d100c640640320400c02045503140080c0009081128003c01842d200c006010703500c003640e48000c4070840f40042640758860884440c0720581014411540e1031820b40e034895040040300e50045205c8140c0110700385002440801e00e03580400926806002c4640360349510160350004840a81844031012113440112424000c4882502038001c4003d001404406460708540451140b80c00152007030082108662150150604032100c15005144402041d048040340387e2181c01e29009a13680716140c1790f00fa49052026003100031940c0303140071401d515807d104071903989030800e4440c11450201 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 780392077 1250 780390827 780390829
    0x2c0a12030831051c0504080f0303070c030302090f0d0b1014060d0509030f0c070501170f010312020a0c09051506120106030504060204030203031305100c1a060a0b0c03030603010b0f 79
    0x984507030355028504610145480350f0030302d030b418030030741c0b04220305651458151400b0f0150041e0081c4121070103501100d0140c00124142512800700b9074003440025804800d210110b840380d0040e01d4000d800406840413194900002881c0b040d505804807000e50a1508000c040250503c3d030000500040d4943c1c1c112a11180002e002403048070b03c020350051380c035170110b003150008105441a980501400d140c0e241511102141d0351031039440f4103400505c0700b00d0a05480b500100c0c030300d402608220011a22642141d03030304030454165403001c40440c0f107900100d901080d5561142c8006004071701001509003030441a0009844015114900880040284a107024108442c0c94111038180c03400140540703a9282c040040d02c1690300107541480f01041c01000c1113610f2001d10f003145c10031140101c107000802000c0d101c0034106000941090507035030300314402c100f04114050348401d00074200c4181585130060200e45800034010f4450300e604c04020000f642c01d0900ca0004034107070403200b011610000c0f078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 780393327 1250 780392077 780392131
    0x60c030b0d0c120c0e130b1b1606110a08010e13031e050d020d0b0a17070605031906031a0108031813150603091509032c0a120308 57
    0x210403c8000040c1106503401e000303410f04504042e02c070305503985540c0e04000b51540103040105006886035880c450100b10b02e0810310a03501c3e001d007040c442050030000045800d10760005640c90075503141c1c0e00d4030380012054841100510a82c11152600420f5504242c1c0c40307108040020001c0c21070b6190382c840d190100e40c001e100302486110b03095003071002d040d90b1074007141c450040b2403140740c3c098008a40020a140144c00035691800706894010f4656620b0b401800501c4000c0f059440d6a048080309200c031718810390042d171380044181a500740d00c00c41e505c2070108641c3d141d44181c0300c081104207032801c808400703000d0794010f100c40c100a5040628a0340d075802d1000703040200c24822042a217040324284021b40156825045000c3c61007040f5690718400f8004c0d18010008a820b0086d03c4082c48180450b0311070000c1035505940c8407039484440c0d480d00d2514513081d0303140646203040044100f5603070303459013203100141c024071351041400c40c414500507150f0000917007454500852205031010070f450350 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 780394577 1250 780393327 780393329
    0xb0f0c011406031f060f090504030f0905060d0b2d01020f010b1804030e0901061806030908070201031d0109050309011103070f02131409010903090602030c0a2409060c030b0d0c 77
    0x358100c0f040400341054004c004088942c0440040300c21400009605c9103154003052081e400b0382c1358082c032480144130495400b04e41e03010b400c2d80403500388444403404c180707903101c0c1458a40203001c105401100b03c80b0a8443c80d24581c103030b10391250007144207001e940e05000e50704814001000911903104240e00140140000b510707444c056800b104000307410325225040038000c80b040a03000c4462540c440340d004101c802c41e241a4020041220300001d001c03846449503015068001118504041080e40110040c25070030400000c00400e42807503102a0074288141044288948000c50b512075001d000901a0818800c0c00c17813454005010304000f007035203400300c0003a507941100e9065001c40c241c0e550344000e0401500301a0245446410000d09040540c01000c0c802c3c080c0d120100400d80e0764608aa882c4107141ca9140d4903000b2041c0c40c000100464007190280e038000c400c03242000e00304000e100841e0801001510102c0d1550b003c40e000c65010b103d5a5070b0850b09844125900074151201e61000110f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 780395683 1106 780394577 780394603
    0x60e060a090302100c120906050409050c1b0a05101e09020303130608100512071707090207061e05070f081504060308131401091503060b0f0c01140603 66
    0x41c0c0b47d1001180c031705075515460541031407101c0e000340c00083c1c0110f10801e8107211040b4000c800c569440f80d1090020000c0c152031949080491038180101201d050451414485100c481050b940c050320100001202080c03001c01840400e04d1807054070540c44040380d6040c0c01054050340404400d0040915440d560700303482c0c40300c1c2088120300200043c041075500c040c000b007002200c51003d16600b80c4010007920701c2c2642d24096003050780d2001c0b01c21503540340d4403035502458082070000d443c90103203204010040791074801005454030281c041060140312544c800519008007010301100204805081405015a40d180806003038000d40d51021842020711400305031501341100c5400c803071300142d4801040d14504080e4075249c10260241000705a1154804100711440700c00810545d14214200e543c0c4500d442c0f4801d003102e00885c00340c54502d083d641400702c299800909021140c0d9 = true := by decide +kernel

theorem cover : BRFrame.Cov 780215827 780395683 := by
  have h0 := BRFrame.cov_init 780215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 780215827 ≤ n) (h2 : n < 780395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
