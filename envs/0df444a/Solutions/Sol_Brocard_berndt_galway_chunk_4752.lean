-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4752
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:37:13.806981+00:00
-- url     : https://prove2.me/submissions/934c7cb6-9532-4e2b-a7d1-ee458dd5e9d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 854496402 ≤ n < 854676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 854497652 1250 854496402 854496421
    0x90e0c0102150916091a100f030f020717040f0603090201080f0402030a05030c0c01090b04030816030e04091208240f01030f0204080d02070902040303080f040f050703080307260609 79
    0x10300714582c12208081c0b007008140c044050384110748a40340351b4007019141e0840780411034020041d51905000403802c040b00100c02d03110b500420707464183c10708050300300fa005035074124121075109440070344010041810041e031001c48074001e00a01490500300000f951540008152060003420303603c200c0140340200d0300f191410050800000e1b00002500d880350b2100d01081d40b9401b90260240c0001c0880350041004402242180d04a950140850380b03000540c2c1a08086202d00b51420703018000c00410000c0036440e14003514200910540b0305080b94465290050701e541400b0b0643c6071224155552401005d0110305011411042202c0501d001e1070900d004034007801d0306a43d0289602d0000c0740000c0c1d03040b000205c85030340e40f400380c017522051070302c40c0001800c078001d07440b010300040c4220340450351904e089803100360080d000e900d200d5154a003075100d441c9091000e62007160181c02c00010005440c0d401807510100440c10f0b015141c0614600c00c21520f49000a003030144903100c044041001202c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 854498902 1250 854497652 854497663
    0x1b060c0803160c121805090c120c19080f15030601090506060705010905010e060606030c04090902010c0f0302072c0105040b030a050a030801051305010501270b04030c090e0c01021509 80
    0xd5000070313000641d10010400601d02d4512030310926940b41e40e500c01251518183d524180320b80c15108a80e07040003008002d403405c0070005098100a01340800c6100c03e0803003070502e030a0500030340e52075a500d5410510110106074070010000480301088410410703840d500460703014112240100042034036203c20001032460321520074002c215603c2c0041200c200034041d04501400345080d8240d03100f0303a490400340002c51108443ca51a4900204418411210a5800000164018500f41e82d4500707140c1d8400741d440d10002c3c804c0e005030740040c00030041d40c8003a0b80044141000401c03904044880c0325007240798503806004d414801c94076407001c0119600e08014a0000c80c0e0044126100c0c0000f504001d42001030a001c1d46029928051450f45001079a00915040b900182d540d81100b440d82403100c0f45000746c0900407904800000c00000d80c14407650090000b55000d020190b25003458129141c003203440106004c0440e03040100302008a0b078000c5040349861850110880c940c0da1104042400d01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 854500152 1250 854498902 854498927
    0x30f0305090330070e012c090103081c0209030307031409040c09090b01020d0813050f060907060e12060105010c05012903060603120a0f02070f031b060c080316 70
    0x24021510081861001c40c601208540d504041c0c3c80469280c0e48403c40d100f034010b40c4100c3c041b84054503083c0702441a04000340ca0304a180d03108450041031030000032138940c400e030310940c1c1c100c0c00401c15103580014144a00c08580284204601e850040404240c076801100c0300501401303840300b00004503500900031075405040083c42000081c6000c103000d4822a00e80c010700a4291030002517904071350001403a801d10500540b00c48415645207441203491140014049a01f4007400d64040c80c1c00008100352401040014003411480341000c0c8010100214000320501c110882c0302802c0704013001042840c1952400e107000352400c11103041850140c00151504046110600c590b182031003060030a44400480440c152032541c0c03035400402d55601d00ca000008031451041198088950040c0352010000c4c10702e005503803a165585081d0000c5800c19070043d2401d07041011842e9031000701803003e82c040c0100e428018004205511129850b020040c80c5205900080d10442e106502138105220346 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 854501402 1250 854500152 854500177
    0x2060a0b0f0406090c27090b03100507020615030105100501050a090b0309010504110d020306073c08160f0c0c05130b0a0506041805151206071407030f03050903 70
    0x107a99820414010405c000103540058004290070484070313800401d540300d0080c1050307454102070400c031290380207006020600da27244c800c4d0aa1914061361074081c90b0b22800c055000b4005910b440d581600d1130a0f041d000080c4a6494201042141c1d00b01e5030002056510a03c0d209031602d800000030390307240c10078ac1c0080b01c1d0b0641c04010000c2c0c440054100a215903c5102c00302545410181444403ca1114500039416000280001e100c0b610440c00d40f500d40301d0403005902d00d504d050034401c0b200060b501610fa0000c03030402d803010300c80f0b4110403041c0e0046610401140000c0200b10024141020710b14010b0400428500220500400307411202c05840000d000001ca6408186000010800d2000d0b95010b007040b010006410721b4260140c50403034411031408a14010740c007824030b0042070006c00000951414900a080b07580700ca81d070800c031003d01c410080c03480d801e00342c0c00507055481d5400070301e41c0b43d101080b007540000e43c08400c141041d00c3c107080c003107500c1e00ca00c2500d9003103014401d0920324 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 854502652 1250 854501402 854501411
    0x30c070314010b040b03250918110604050a03080a0302040b0f0c1c090308210c03150906010e0d03030f0c170a02031e0403230d0507020601050102060a0b0f04 69
    0x144108201580307803188141000300090010705040c00241d90160349400e0740360b0840c0d0100340306408046c3c0703000103e20711401a1041d2a031901c03e0070b01110981c0d1004850600120500810003040c00301109038258100c1c0c1160405141000040842c04240002400000003081802d10706009406403000f50000421583d15030340c846801102a400400820303000e0311039a06282450750181201040c107030070950300d00c3c4806045850710b41965204d00c0700c0c0744440595128000344580080b40c11401440f418a010366242041400345501400000d401446410504c0600031240e8100c2c064480b0103c0540c1e0702005042141416401045191f0302c1a02550820745040050340c2d00a0f5a070f01040302c440001801d03501c54620a0040340000c135681000d1410b4404002c5a1004610115500ca4480d20f0b02d00312600b280a8a9181c06a05500c03032102c030071001c05c040004510b98040ca55008015100500d903561402c0f0000b50b1300c10005d001086501d986260100140e103503101140c6840102400034030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 854503902 1250 854502652 854502659
    0x8063c04020d0e1507020d031d0105040503041d0c1b01091b170c1e1f08041a070806010e040908190801060c080717040509150f010203091305060102030c07 68
    0x303014001844240400b40a1030402080013801e0402c00340c002e480700ea008240a1007040c80039002000c610090503603840300300c0c400e0b04181000340200c602c164480c0707001d180c445140c00c1c000c0d01c00410344080c1e100d6410740b213010801d84000150030350b004959400c226441f001c002c00300640c01025100e40281c55814a0441102e4500c0014203600468001003200302e2100a00d68000d612106034441180c0d206107402c064000d0046869a072070064400140074210b15124601d180010b0701074a80c80d00e021074007450070030040c44014400384100404484804026150401e801490210014021410722605c1102c0103000d071a070f40d001070161039216440c240d842c6803109070310b951400514420400581980300208401d841100410621076101130704134140f540560b078203211941e4042d010101c00900344000601682d40d4000756000d03080382091140d01e8000c2509003c850500d8504440c150340c403c000c01c16154586004034182c00780c11340f00014040c0c50b103400403800c52040882c071044c01d200308031011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 854505152 1250 854503902 854503927
    0x507051c05070216050a0308070611030106091802070b2a040905090609010b360103151a01050f0702120109080a030c1e0509010c120c020108063c0402 66
    0x718040c60083d0211188507101c0789030803138200d146010700c680103840d540c0100001000c0c1e1010300202d0340314103001302c0e4844a0300710700c8500c0c1c1c0090744400c000521000303040005115042880305418688201503140080a0702e81048552028090b4044101c8155040402242160b0f4450038207203002c0840ea1340300c5e40c444950f405000300790b038860044d0013000042684001d051045200309503000c0c02d84070000015080c80703c00c2e0155000d0b07400d40c01811149585000d1070083e0124061071003003807111001c044600d80241281d14481000c00362405440d01c09445a800605481234911440011139071941544003107001a015080005090340c01d01000030100860314000e814654010b40e401c0000065a0350704803486207000c805c68640385911528554030911a0009202842041c1889980728420741d607141c40c480b00042c44400041c10300c01000d411503038044022608080c080311141310b541c1d04618200c0c0458603104040c80d074526401c0302c0300d8401114850100310450001c00454a8840c0303a40c51 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 854506402 1250 854505152 854505161
    0x41d1005061603140a0c0b090304080a0f03110f1b0a05040f0509060705041802072901170705031009020d0609060c0905090f04060b0d062f0c030a030507051c 69
    0xf00c000c01c8008240c401c050080e0000d94400ba0580d80e00c1d10b1101d129500c5410b6000c40180010080780810070000c00c818070100300c0e041c1c00a00c16812200c000d0124200100340ca6000b851a40c800d8200e0101c1d4041c0740030003c0e003039170402c800b60160007030800041c1c00a032003000d040d4405a0814109801c4003d05107080d800140300300c3c01c841c2950b0455803031180071a8035204a000b001c080c1b40101101c40803426156024010f03440c8203c82102d0b0340c140c0342c0200710390f0107054640e009009504d0307270050040d148840c0d40c00703a0000031000100001c508042c000b94660088400c0c0c029181e0b69140c071f0070195a11502043ca000d508a001007040c5240760400f40c008d000b08081100100d4200303007000030203041440c1c20601c60f5091200e030f652680c4030703030362204007420380401c4584d8400486a016000304d00c1d244912030035081c010400161800710700c2c984e142c3d08110348204000e4204140842044414080104d940d40c140c0c5140004081d0b41385075094807070340102012000f21882c00c1d822618900c0c042d500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 854507652 1250 854506402 854506447
    0x18091e011506020d02070b07060905060406050a06140319050c15040518041109040c0b1210050102070e1801111209060c1812011b0c1403041d100506 65
    0x40c9088940c0710003050780d466903a10400c130b005074071001c81000348803c1c040140c040381d8843c4402140003c07082d2960ba24000040d00d003520407607962414000a0341142c42060010b12028070400407070504200029220008410010398100100305000b0802205007d864403402004103101c68240740f018100700307150046d0146030700450341d000310b0a000200c8648420310503580183c00ea00f16279804c0090190013100503004840781b60412401089004c1d0030030280c040c4c09801c41c480403191070200c56940d102a090b0f0b0100d815500f00120501c075103800851250b900c1111003101c0d19103401000841f90041c4180203c80c0342c0180041540c40c8a0f0201803103090040102408580154803080a1a00c1b14032480d990342142a0307881d01c100c0240d04000f609140d10018520002401305654008080c1d19002c0c03001c602c000a52503102a4204010813803030f0b084602086d001581400d00700f80d081d0340386000c200541c1004211140010321210710380e84c655009001c010b0070058030b0311442c02c1e01c421101508070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 854508902 1250 854507652 854507681
    0x1401080105010806160507031e030b190302061210030b010308070b060307151b170309061f030f05160b03011401030e0a02040203061915030f02070218091e01 69
    0x7000043c641030300103107450094510b0140350744404620282500d16600001c011818003510400140e600c1c110b80002e16411030a648001c83d1111600f4108030103203640c00200007812120000900268807080240c070700128182072041815104d1455088800c44030b90b00040105406c10300210030070146101030044180f04040115040d15503000300364440c86039008d4501c5040c0142d1168428512468010040040910060f01c4c0002107848100f0400e9101d00d80e030f21440c6000080c0030740a50200004c5a0001041e07110080a4408081e02c81d051034031880042c01f16200c00c1000710030b000051010206560368000c0c40101030340e9030110031503507400900c141c40c810411684240d43c00e5019004091440181401070103152007a5820400203401c0948601d0300005604030104c0400c0418030034002406410071114959a00b00b42c004040d252070342e014004031801840040016243c0a01030701d441059807a281100b035840621070f924202284408609901d20070300d400b2408031040d4842e0801c6003652 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 854510152 1250 854508902 854508911
    0x603150412031d0c040f0b0603040c0608010f061d0103060b12090f150417092101051005031b01020111040f03050c0105070b1501050f030c280f0c06020d14010801 71
    0x40c89a10803540714002d142c011900100034004c42403400d580700241e950100f40000443c0850038001c2041c1d90000c4808172810130b105c00041c0411038110a200303004200142401e00801d04042d0000e10a41d101c103e100e41101100d40341820703983c000c0d00710700d01a00c8100300003615410724020501802005446440090192a108105017940440c02c034440d02410307403c071328035a11603541d040320040742d44250200207201842081c0c3c0e10390303c0b52200440d041020400203100c02003d840c490071244040c00f0b51001d0b900d282c504002503200410004901804103d00b01c00c0c594034400140e01500c01c04070704420038080014041504a241e0303003110252070044044861507503902c80190340e01d100d0540064803444400c2d0024000d03540d0b400c3c0d000005403061420900304010454a0030f5590016075a403041540041130b607003981001042c0b0b4109490511b06c004a2408035424081c2a200041c9800030070410261a5841404030540440c5c0044100240400c14021003051f101d00b500000c0c0034a44155090 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 854511402 1250 854510152 854510171
    0x30519020102180f030a0507080d1205060f040c0e0919060512031e090901030b0f061e060a030209090f010e0f0708011502011b02011b0813030305060315041203 70
    0x148207440b08845070280e200d6000900c0c40030841c04403104e0ba001039140c030034000e81c04000380b801c1c41003400038042c20000f0980e00f06111000380c0405503554400c14001d150070100040741d6508100080c003104140c400081c1c062101100312211180068004d0700301e107012041c407080c0500d25000501c844500c0c4010088191100100084d880b6405814081c81e0702c00e01c0b02d001da5403140b84043c40b0026858248518158903840420074403c400d030b2081e1400044901000968050000e549a1240d0704031904100c00c041c202e0808201210003840030300801000c40d85405072030090381110400900208658014502083c05600c81903090040a0464208202246c110780d015681d0394090700c49034a03507140b1a030a040e00d455081c2e8290341540215903c0320a4803624803d0410358684620060f800821003243c000b411208a0800300340100400911204210003500310070003402d81c013640b5180104181d15003030000b0b440d101c0071504030084a000381c0140005c00a90381c02c10400c03980c164a0a003d0101e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 854512652 1250 854511402 854511407
    0x905030406120504110402131a030403110a0510050c070f060506030c01180b09062203050f1b0f0612072a020d060921080109060f080a0303020d110304030519 69
    0x40d13600804c003103210306140d2014a400d80261480d00b8140d4200d1341d1207648c07500c1d607002c0800309048600c3c00f00f50010a010505600c01c3c412101d0105120082010b07442d29681c1c40c0d0ba5804490030303106051342e0745011689803c0e14a0446802e01c2e0401082c00c060b000134100100244015950103100f842800038907025035025502510349481001c1248003018605000c1541517400b1020341980a0810491580641402d54041c0c90020b40d01814210060079450321928290814007019001d80c4040c14540982d000041e010001020550b14010300300d183d01c021403418080c0c0b96484c81200c9054040014003a405881322070365500c5d080710395400642e40012071100309940d44000e9040040001603c0104806801080001d07101d113a4102080f9499003403200310704145885940011400300c01042880c5450241300054071461140034002d903e80080c00d50b13240c1c5080c60040c113042c3c000c10302407a400000c1c5d002c2201000300520341983c9140c5441c0081441e441511524104e54001071403c0c1020f1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 854513902 1250 854512652 854512661
    0xd110c040b2b14100b040e1b06070227150d0f0327060305060405060a0608040c0e0703061701061a0f1b010b100f1b15090503040612 58
    0x20400b800c1d140c0303075101c0d90284065410031090030345503640806100100082c1e05000031941440b0020207000b200015290140a981c03543c42e08a118604045926103c01c03c04115001c6608010b050007500d6000720011408030701410074007a41c00300d40f42402c50b1590702100c0b10900311181d90443e0810a94803040642045100040da198000300103441c02000504000e01021106020341420540c0c0c10302702c0e01c440401b0300710341401202c00e2a02c19041081e543c1501900d60801c0c0e049800348058a0514081000c0303020070311400c000c01ca00e004c0440d01b444911f60a020107000300c54103d0007549011030018021300047d110b503400d500780000d401d640340c10042c0300780000c0d50343c404440c0d40140301d0211800e405030000d0b00301a00f04c00c1c0800c80c881641d4a415540400200004c002003056070034201080841c0440c00d0401c3c0900c007102542541140c1c2c0204045490106512882035401240c10302c100710b0940181c0390300c101441c0024240c24054000080c008941c01561000d9000c2032500d03a980a85 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 854515152 1250 854513902 854513921
    0x170106030515071211091f120212040f030c0804060c0b0c030714090f0604090605042003011505190c170f090d080708031315020405010c030e030c030d110c04 69
    0x3800461048282c031055030050030001d00808401c3d030034a4107890001f5600c45100a06600e1582d1841c2100c083c1d503009045a8040b43e8100c2045080c90180369141c42ea07070400500041070410381410724001c16010b0840d090f000e5402480c0305446a40359003015007001062042625180c03e8480011075040030301013142c0c4210030382e56030802068601c01100d51242c001d1005164000e02444604240780c07503003006480100800074020419070715040a00003110121420360071244141c40d800c20003625880b00300c0b4112640c184604801c40c0000f0011192406281d8140d56421880784a10311660352210707028840c40c1c0188444280e0814045070100a0320504044002256062021000c03d251943d04010110700a0440d00e1520380e03070350340b0140c40360300c00c03101e40720700d5814458040107011003103000714410a42203101310324050904001801d1070400840090401c90400c1e0030200c5600c0500c42204002006070445841a01070740001e003541e901c0d030400c48211710404005c42100c0c90540183c03620b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 854516402 1250 854515152 854515157
    0x50c0901020c040504030509041103100506070309030b0a0615210c021509071e080c0418020d110406180b100c0b071106040c0e070e060d1517010603051507 68
    0x70240b64505010103018000d10030b80c18008180000300d1a500c03940209444544180c5c0015903a18002544030300c40311450300310b103010b0301d01405208002500b01200b40f080c0ea8102550055a54881d21898050505a003140d00e0161003005180b1044d900b201d5044020807210245522407443d2070480011620081092801680018a0302075014070f00f113885904240b4000a542c01251900c00d19403940351000b00d100ca0901540004020038601030115220701001110309201c5049050601e61103241c030303484040c1c49261142100000c2040303100000020030b901601c180082a40c0e2203500d18000c48a1150501030b608200e55441a4071741850110b040d200340c1d0702c0d03240c00310f21f040e00c80003070055005040c0020f006a12060404010081007020711582c460b081c400455424038500324058140600f115082c0601d054100e141c40d59208260740111503807030000940c059141c803606c2d5100302d03d1b0348030180484421003464000481900018140c13405201103d540320130324060703079040b50802c0f14070200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 854517652 1250 854516402 854516413
    0x7080f0907050d03263705070e1f030608010b03060103080a020724030e010c0206070e0307050a0e090606011d0405040f02030d17010602012a022103010504050c090102 73
    0x280703140c40c4880f2071209009107805c1c411030300005111030341011242041881c00010030304001d0511000b4490b015001e02c0c149064400c51020040d00a01ca280702100c546200d44410000301e5161040c2e0002003550f1008041108440310f0402010140810000380720000e410203601290381c003014010303181c40b00e41c098020701060f881d54072681843d4200f800407101318043c200000a0404403002c000e0301c4005001140c2c0048082c0c01c0b00501152100c1c19007a80d00d9051040c00c3c05401e4012a02a80c0000b0506018030080562800a030400e03800307030001c540c000320149012500c401e025800b50300c0340300c0ca00704a13003107926180010341b03010001102c04501c0060090b40c1c5031090400742c101070b402071300c41c6c1502900b075085a8000303410952000d94035400500004801c0c2d9070003a541080e2401054140001c01103824142e50402c80b46c504404c02060700c40c900100500b185100300b01c84200f1008201050040510404061000f54028400c0520071401c1001185102181c03104490070100160005c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 854518902 1250 854517652 854517659
    0x801081b061602060f1801080103050c150d0606030b040f0b061b0115060503041b06090b1b1207051005070503160908060c21010506070b1008031207080f0907 69
    0x10342d0141c52002414191003520100507200c02024240c03c0e41100100d6440c0c10f40043d2800c0e80c8034041018604101040004001040f00410f2402c0c000d502640c180705504e407801201c0b841e80c803460a4804880f40f0b4484001202540b40d400841000d808450602060308a01c0c10801039035008044194801c408110706000c001100402d0b60314014020008510140746025802074041680d00180100ba00042004104500303a0480070300e0040e0321180203c91030030280e0041c03000307080c1e000d40c0b50703c410006002c1285040c040d42e43c400910a000c05c071082502c0d1800300c0d1a650300036460480e200c0c4900900400707115558001c880c8503444c41e55485041d83d030742400d0000e1100442048405214103040d0105001000703011003403194810135410350b40d45440c60205902d203110440c0c8180321041020040c006a981c2008035076405030403030868901c640341c00e4480c641c00f5004d50b009102620000071400c10b02d0980c12440b038426200c644415095941b04403a580740345030210341a0440360408007062 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 854520152 1250 854518902 854518909
    0x2010809012307030e03190810030b06010c051905030703090812070f1b0b03100807081c02190c090507020a020a062102031003110d0302031207121b0801081b 69
    0x1603900803d20319010507111003a003603982c155172154a5117900c03c049000903140b42d5070064042a00615601c1c04441c64500c1c41d150300564605c0136028034104040c0305215014440104001804008045000040c0e2032591030980c0c1d0741ea000c100100e01049005000140e0f103200807030103011082c0018125403514919581d010210b0200c5c81c4100c03018009a011441b0314413040441e00058020713060481e43d82d05040c4a070702002840c5a00c100440da01c2040203000c484e0010407002041421528902016021060305034180501d10b6000c0800310300400381c8505105803054488100c4009800402c01515641412600c860355100041d4200e5824441004141e00c91484402040d17840c941d0311714490b412034404c41c2a41d1060781c2c903000d049040030061082c0b02201070806640304049868888884207a540a5181d02442c3c0054003203c10050014505502500307071007102004c8031804120f000307100701100d06001c1e0b041c900c4100140c6240004500d1140014403518002880c07803400700171102e0041003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 854521402 1250 854520152 854520221
    0xa0b0708060406030501050f040606150207030f02033409050402010509010f030b03010f1d01051b03070e060a0203071b12060b06040f03050a06051b09010c061e090201080901 76
    0x801c0c0c02c1552004000080384082c0301d098080ea410842013a860700702418030400740c0e03006800062800d2080a215502d00b9000100107003240d40c040088614124140002400e04240824504c2c0c9003002c40155101d06500450005c0c00a5142c002c0160f02d50b210140001120400c40b0002d01142c0b081040f1003079580102d04480040c241740c6400704200d03002001207400d5510441e05403102988414400d1050b418410400109082003002085180391203140c017201c51204000042d5a041d0001c041030340702c0e204d1045802240d01c0906081c0d82d03202e8038640250b80754440f8406444400840c03120322000004e12070000204e900c90410007004000c0c43d2034980051203051540c580c4801d04002c00107012400d101d800300210302510280ca0200e0150601109a4000411030304524241d47d2012020040314030a0f00c0074450300780f90510380d0b4042454214010540804450482d00c01e1110303c5100400a802814238240301b0b98600217191038869080e0f081c0c1c1c8030014600f04246000c1241d41500000000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 854522652 1250 854521402 854521411
    0x30b100b1804021606181a070206040212010b090103031205073b030715020706030b060703110c130b04180218070c060911120c09010510030b19080d020a0b0708 70
    0x1590038040d01d41d0352144106d900152004140b0445051040c09010052480750703900340100ca4034220301e1030507941c000e40368440104002d100756150607050b40c40ca00250311441c20303020080e06054403542c50382005495600703a5900e45c2e15850900c000220841d22401400c0c203000e41c407244103000c40d10000b001c9104007801034511001c00200e07460204c070311f43d41041408014119420304070013102001c80003d0820726250007a03010f16003440440c0c0a83e40f100402c494126070189804540c4603900d40e00b46003081540071060768004602140385a6000d000d034010825107400300c0d020420308122064030b00841d02040000396200700101001080254413220351640400545844003045000e40d9484080b11081c113000d45841800444281b458241080d06241c280f0071039004050903541c1c980000c841c5101402000e000c4c00368201c0d00d201640c000c6e0418180c18400410460b00c0c0c000803074104034184850b02c02c1281d0f038031911901840741c500120b0032329010f81d04946402099564510140c41c201000b80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 854523902 1250 854522652 854522677
    0xe0a060b0315010306020a0801080610050d1106030901060e060a050d0f290105014d030a0e042d181a06010f03062105030f04030b100b180402 62
    0x79007402c051485401c201d010b1481414016260848a103005180e244140c0010f03072981c0c81941400b490716003410102048a030101ca0410b004405481c1000040c0040c0c5001d039003054000c010321510325019089881925411400b50784180c0d607050070081020202d01c91250800d41220755040817807110762820352041d0141240d5001036901d1041c0c0c004500502d00c060f0003075485400107000940e4408204006110142020040744201e4260074000040041c20200d041c51034400700006070307200c18061013509191105998607840170a80c083c005104034058a80324034a4503001280c0f04ea040e881040c6900000410b08085a14101e0310600418440d01501115000c10200800084038041c0503a0903e030200e0030500e040c03c0203030000d0040c0400005a005141c1802c605100408500040c00c003144843c002c0428464241e00f080d03400c40c85600e000c0702c203400340000e02000f0300c03508560440c0590300b10702100e5040c42c2d94520301d9646010300c0010780c1303490011210030740d40c914080c0c025058540841 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 854525152 1250 854523902 854523913
    0x120a1107030b01030c03060e0102041a090102161e08030f3a02040312210b0a03050a060c080a150e180109060e0c1c03050c1228030e0a060b03 62
    0x2d031102000c0d41001d03881100d034886a654140100541c80c0030725180f07180000004d43c00e00381040308046a4484041000c110410301040a22003030307100b049082c011040d5800044134094072540a868604510019104440040b46000400c131800004913000a0000440e4030301b044a00007c0620303621080041c2e007021030501e061000031000c026400707100e84002d4040103950300c1c50343c0b401b10700a420f415040020b20840514104c0652080e011500202e0032102c40000c00a0907000010342004103900081c12520541010104002242d400289600700948900740303542e45030311012056442c007000c00e00e83c40303d41c00d0f41041401c00c4903030108c0c0c109403820203c182c84d4044d01d07a41402c441c1d000c0010f45005494003d4941e40b92028440c1010100c403c0d40c00080301a00c0317200810010754250001002c0200000712580d4040c014000b026582c0200d008466070ba003620084c900804201c4c1141411041c0300b160f014500302d0191040c4015220fa0101410082c440c548034140180800813080c0e4140c0603a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 854526402 1250 854525152 854525159
    0x726100b031f090c09080307033509071d091005060d0f03120501090608070b3105152703010f0915110c1018060c0503060111120a1107 59
    0xb4119010003822400758000b03942c07042c00302c0c0200300c450181c1c030021540c0c008000003404680e0000340503418000083c0c0076400300c01040e20401410016800860000b0550f8040c4100004007284500441d4880035100c1100160303008040380001040d103d15a2a03030002041500350b02c680d801c816405500144800d04240168480c008040100081200000d1000003000e1300c100207841441c0c05000140c60410000b800d04100c00e540b00c000d030042500058010400c1c0c8504102d020640143c90385a0844c070610100c0011000e4a819040c0030305071245900900d41c41200d10032038240c444981a403000140c11070001104501c0f0360640311040380c0c25548804a1886000c0940203040e111489070070402030031460789510200310350980380003402d40701003000b6a101241c00010019100c180f0031000040c3c5004180844e1115032043c50700600301401d0485814140d07420801842c842c0e00280c90307100910501c0d04400d030f01d80d0380c45c1c01030020392082030181c428614803e100c0d00020300803010444034001d44 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 854527652 1250 854526402 854526451
    0x11030d120e0a0803011212210f27140c130510050603072706140d0b0d200409120c02030106170a050f06010f03060b060904050726100b03 60
    0x1098004030740319144600208200440d011418100d1492488c15250402c00d080200c070019001014107000c5a84981c03032074809080310340c810402c041c00404103081d0600c0085400341a00c050700d00903602041c450340c62180503c000b240c02450318030010b0030050031703e505c0c0c80d401004000142500c9901060500040760310340351b2200560080754103403116144444032149910b07190b0a9407402550380058500200080783c0c0140101c085484442005c68a0b1850641c164004102c003030415513100c3d04018080050240c0414800c80012007131021079071103031069007848151000c80400400700300e000b41d00c44c1592440384200c2400a8030040004c10241d9440100e00203141c8445c1000d60350f0340100d404242048030410a03d5040d100d542d02908656142294a000000f480e201c080d12103030700e980b01d00120741e80c0c410464003110740042c801c00843c108090028110500c0b11503c0e00740040c0034039021411285509010302c5000c0b401c001c00c481c8e41c20091000301c5a04050300c207078101500908854000074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 854528902 1250 854527652 854527657
    0x100b2503020304090b030313271104150503060f0105160203070807050f011107091824050108150402040f0e0d0e090a061211060d06090911030d120e0a08 67
    0x501075070080d51582e003031080b45030840f402054001d120784d00420000c0d41f2050054800c0040302d020215110100042803006c40103e80c001c030380c2802c110321700f07150105c0f044070400140c01903030100345510410300b03402c01095075188402c0c0d40070f0354825120122050300750f214000030000c000035580c0c4000b5078112a07021034600143c0350080c5c07990303400c0000180114205a00415070308502460440007040c036a10005845030f044d4061820544d450355104200e41d8401040c0b003c1043c0e02007807401900e00e50000c21400d120304000034038011800c0400024440b4000500c408c60905500182c01c15510396508200003811101046143c1c40e0311110308108940041c040d105030002d56403944060504405c04204000400516946000341f82ca0f8050080301c820503d40501c070340d4017541c00c0441e0265040041c5403409001d8810003009e0400c0c8000c100041c40e90001c00860340311390010982d95100c43c08060b1180103041c180b070006940c20320708203040c06154101c031148207440c1050b2000c0c02d02c41d40350705110380e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 854530152 1250 854528902 854528977
    0x50714180a1a0405040f140a05061f030b010807030e0706050913020f0a020c0108220c080d02240601020d0c08090a0b0a080901050702030f1b060108010b0a0e100b 71
    0x1c81c0410300f0031035070420340919000064001401c0008110701d05400c0700110002d023440c19a0b90b0b640300040c9440c4c0b03401d8041c61400720980140044240801c00c000d0140101900a0340042c07503c901203050a802030050034203040c0b001c0060301039181040011a2103070450390003560710480d10075011400d01c039144010b2005c0302403d0407203a640c4030711001c00381c98042421005810044680200250800e043c009641c0c8507003d16035501000f4140d0800030200115600305010707500030415545021a000940703100300c0300c68504a0100304224120750324091000321a00c901680129a540c1d0f69a03200c0c1c840e800b24a0300ca00c25080c2405a00c00c0852074440c0560002e04500100080b00c41c0c090f50050b4017241e109005400070300451500c184001d480380a003a045200141c0c01040403a005e030307084c0c10307a5545006200d0858017190b9644101e03901800c50051403a00800251002003005141036282d00e00c82c5500c80c1650080034a0440f088001e644843c002c071100c4080c02c4201e603402d5240907003a0b03425 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 854531402 1250 854530152 854530199
    0x80303010b0c0c0d03270f0902030a0e0f06010501090501032702031609050711031809180a08030105100801061e03090b040f061a0d08030a060314010c03050714180a 72
    0x25612004103130f103030440c11011b0b0b000f01e0701c0340007040280d01048000c010580340014001742c3c5989485000c000a40210300071b24210380100d0b034403485884000a1403a048a800340e0394512020f0791040150308036084171090318840d41c5000c410401e4440c1010b42514072034030144c02c40d6000b6000030b0326818000b80b16000000340030348460600c08160342c841c10440c03043c52101d01542c07414800c2d6501015865244161a000302803010001d8070181d002c204900e80c4c1c104c05d8058442a850604e00400203510900075184211441864038031014410201c46060700c500b600c1c2c19544042d40903413540010054200c0c14100350720782d00c2020000d0f03d00141c06000b14492030552090044c2450904141c4000100c08401d04106021641c0326982d06104a004a90403c48181d9261520207030750000e0440750b0006008034082c00b41003103003580154001450740040b42e5042040d61905881107440d281900104100c0d088240151003114010001020b011400107000c42003495440c860b92002070f242e218003800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 854532652 1250 854531402 854531417
    0xf031704080c07060f0c06050402060409060b1b0a17070f14100b040b010e1306030c031208011a0702040f140a020c0c06070308040b130203060a021909080303010b0c0c0d03 75
    0x12200c01000508003030130050901c21442038011a004046e44020304000e01083c5c2c441010400f50f456010845010b84034440c010702c4683d80b141950103c96118086191b4040c00d00d000d408500c40020500c030200342d6001c0320791b41c1098980040f00c00740380c0000e5026600c42d41c420030388000084c09145140082091100548082c8281c16414011500482c98103400b480c284a00b1020360781c0d000e4485d001203001291828070140310466818010140c2d1b8000074440441c0d00000f105106101c089101608850342d25030b94240c0e01c46160f0101032143d0003102c1507080040c030005c001403820307400000003580100400200c800700d0f181e174885244815100c0c1c084a41e80001e00c00d4841c80140081d2658a00580751075141814036a0010140d80d001030014000344880d501040c1c1701f044940060703904d103030002c3c04c94142c0d0130040d00c010020b5001042007584d10b0250b900d036200c4140107001502c21600300b1750286d81568a402c01e40c150301c7e444400506558081eaa500e0f000c0365507040b44441e0310311302981d590207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 854533902 1250 854532652 854532667
    0x70f05100903022e0e0304051f0509040906090204090b190b1003150f0303030b0906030f0d0509030c0d06020c19050d0c110d050d0f1103070f03170408 66
    0x50030110892600d0003a5400c0840d010701003600091010103003203d055030f44c5040c01c82d0002008140a20100b02c842c040e06199007141c0703212000010f0000d42d40121080402c003080c100c11402801c2c0545c001c180440d400307004082c458a00b035401000554010100805c4002a03540010201c91600c103080744c03030a000c3d00c140400341c8071411054801c52144801040344542c280d0000e02107001c080040000c00da2240c00c9404090400c6e48000c0003408210a103041e80d90300c2c2d24018019143d4101030764007940c54640040e03c2440e0002e1010003501c1030384c020b44081d11103190110b520f41c1c0700d040700c181c152154140f21701081d10790301c030040d00d00c1c1e000310030060b194009900c50fa0b05003555076019100c046c40c003016100104a01141c82c540c40c2c0500d00f080b40710000145040d0604141003c0709a5002800d00f171800144580450034002011141c1d0f0784142034140c10b0009c0d20042d1041001c6412a0310902815000500400c0f0349078600d402801c0a046080d040c02c1c401c1807103034081320204c1c0e1007000443e450 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 854535152 1250 854533902 854533913
    0x4021c0605091c23030403051c0603110414270f0a0b060d021305070e0405190c090612051801021b06010b04060c11121c0207052707030e03070f 63
    0x110f06028084c0b80500c403525030751541c440200030100134000304440000100d0105030040f0300b1581d5000c2d50000351001c1c5811061883c0050110f44026035070032072001d4034205c0a1405104440e0007600032001c00005440728051101502c014032046126040e00c407840c0002c10404108042c4004d0203203004158840082c500495001005484130b0f006034020101080140e44500c04c10411240a84001030030340e4070403900b22948203602d0b413444d0304986403c09000d1040f1103002021079615021100b030166040350001200c009900b4460710002822880d03c0900c516950781020307821010311240303040040190300e011801c80c0c1c0030050b0900715490300300c03000040400500c03815006090301c500c00c600b400e14001c000ba004e41c0e2000d80c000c0c040000603502080540d21120414410717040c0204a5130740b504c070642c00e00c1c6c6440042840030058031640c000040d1510b440442d810300040105000b440f014003030300d5003000c8030602801010900d9224a046111a00304002800411740142c015592004031130810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 854536402 1250 854535152 854535193
    0x9060e070f08030a020d0c05070905152713030507060c0302030115020102030108060f1f0f08010b041a12030f0c0607030b0d050a02010f020f0313140a0e04021c060509 73
    0x810b2aa08240706a2250540110f2a90740903101c070700f84100c0e421803d00e020390911405400108000d860081440701c0c00980040c030252510083d20b000000210456008040c050182d0b00c0801140410000800c1000790030301c00c2444901c13a081540c1401c07080c0c0c0c1c4400070b032150040b015001940c0400100310f40d10341c405441012494078002180b8650400d000d031922207400400030003d40003c1c83c0482c40c0000e200b440261101c0c0d40205641c2c2c02511054440319800e0780344180e00b020341c20404000030070714043c481c0001d541009040c030380b6809051014003c91051524583e80b00c1d0000340410001c10700c556000707103841415036014280900e46080050210350070440c140c0c1c01001c1b1080f003000066400510505540d0302400d003001480c10f40403040b850480084191046400040389600031140901d2040301598000002c000c0a107426005009219160b885034140d81907503a000710f005800c000600b0a0304000410003286018000d440e4030b815903600341c44144446d4060185814500c002640 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 854537652 1250 854536402 854536409
    0x6010e06070305040909152a26090c1306030213180b150d06050105120a08030c0a0513150e010e06040605160210230f0a0c02010309060e070f 62
    0x3401820000c46442c024250301440c01002400d07603455074044140000c261030340c40b10901d92202801840c4405180403070074101070140c0280d034241e00004905031405041d542d0700300c0c19050001385814281295403500e41d034025004500ba40621040300c0c0301034803400e500544803508020b001c100c00f8a10710500400400421400711405e1900400da540b40c1410b125414001340c1207001008651101c00560400744c040700c101380e0340401e2402440d000c00a080d040503040b210b08031070002015100390384460b00d0b10080c12008000e9201040061900c00b08940580070035920362601c10308006504c0080801018144c01000c1881c210000c0e9002140d07001d0b40c0070000b03500a02c0e048204150420118140307004a0154000b800b002140e548070b05052a04d101c0b4025070020003080880260f00700140004412240184003500c813000080150381d8440201c4048200d49082c2618100d407019045480880103030b012410135884500070800301d580d600a00302041d03515000343c040c451410454078072030504c0e0b90 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 854538902 1250 854537652 854537659
    0xf10022b0504050111010e06070306050a0b0414190b03100306150f0b09010201090b04060903090608070507030807020f100605030d0e03071401110102030c0a03050c0c0703030e010201020f1206010e 86
    0x409098030740c0c05419141111403e08000300754004078009103014001c04d03030000303505200310780c100b000144c0d0640088045401c240c03109202c00d9202c8810110301d10490091512224a01d4040c800b5411b02880c0050b140780300402c0001c4e13160b1a00100840750313100b0b07100540da070032240105109000701841001d01088080e0f181840d0ba41c68440e404d090b5030303128801c80420a101040b0140b15034002e401901c40b00b0b0703100030011103500e0303d4174000c401420401c0003500083ea401c0d44c0452001d0040c01c0b0a401002c0c0350316460300b000403603541243c3d40c00c0700420000850007820b4034103500400401c990181103024ac800070404600309818180303000840019030b01080300009600740d0a49022884500381c0e17082c0d0007504441c000c10801039030501201c1e9043d0080f507200008011000011401504426002d42e5040c0700c0358807681d04026250048003c0f030581500403503820000240541c1c150445550180005030610800c41d658410b1504a1094002045a402d080250035a84041c051a071500d085 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 854540152 1250 854538902 854538973
    0x504050a020901092013050a091410230a1206090512090604090506121002030601120603050c130b06070b010503070b0708030705090102030436050603100b0f1002 71
    0x610096810350a0200c41c030a0400004120200107240c0510354050071024050f00c1d035075641c80c2c078130800821244062b01a482803d80200f481034240e5070581045400030310080706c0b1415105603e4100758807014802d98402151100000c03c42d408030b0098003958000ca80018003072a16040040c14284007c04050210034200b0666240d82d54201c00d51f01079450344d0400107025504d48000c608103403030702d4807045000e2048460350651001d40b0b8006510421083ea00c0d5080c00c00c82c50401420b4600030b0100425035004100c11960302c1c103080f504e404581840d654081030543d06180440c1c03140d8001c1e041900c058440800510480c2020820710004100a548051034140252a50925404040d110208001c0b0001d84151583c0c420001d072005008408108051001092900f0055100301c03d02002800d07050051601d0131a0544180e901c070b00e8010780604083c0e440c0c0660305000b000c100680da548840e080c441100c1c1074440e00700400c0c103c48030360010500b6401d1200001028212104101c0380017010b03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 854541402 1250 854540152 854540171
    0x106331112070f0f2405040c0e0709031e03030e030f03061207080105010e090615030c0d1a010b0c1209030a02101709010501210b011a07060504050a02090109 69
    0x500c03294050300c151080b80c0b41d10301850100354610032044041c0403003078402c4d516420f00c01110f403400d0502c102a144130a03100c02120350107040e0782e011200038004e426030a000f001060b10f004195030b44800c1c1c601c0c00c8041d0380d46903035034010000d6000880e10f0b180d4480700c030142c08068242c41000300305d803d01030046003031070449210003031103100040607140280d50304014080402d0003000b5190152074550028400c0b582c40340c10000021404440014607072140c0804200c03552810025904400c3c00a00985500c140132000d02074147e604000c122052000e100110314804001548640640880344806644601030b0001d18074002c0001a00d00403d40c04001002096a00148040c0800e9050703c41021040780c1250076aa10140440604d200c0e450b84403c21814071010344c041d03810380b120042e103804040c400d0500b0310840402100010084d000d038000501051100000318465810003042c1280340540c1d0355203103026103100b60b8040700c3ca03038029a41b80e411854840b500d64058091400d08110310b0f8403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 854542652 1250 854541402 854541437
    0x20d0606050f0d0b1503070c330b13110711120a110607060516120c02030f070606080307050c010e04020705030d0b0301060f14030d03111b010633 64
    0x80818206071190780d035100c2082615a100e002c61646a000c0c181506c85ca0000009006042211401c40310461941516900b808620303904030700d82090500f19003030030328000c8001c00c0101050006076600c40c101c40320500010115000b036604000720700e2400b64984101c2c0c50191348250281c40018440d2541c041011030a03100001d0360941e80e50044c40ca241f504800e034002c100540314529010b01300c0d5040074100500d0084105140254181340d94540c12410310b100c1800e41101c203222905e400607041042400e402c2d02d0303a9009400801e00801000414559400445195a00c800001c842941103505400c400e581c1140d071524411070251411361501c0c5156035508c0e107a12a00a01b948491703038400d554251910300f544400c0192140480c500542c9441d0f5414440b400c80441d8a2442481076825800e14944680505520304a40c0c01c820340c2001c002e140540011001c0350200c2107190343c1e407140040c1c0d04000030081101102412010a00e60240d8240084002035451500082c054a10714200a80d00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 854543902 1250 854542652 854542657
    0x709090807062004030524100e040203031605060a0c0314060105030a090206041701050a02043c0f031103070e0601030216080403030e030d030e0d05030702150109020d0606050f 77
    0xd5200300001000c201403e0107040801a000300b07651401400314001c01000300010b40c94455a505020200c21010b401500d440030485c01c4403500002ca007403001c10440700b802c0409094100384010305980c107155903030b100710f00e0520941c002501d0a0b40b0140500c10b48000500c2250702044241c80c1c1403003440e12031032542989040c00780c0424100040000086c495000d944d200f21041c5a008007050380c0d035540e44140c1120b078100440d800f80346500c0d040100329031042510031034040741d07400713011000004401c0d03074642d41010701640300c02d01000c00040806104030000300c90202500c0006941030106045040403043c02c48021005e9020f58840c55042c4140080c0307988290348180c1c00d207401360b41c0703036000c542d40c0c132144441030300040416201183c01310416400006582d4004416400c841d0400b10001d822419203000034003001b482d401010207044454072820003941e01400341e004a0b00f0500031035495052a6100f43d101440041e40420006a141c100f0700a880040000d0724001c2d007081a01c1a00d85032a1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 854545152 1250 854543902 854543917
    0x180103050304300c06021605030604030c14010c0306140315150406050418020405091c03021602032410050105090d051c030209131107030e3007090908 66
    0x2480c0c0b4019021405500300c000041e500a640343e01c00f081c00c89840c002ca2021542d008240c0580a05107a07402c0c00007040254608950001b0300804050b05c07152803e442d4160b03264410f0b80c0303403030044c40c0b5107413454824010200701030901d0790009006072821140000f1070b840b04541911079000704002e683d00300a004c41241d00440603408010204000c00002001410243d01440d089030500c000c0344001c840c085c0e1078030340090082d00e090100c3e68501442988801e103c00c494409041c16200c4542014070a0340070f007205503020600810401165000a071600040c030911640001c40c02c0d14035000c0d005c0d14100140c000f0441100c5813a11414900040c0c8940540482180240840030465052103010030030000c449100300c000b502c1c94204c1c2c040040c0a9846203c000d40500d07000f008050600e20540f04400035643c03161034503410490942c1d001c0b41c0300204460010343c07120110103001e080e070307401055400314484250800c08007461708041c040d040c68110360222007a5031600c103845020500d90802ca8060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 854546402 1250 854545152 854545169
    0x61b07020d020f0a12060501090b060c210417010c141908040f06110a0219080a030203130503030c090111010509060f09011b1d1e0d0507120b0105180103050304 70
    0x9140d4043c0414402c481903071040e09045006941c00081c08001d5110a068498440d4280014028002403001603c01c01600f61019844144c240817010b0b101c0f01e1064540b081c0140e4103203050364401c8040389200384c01102c01c1440c0d41d528018040300b0f8008000da017076411038205260611007122003000030050720f84454420300078903000003000c001e64100e5501000c0c5e4031910800c030000601c82d0310304ca44e4102e83e0340358005d0321a40314100325040884070302a120030740c804400c0307150003012401100a0f404c042c00240044920003c100c0010704103102651190620501d0301d902d0380090300005120505408080110381d1524040c0020030302c0106841c0e61007680480301c107080d0f8aa40068500401d0301e41007c0c2c5070b1542203160503c1e62175125400150070440c2d142000c04c00311200f002c0103405145a4002141441001911a0a81810384203c0b6601d80a4800c1e0307203840d540d65008075820165902c0031640702c03420500600140c40c01903610b014103100d042a2418a43c19581c520341c1d284124040d1406 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 854547652 1250 854546402 854546419
    0x121c0f14161106010f0e0703050c0306150c0a03030b04110f1602270a05070f0e1c0b0406020705061317130503030703231813090212061b07020d02 64
    0x10311a00500144070001542c008031040c03582e45092003480ba542d180110301c45081102e010031070f8948a070140f2406010b1500f001859030320f80300b0421641070703a02422024114024040716240a400f800801c4e041030103500c0201c2c8000c0c1190810040310400080c00d50a038105104000380004124280c134601074032040042401c500740e000149404803406070710341c000d440f142d5000c001c03a1076483e021400380440f07290500c000c1d01d03a103030280c89803607001c408000042c8000c04900464a800035071341a01c11a07401d8041c02e40000c1f80c95501b40e03264111800d40e0740c0d503000178201c82000350421046a0000b25414013040c403103480d94943c5010003003039500c010f1218001c240c0308810521980c5041c01000010201c90307036410702e4540075040601c21451030300350b12520810720442901c4001220704081c0c0c14260440c2041c581401c100006007280c0b40c03a40110f941d840901e00603210003001080017584030b0020440ca00e08212070b22140e0004101044408805104440050f100c030001c0c2d040d290b40c1150402c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 854548902 1250 854547652 854547691
    0x26030d020717041706061f180803121b090a060c020f06071101180513050405160816210605061206130b1f06050c121c0f14 54
    0xb00340c500e02c4410a481c9800014000840e031000d0b4802c0d0502c0307000031080e90320503035802040000a0007000702e0b074015064520782c600400f520882d0041c50607468000380a50b1903889098803451600440140c1086018550601000c1c0302d102030700d61f04c00d64080c08041d1404585c0300129000381224400d01090047c82c484003421940c0c1e45c10300701c2a401d000f42216807103030317041c1c203107420585001281e190100f003522117040c00000a9220300410f540000d0500d01484541c26400001004028000d0f2680c0c0105182a0b03202c0c025600300301d00030712610000340089541c00401f210500f41c2640005030100c1c4094080138200e1451440300c510503000355000034142e0310310b030200e1103070240c0c84900c036014017070070003006035034036258040005203401003000381181da41e5014080710541121080621007040d210b030802006104078010300c05a1a080c06440750020000302e520801e40101301e10340803201d10148142e030403c110344a450459100f010040c00620710701811054a050081c01400c9040400650315 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 854550152 1250 854548902 854548913
    0x60901091e181103070f1206060506160201031a0603070c050109140303100f05030c0f01111e07080321070c080c1c02031801110106180209010906140a031503120926030d0207 76
    0x10b900401c005081c81341c3c3e4450104400f46109233445c1d08901180c50504094040d164512400842c484060b060510315295176409a4000313081286c100d48c00d64980c3d603404c0010318040001c8041c107080100031501d0703040c5030201b4850b901d100e0708a400840b0128004120641e400101e02c0500981a031741c0b04154121080122921415201c50b00c503a44540e20220480d428040e017081d002600d20410b603854103441c0d0340480c1d1a48074081078034030190030302e10314111085440f5801c65007000d200d0410078110016a65113a41a805c94000e00882e600300c1040384081142e04681d13072245403058400f942c076007030f002c040d4042d0580751155801d0401c0486510250513003c00d41c0b018014020b214038000d0401d01c0414100041d41c000800d01e030005445c5000007540d40c0c040c03503a0141c20580461500d041c0740d40c0c54021802052600c09011a00892901c000085120007101c2d020800041d550041064105403094076440254080307a076850517204d0022044400c00f00594110300700300300f0301580d29035050529 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 854551402 1250 854550152 854550161
    0x70c030213061e080c010c080403020603060a03141b0a0b03040b0702122803020f03220b1f0b03090312060d120f020c040203060901091e181103070f1206 67
    0x6045a140b4110243c00240c04406a003c44840d0003c44a20a100310011101540d10b180021302c0b050051009100615280014580c8030501074203c1140139541e40300c400036a00d0b01120201c03960001d01d00e40300000d0b480d981d11405402c017500c5000350503140004001241c40000d0000c2c2c60b0740600c038003180f03049209100101001800480e03064550315411040404070401c001c000d503c220744041d800202900034000d40d140d501104822a0540d034807503e02c03142d240e00100c0c1080c03660380400740407000512515101e6015211301c940684503084c40340008a0182160f170000d4515000c02d10800215000000440320f107481d0660046400d9110340c00800d4400d540d10200400740d00c4803116910401d42e100c9030f692403060a40c1d0031a481c035403c80050000b00d10081d14a42d4003c1da0190041c040300056801181c01400ca410b0f06146a031010050301045030307805503216080211103a186401d102440800810454007200070b000510f1400d14110280041445001002d109000ca510184465540b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 854552652 1250 854551402 854551409
    0xf0b010c060c032408011d0d051e07060e0c031c260711060c0405010f0804020d0c08031803120306010e0a03051b04060b07200f041b0f05070c03021306 66
    0x2d064800b109407003003103901c4440340141600341d0718180c00040b54407c1c100d000c06c0760003103120141083d80ba00792000c170707401d51000f142001c2d100e00e032151482007580c1000051918034040c0a00088010b210b02840b070a003c411035020b8400d600100014180d2080404540190702c0c90f030a12444100c40306141c0358500c098542c143c410000e00400300403600340c000a54400034078001d0141c032403c1d80c3e10000d410b0940908d0045070300150b503c0c0c0719610842c0c0076a2040703800c00d000420840c00c4c080c0c01c0e620311240380059003094006d6000170509422001645020402c218021800342c00d5502d02c00740d030b1072014003004004604000b44a1480740b40d90320354408801c0515003201c181c0b6601c0220072070b420710039035111981e00e000c7c5140c41e1000501e0866a800c3e42c9540c0da000c4e449402120758002c0d886454480c000c106503000034003510314101c0d0741d560300c01c501481702c19a200e8840c0d040f102e140503040c021034481040034010200494000143d0030142401920742c11103800c444814040c1220300100b24582 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 854553902 1250 854552652 854552681
    0x3111309180b0414011506020706080705121005010e0d1703150d0803060108072d030b0406091b0503040b1b16050c090612070605090f0a15030f0b010c060c03 69
    0x90503c01405407035004c1d400716141e004000d0050345140c1e018280c151015201c0c8200580181206124503407282c0300d402d40100032454981c0c10801c03e07018201400409990003454880c0e2000e0410095805c444541000f00b01110a103803200c4280e1a40c0006142c10224401c0410000000641e01c40d1004c68a0130221400740c14884400e026280081e01c0758425944140810301c4800052101441181040c1c02d0611000c9000307509690380304c446501d0b04004000c4003c3c50f48401c1c0015050b1158441ca4004240c0480042200040c01d9001d0200f0b05400003071b581007000c200700b04000b099030600195000300310100042030300c001c0d864502a550041100181300c1c072440324500b409000300000c509410000840340c0c079041d900d40381c00b0040c61200400840742e2a402c54042009040d0244014024000d005040c2002c1c440311240003a42840c001c2d003110300400260f40413000107607810b00c80c141c0352071180542002403828020010309503184800009000c161141644002144660040e6140306001d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 854555152 1250 854553902 854553923
    0x30e030717030f150d020603040501110d09030305010801060b070b0717010f05030d02010e0d031a0301060f0824010b07061401030501052409010b09011412070311130918 74
    0xa460801030ba1040c0e8000d441050b9110108015001c0c02c1c4c641c2044903401494480e1103d001d0b030903c005c0e600300501c00d4407295a41c42e681044210407074024a10f00d89400310000c0c02d40d9013883c002d000c40703c060b000500160b24104050254121080c102d81900b82c11403000760442da030744001141c94510140705c9000c03036a0301e10300014050200080141c2528000c4043d102100c1816008074202c0315200c44c04c02c00c1c3c2d8040840c58242c0ba0003039200e04940380350001001c900c14824800709007902c216a10140340344d049801c00b0031580405002a00310300c0c0c11010000110346003490001c02c20303503043c0a0f2860406000414a0411925074005400c0008a2070300a42c0ca40e564144140240000c5a200b080a05c960061580f50881d030006841200f10042c0b5050303c2d40d00f403054095223030304540c417a00e051110300300302c034118074500301e016060740a1894890051446c20060040940705110814025408103011821088035804050300981d10040b030001603132100700b0340341120f001400101030480d0644 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 854556402 1250 854555152 854555183
    0x30c0d0c08011503060b040209091906030203190b010b1201060e0a0302130606090b070807080d1107050703031403190b130c0c110907140304050c180603060a06080d030e0307 76
    0x640f90710104580c0507940c10882c1d1902003040c80264401c06420550203006000020764600022aa5400b030490070304000601644a5001c89d152907415441d03c20a40c140800400070007269074441c502500b00a81e030301d8140b004c1440c0310040c001040c000c481c00e01c0200880f0074003a850f1001d410006540041c1240401c8500300035102c0180042e000f20340000e800d030040440c850300c110003103880090703125000920700a525225105250004d80300d41c48a1502c800c85950508112000340c05100e0040d0040c01444d40b0b03514000e40140760074516450980001e208000b0740d00c4841106c00b034002c4181c040172030b0500008000400c030803107006140510314600304040003015805022174001c0c1c3d00c142c58a84002c005141002011442160913400082c0880c6c800b1960001e004051a0441e1203081103e0010028000181030140e0603440b981c565202c9804000041c0380810285030005014182005000e0400010a45404040024600f410b8441168001c105000c000716039402c2e400c01035843d000da00303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 854557652 1250 854556402 854556431
    0xe10080406200316020f0705130209061b010b0405040213090c0305060c1e1612090305070b07110a062f01050703090311060f0103150e06090f0d0c02030c0d0c0801 71
    0x1690524600c2007885480c59005000007901d107038007120031008001140c5020704010004274000a68903042c0e800340a03000c1161905d102800c40b81c100034440c40011000201050300b140c40485010707100310f08080a0001584a0007030040c2ea0024455001c2000340c414100010040c0c070580c801070191103820b007044000080200984890108002c002c00c50f40c01081c4140c1040c000c00340d10300c1c011044d0740b422400040200c0744080c0600941d04020b50b540f681c3ea2521401c0810f40d91000650500000e042e6040102d000c006010250045071050314050800c000205845203494074215a081c040035040242d482d10f01c4c0800c64400400020b000340d00d04408014064642c1034011004604255080c11800d000458103a00c0752009082d5650340380c1c0b86446013022a8849020041c100b40e03284842402c0d004180f1180c0c1c4103510b00d0009040342c880c00c50000749409840f00d032082c1045000340300d1600503079000c81c14120710401280e02e0600000982868030b504440c40d40070b074900358070b0701501160488 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 854558902 1250 854557652 854557657
    0x51809030714030a140403050d050919031a24010e04020f0c0a050f0a030f140d05100e011e0e060f120a050d030203130219260d0e1008040620 62
    0x20545e5100c8141041c200403020742401103020050203508040000c0d001544188003a00141d42d004280720f00c003903810b007090500c948158000b50b60000d4406401c018066030030090a4100060317441c107140c0110403010350b82814824192443c104407050f0303000d4000d0f944035016101c110090503022961502c00074001d6a030751259107002c4800e40280d170f800401d46a4003041c90b01d000d9070941c40e400150680210121513900e603126083c02000c10522442c1a41025881658821400303000403c0b085418160100c0c000ea4059019140040a801000001d10034a402280407204881050314064543c01c0004a400003d070f1211900202d002c00300c00c03210340b400248042c4890081084c1d4509242c0074408509a100840310f06081135042007807100107040c098550280e500008400500302c503100e80c4c0d001d81c01c48100e80d01543e42101700b01842107500f0280504c1040450b1130805d0f180f1302c000034001c5010b0302001351405c0240640840010f0500c501a0021a07000071700c44124000342ca260928030f4644e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 854560152 1250 854558902 854558917
    0xc040506040f0e102a031509060b0a020f011116060608031908090d0804140f16030309080d1b0813060804050d0804020f1e0301061d0f0105180903071403 67
    0x40c1c3c01c00f8102a841c091040c0d62141c40c802d0111190310506801e02c056002c7d010080c956030525003403200000c0d0011451003010040e205100865680740d07030290300286090031104882d031082c0d140030030101c98481d0320303801c0310042d40009085100300407a40c24410014200e40c0c2c004203140c000002c0c59101c0040340741c00c03e410810545c84400f00d9496480049030769511aa5403003012030101004a404150a07000c4c060070315504404403040501051100b90a2800081c01802c070f015810b8800c0c4209500400030101800c2824000d18410f150403400805401000e40c0c030b1005140040030240c1807064000032550355400702c690000c02281d42e210001d00e0404c00b213600399181d0052113800070900c0d21400c002030240303400409104500249800300003808442402d9882043c101703840c1c0079842c2e102800b4420040400d5a24002c0346010b880900368140d00044c0800c00e80c4075a00014445039a0703220600460182c80e560b1042d5035900d041a040c0346105415003d040704205e0844041034980000003400b24 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 854561402 1250 854560152 854560183
    0x3020d060b0c100b0d0308092b090b0708160f051506011e120e01021e0c01110a1202132106060b0a08041509170307030c09080c040506040f0e 62
    0x4441090b04080c11184d00708101076200313000605400c0424458981250008d02c0001a540c03000140c41d83c20106015052250f84021403281d08888100d03004540100181160b0262078604206591070300910711601000142c030821003c0000c052000d1914a2a4029071040031104d050352110401003110100f11003403070004801103c005540211008441c14444a03504e85501300d00419260703001030494188004010740d424040c3e4041c02050740c0c102182e00c43c0c6001516560842080c0715400d5482544690701c103417508010740030101c4d900540240425510520040c0c0381e80d104044c1008610b02a4400322145a01303d001c103500d00018000c05c071100f4441c0b50708024046c2d079401545064018500c0ca403001c1440900060040307810202030040500e0030000005402140d50360320344035550800d2101c50310040100402c42055007500c00c4034411809424042c500b940b0301404160784001e101e509501507501e810101d1116141c5412480c0001c0040000303101c001c00141646595481c02c942280a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 854562652 1250 854561402 854561413
    0xe06010b0415030f0b0d03030603051213060c150e010509010e0c06071403070218090f010b100f03110a0302091309380f01030515091c03020d060b0c 65
    0xc803039490808940840b05aaa1102001000e40768140c004140c00c414001520341c661190404940e034400c1c02c0301c0002c2c4240c40008038a411420080e1401400b29900e181c2000f0411541c508080c0603a07101080300c1091501402600d042c4c6403c00c00450000b02d080d201d60b041002e0810814010341140b0701c00d14200c00208154042d5000d8140c1d543c007160071980c0c010404102120214901001c00d81d4131940c0c1c002101d2420805902142030015840044c101c0f548101c003e1045000080c018682c00461550092088000700c00008849001c8000641e06002c00d510030741b8109030090300082c88801001c5070035a02d408015034040c2c0070f0341c449041030380f00d01501c03401c15803582e465214941c0d80d90740202c0e10003c80030300d2200c02204511b90b81c0e600f591000380c8003c0311040880e01c0036114803a540d07e010426642d40765151407450a0340d6104a000c070b2500301c00801000c91800180311032581001c03000d40c030460f164000c040c0c00a205007040544c2982c14181c01080103d05400180302041e41c0808840c2d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 854563902 1250 854562652 854562659
    0x405011508280b0f1005070b09010203040206040603050403122a02061603020a1701030c0f0503061b030703060803031f050111030f03061315050f01020d08012105100e0601 75
    0x5440c081400c400c880e041c0c4040707000b10800c404503070000810b8100030b8143e1401c15014070024910f45815203407200043c3c00000c40000304a440030300c10303421402800003942142000c2d40002d0f142c0c01503000306810151ba80000a0501d841001c1c074104050304624100100300b0300040c0c81c03114ad0210402c2101c50140011000300c490710008001d4440c82c80c41c51102000f0640c044210065800030005004001b4103440c85d0b201116041c0701d140c0210301c1402c1c610b800c1440c00380c418183c1c018070340c0100d129402403010842c14940d091400c000384000b180e03805540759681e81e020380040c400c0350002d2405120100821145010000902c0b500103c0d40781c40c5030545940b60011501001100b0480031140c209205101141c02c07890044c6802c0031008215584655010060394200c82c00078102c2c100c19824050100064140022001301954007807000d030100303403a580c2c80a017400742e06201c1c9a0f4803128011005c44554070000050f5181584001603a102c020568040f8020700364210705112680160710000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 854565152 1250 854563902 854563921
    0x1120b3703170901052110170d0e041d01020c06011205031912050405031308060c220308030408030403030b0d020915040e101e050f1b07020405011508 66
    0x84a0b07000020360850603401c02d1000890304445002c60600c9401c3c0000c0745001802080c0500310944d00202031040d10345100c0701d843c404400da001021540d800710402d1152200403c9485400c0664100f00031071300c0728040403400400b2007050205180f4134101f004056002d0640090529034240d400b03e680301e0b40c03110b0140501450360b14001780b0b03507072040040c042200b0066520302c030030030700d03900700081c010213a0b1580d00c0c00e480c41110704076020f410000c2c07a10321086054080c0d40282400748000c0400d46840e90708062188103407441c02c80102c95094907018404004054600510340c002e144d1912800c0c039180c030b260550000c2e982100440c0c00c08411910307504190b589043d0490b001000c22a403502c400350b03000d41868411480c2500681c0740d81c2002008282048140d40c000742005002925448103104007902801d02c50700d6090107810030003800b0185101c4000950041e6000e01c07030309146841445079032024412014000c0d00682070000004040b5a500c5540b02900d0b03168503043c01980e140d5841 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 854566402 1250 854565152 854565259
    0x7050411180d0303090c062c0a050f03190609121e08090c1009180905151003062d0212220624051e01120b 47
    0x49401c80d28604055181070400141c0382400790400107602c000546460505032410342281012422242d8499807165050038205540245090003a00031050803001401c0b034401c61007002d1080c400e51078800c11507030707003841106280c0d400804103020921079850004064400c034141540ca40030034148442c0201e000321905c02d4040c3e4040100c94040344010025166064040d003c180c2ca442610030307420701510380d450384014141c9251940c140480c40c00300c8034402c01c410002003860350713070805440100080000410100c0704074a0b4440311113503650208030340130301c40aa500250029080500d4040c460040340b456070355030349100d0f0840d03407810340000b0701c4c9045c0e21480c40089080741102c000a0380400c0c07079002001140304082040340c00010246c0312101030b685052a03400c0e002001403c5c244c6c2858401c440c0c00000d00c4107540c4800148655031311089880061400f040c1408044045014a600158001811802c004002694008007010b403001d11115030500d5010781c07060303270b8400803090018290 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 854567652 1250 854566402 854566417
    0xf0f05180112241e09021c14030a18060302071109040206040521010606171501051c0b10140a05090f030624060f220e0907050411 57
    0x240410542d28008125541d03903010407003610214668800703162984801c081d001c140c0300302014041121103810400c40b0062104054140c1c0851070200708a005071220100d640014050b0381080c40300401c03a0070003407107940010810800f1070000080504003940c1184692b10401c01d4204100b074050384404003070f022407007092000380c005042c215042d070152400c030310303440e5200e44007400c2e040c1090b5441c0045013000b10b0021501032980352107410591408024403070503006103400d140089040c500b5038280744150001805414141602c0040107280782d028500305c8903000701020500c00d80b4980740300780000070135400c046544207801c0140c1480c11a40714050340b16415404018042c0303020b180f04020782c0d89034407200c401a002556005402190798042c084503100e4a442c28840c41e0a140a0031486403120307a4070b00c1d10784188028000c0007125400c91081d1104610401440c1402500344151442c04aa696211449049500042003803000010494804903001030314144031959400d000046140100c0780d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 854568902 1250 854567652 854567689
    0x1224061e08060123190603090203060c0f160309030b1006020d0c02061c0b0406030f0311011104091a0a080c0a0b040b03071b140c0f0f010206060112150f0f05 69
    0x160102c45909071306101e00e0b40070800038203800b00341d45505006805d4480c03691009000c07a41d100c1140b0203505003805055803001b01260520325001c80c2210b0801c1c580070b03444103a00642030007a04c41c0c08050040210401440d0400d103054201c0c036001e0440d0300d0040c09405031342c0042c015010000032240c02150180c00c9030b6030080c02e00d81003640880500a140c242560150f82d815260a8121990b85440c40b48c90042c5014468030003000c9000d041c05008490300505980c4a81e1504424154094807201a1002c1d950143d6021901c4500b404401c200318004c01a041da010043d0500012000000250302e951101e0a5960f50081c0b03965507a0428180a82d1080111500b01003000681d8a44100b141509402e040b020760013030766400307407101c9886024080c1e2003c1141c5c400180d0b0a210300c5c0a10a10b0700002003140e041d52420201c1d40000d480c2c0501810482c14402c0200d10407900e5002904415490301a80ca114143c055032001c000f1081c124031311400d00039054041d00810f142c205904940a94507880 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 854570152 1250 854568902 854568929
    0x16110a0f14011d0a0227010306050711060a09020f0a0303170c1605031c020c03161e051e0601061b060609050703090c050a1224061e080601 61
    0x1600c40c04110811070014000555032400b0b07610b601c411030810700c000031111500510203d10745105104c2400e41400c141d0034200f0410000203288150182c986043d01e40c1300002040588400c0c03030690b080510b0726410381090160301c3c100440c04d2881c0c2e10034082030b0300884d100c0c2c1c41aa91141844a41c4080f4040980001c2d0005214081800d2101a841d0004802c40d1001c1c5802000c10480b900c14407000400c586a0b00005080d03000c120038102c0c203001d1359802c25811031812a030584115070300c0c841c2030442174070410f11210802c14007a0304032000181001700480e03c1e24101721441d195860b10409d0742404203100590000000300900000c1c0c0b00d060b075503651039032002802c072000b5610004198035070807103145071585070110310b2070f900b0f0003034034002c0c01642c0340401c01e02814901700384d00c81d880e500f20501428403244104851404003004440003a00802004220740a100d28080300c040749044a0b054181070060014402c3c4200000c00c4004481e102660a40d54a64280c1511808203200b880c0c81c40c0000f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 854571402 1250 854570152 854570183
    0x90c06120c030e0a0602130b0301150801270b190f0f1202030d080415020d0f05070c21030b030105040503040806070201020901020d051612020d0f0813062316110a 71
    0x503070050450032211f21104420955a50f40103025a10980212684c01d0b01e400c00590640d400c03803041805810601c6000900d519050141301c2901703c9000d504580c56142d010000c169103451000b560025800c0d550703111600d84503078180056201520400e1030342001c001000408515072403242d065545d0080c058400307212940000c840c2988040e1060b43c1804c0d203c4034022030703030b08244014500060194400f08115075140016422030342c00030254001d1102246078040081c408444681c08807030351002c0c00742c141d40385160132001404a40d1009070598a4a030921040c010000041c00c110b41241c804c5504c0c1d56940a4124240c1c0902a0214050303480540f0311000039024001a050214000703212510045450321111040350441c01079001507000320003401c2c50170340d00c040c2076800680c040c20080c680d810f114525034180c00180c04003510a0b56100b41b040c5400940d00d013420082c3d49400b02c1c2d6252410000b150601d4051491441d00100340e03200651031a80c0b0700403034141c5249422500e20405a503c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 854572652 1250 854571402 854571413
    0x120a0b04060c11010e060f0708060114030709032316080c0d080d050f0709081212130b010306020a0e0d081204081608070501060e09190303090c06120c030e0a 69
    0x402000100780f1185109420406909203d1015021200c1c8020840c0d810b00285054450501402e0300042141400410940382d030860091030708091820032041d40ca54a0240844a400058000801041c0b80050910544440c45448a03190b4036400c01d40d10320441881d0560a03110b920f100e54140d5412111076510503142954404d8000d900501080703241c9050030114400b100c40032038202c1c20326074041382803003940c1c0d52040c0000b000e08464401031035400b0b180100308c01140190122140002c4021001840b280d88141032034101941c0080071140c103503104e241540c0a034210030107400014008a03403505aa1901640c02c145190300401d60038580041004d928000700c5000380103581101040080e104281030049440b48514000c4d1000c07502c9108518009094894603406640c1c2482c50300705000c44c44402041c50b100031060b1580800390601540f030150041c10b00243d0243c54405022000540c49802c0f800000828010386c208118010700d04c00300394120b8a83e5141d0030075961105840750f00150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 854573902 1250 854572652 854572661
    0xc02150618190609020309032b020a050307180e010e1b04060905120c010e0d050a1703041e0b0705130305010903021f0519091e030e120a0b0406 63
    0x10003400d481c01c04800c8603440070561100399a2822007000b1003803000182c00c1c0510903840075060700300c010341c55400c014081c02e540e0300410304043d08140084820b1590112154501040000c180e941591141114040034207640c00403609500407400e4285a205034048040070b02050720042d0800c40c0c500d03401c000d001185210010440949041d40b6815050003042d03c2010f40b009044590365454030500b800700344003250490348100c02e0341381c0c01190b440c6038681e00300c40300d40e00904050341c1c44840c120f460300b4403526200901401414510441c0da10285122110009520030341c00b5007101c040c18080c00303550b0307070703202c0300c411005441284060049009a41718400500580400c04480000d1303a841c1c0d15031900711200c0c1141140568400f50f180550003800143d030329400405040c040000b40740442c1100c0c841d240d00104c01190fa0342d90001a002c00081d48001d00109824115601c910303207503881c01410003060b81c6001445114400e1499140708800620342140365400391240748541c880d1796480c1c000c0c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 854575152 1250 854573902 854573911
    0x21503090d031109030f03040f0609080307060209060d0f090c0e07080606090d0b100f120503071b17070306050c0f0f07020a050303070c09061505070308070323090d030c0215 76
    0x2041003004130060b540c20014808a020a400030b140d6403441e081d149008500c80342c0c000c0040c048416420003140502109603810103400c0b070409640c0f0f0442d240050079501c980c01c070054041e85424041142c43c44142e01c0340034514419040d0a444c2500d4050701000c5140031a030401c0003540a8000a02600308074001c1c281c1c00310054110a127460f055070707981c0e01d594012510340e061440c03a0002040041e030042c20040043c204050300541000060f1189a1684600300c0c02a10741c0240c405005602030398003800400900c40550013220541c0041403c5880b00ca251000b6511542400d0102d8021001481194590407280f09418504200b601060380d454006a0090b640b007040700100088a1b2000c1c8024000c985c404e25801c0820b0b41400340b64000c58000d5040300c18500e01c4107400c20351868002048500860709410208001da558801c01c0340a840c00b040402d22100c412026020014070665125000e4150481a40e0007a280d02c00e044003207807005622a801603002851782884200c2c54960650032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 854576402 1250 854575152 854575181
    0x1b030b21100e0105060310061a03220f031701140f131103040512030f06040902030705100e01110105060a062d20070501051917040609021503090d03 65
    0x24196859908044503124080385600742d44800c104002c0746011f1004250000301104204100f030300740503100714182240e190954040f0380003c0411203a400c0da16001641420549500c03c02081624001c4141c400c55182140400d140803480342108481e0380025041c1c03201007d0400006c907151003000342500d03a1041041d00100ca0010380c2090b03990030300136007404801c050143c96407818a481c10b80c1c9000607048864100503828000c1c0941c541c5c01e5051250000c0b401c95010425a40600009003000760071b600207980048203640c0b081419401100c00b41d8011001d0300c07024401102d600c00030b82691011030744070b80d00000407401400201c2c0540700800d84000c0203050005481c114801914485036080c54000100c2c0032248007640b50100d04047c61145402c1001030300c1003924000002c1c00500030641030340200d51900c401000064841c071404c60050042d11244011401d003070130500010154a18168055485404102000303094201144d016221b0440104054182104218024003048003480c0e030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 854577652 1250 854576402 854576413
    0x4200a0e011106010f06091a03010510050c0d0320071203020c15040813140112020f0d05040b040501050c070f03030c031e0e0c1014090d0b0a1b030b21 66
    0x104500c080048074084c0c0b17110107201d0022820600c5c0506000c481c1c1c0d000c0c0012410071004840880030950a07241121025200142c60000d4031406481d50701406c0000c402a00c40d003c2440e0006515821080c0454000c1a410414500d0048121003034410400050320000300a9550b0300810b05c654010414651024155100715100b4000c1c92083e103801d03507056845000c084ee070f44501e00a20810600204016150082e40511840029212285030b081807d489a4040707408050302c82c400080303c1d40e082080a040103146001d2401d6102c800c0c082d101942d056103842c002400b1101070348100c801c1c1c1c0d500128101c41250459600300c1c040e2100c0d0310000308040d164680c2a1400c1c2c039460300000095540e440c00320ba4609030b152603034500b5030014001840b0b6000c45440b50403298110860004c0c0c80380d800702680d903c03100700c0042110710329000001805910400300f0041006c3c016802908900900c104008102c0d000040440584100b0402554044e08130b08920088051542d51032070005860000d940 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 854578902 1250 854577652 854577677
    0x180105040f030606090b01090305061801110c0313050103050705070b1302131b03061203110309030d1e0206010e0112050a12091403071a0d06090f060504200a0e01 71
    0x4910075441d401180e0742e03a152907090220741c4c224001d02001800a203881d02003a443d584560780c0da01d070054800718510f4003c0178200c05c0c40130207401c85a05101c545100381d85e074080260a00f41ea076404031500106800207070708041903943c07285c00782901600c40c0380c2e035007418804a0380b50340d42d0780000908000f1180f540841c41800603110803089441c24034028200080407000759194004850a041000d010146090800e02410f80d00c0d0500c0321110750980f520501c5e0a4a000c402e51843c415000c100341d16218103103844503141e6102000c00e0701e08101c0404615004440c1a040c0d039284002c0c040c41380c44030030380c00041c400d01d8680003c0088060140c4201c492124403038a0301604007070142402c00008012100920410010142080d0a038200794002c0051034606460901c94503104800c128900100180485180b1000c0e00507001400044070100308a8602e0b062500090005201e00d41c0124113013040e04405600c1098410200d0706000003080c41e0405d07a110468521104038441d5052214184600 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 854580152 1250 854578902 854578919
    0x10050c010c051b0106030c06030b0409020a0f050a0f060507021302160303060f08060c2505030408100507210e010213030812011703040509060a03140d0e030a030518010504 75
    0xc03011481e1122503a0b05022000f0502d50500640c1e50b100c0f07a03041c100e0410014402100013800c4615906d8001040044c0301c00080203040c0a4201a40c4600d54100229054a50351611000c59104407298140c0554402d1000002c921074030800021403030a001c00405420405035a01c03070039808130401440c000b20314000c02c50105807280154006942e0350020301101304c401000784007410040000749076624114141c00260300c0340c0780f0a600140030039190340c941c003825448140c41403640102580d440c2e6444081c00c560380c040000d10404503070300701400325084e40d009100080000707060050081001905080e44005441c0c0d070540d40c0300303079903080007868010103d41c01d0707001c00b8500c2030400365a03a602c800484e1070881c1d07042c4c1024102d04c6000440c03940c1e420f030001c201c5044860070b032403c009650300e65002a848103120f51029122900014110105801c00304024200074169115120850365120034941c1d00c184000b0011301180c405c01211000321158014010000e00524140d407400d6158040d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 854581402 1250 854580152 854580161
    0x40c0311041b021c0201060e0a1503020a060e0901050d052e150305011104050d110a0909050c01030608030901120b06070c06020f0106140a030308181b0307080703050c10050c01 77
    0x10a001a00b00c8502c04080324a80c401002c1001c4c200d1009115050428090510b11203000e0a040740c40c80d80c40e05444079410011280d00c0c020368004223003000d500d5985001816180030300561a204000c103100205075840d01d48050f10f4a150008018018088070606a00380401c46444000110001c3c045c405400b207600d000c0d5003800750b5012154201d2502e10f1030850b095541558010f911004248003e0005840320561422043d8000102d0401c00d48128049284549646c002a84803030505d4055814403c000990071f841860030381c0e08000c551741d070b002a6903ea004044155002801c03000040030f0303400180e0030120524400406e801d00e010301ca50354001c1048219031140d80582c02c0703505040301c000d00a100b2140103280346003004036480f4400740000c083c2045800010103024101021440c004510404030060810680c200c40440b81c0b910940480e07109001d0605100340300b007600118503ca0003160010890b0341c8200101040c01840040102a02c0000c83c01d0f030811606102c0b56950420074082d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 854582652 1250 854581402 854581451
    0x220f0f020d0b0c09120613121202181918020a090f0e0103050f03190507030516060615030b0913030c1514060609030a12111b010314040c031104 63
    0x41c0309070356049150512400c5c41903c0d45860707240d040300d0104005d0042d1540d602e01d51603070243c107118a410f11000c040d11041d09003400d40345c07900d00c0441c1c0d070028007549c07054115044004030380060500000c184d640d20f0710705950013030000c1001050100d0f46503400035000380c01001906e082c6002d583d40c48e0903a6601d440d0041d80401405905140100107100092100d0788506540d41c001e14a0114a81c091030154000b0007001408c01c400040c00106051103007007a960310000c511642400054541051806030400f4003e01821112282007991007e02034810250082c8002d4000140ea0baa02d400e0304054816581e010303001d22404480da6400038100f034180a1007424003800004070b004100300030145100c4d0051907180110010080890340c0c4d42e000074182483c90b440f00c00c400f8510f0390325800300c94110304000c4a505520607008402030204140b124400c09171806e076070412a001c0540c2440b01c4800b0300b62030140c002c03108582e06202080020741121921240a00040ba64100f945007160380e003002140b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 854583902 1250 854582652 854582671
    0x50306130212070e0a06050a080411040c020f0f031314040902060d09060501061b1502040f0b0304050606010c0b070c02010c0206120f010905160302031e010e220f0f020d0b 75
    0x4041003c01500500c0d04000300d8001e030761100d80c05003403a0002d00f440c4100c01d084005d00901d41c000404120886040c04500e500213030051181e40718800d0f001c4d6a43d8000380025070540100c00e50490011030020641d044a09207941d400d008902e00204601c5a13101400f0705908070791100d40c880d0260725000002c00c9505000b000020721114036042c03807001c80320107030455400c002980e01c281807203043c200c400000c0180c00185a81c0044c00c040c520710024481d9a2102c20305110494000401b42c0700100514030603401902541c000340d84440c01160800326542c00106440020404101c00030702ca904c510100e82d1041c10401c007490726035000520260081210899540040c1082007000c3e07003074078400c80c01464280010320031800d003855424803e074440d4110074200b56010001034003905124070034010004450103070340f10179615151083c420000844003100810216030900064902458450401c11703040116022140d1065907022804040c14000360303448160a030558010920320303003110b030060302c809 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 854585152 1250 854583902 854583937
    0xf060c0d050601080c0316020f1207060e07060504171204030b160e0f0415050402070c0510050702010c020105031815090f0a0b010509091618180f02010503061302 71
    0x108214415900c00502c241d040000500070700484610303a0040c2d030b82043c07015080c0b07490070078003007030882c075000c0114101d00407845112400d4000c044248010b200250040c9410300007800d03900b107000d83e200b841d849500b0014908020401c140c0d00c3c0351080398100a002000e451485c01c8984036604c5c0f5030403981050310321030540760500c15014260508494000105e09102e240c00c81038100040450704a001c01074010394540c0f110110f014000302034600600300040046440e49401c1c20103000380241d50040502800c0c070205000307080c80c00307282510301d044d81c165504070b50703240035500440340354101a040e46061070805042d0350a9000601501940301e02484a1140c0380c0b90482115181968881d290126030704105044004501c400c001d01341550300944121903a83c81c1e12842d2461f00b00c004107810503481f150400481c030003215200546281a46040038080301007190143d0841400d14140148a101c07003010580055016001459010000501d61805445080341d5002a139100400040d14900c0c00f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 854586402 1250 854585152 854585167
    0xf0909090c150e010c08030901090f0b04060c050c0303010308090d02040e100c030e15071e090518150409050102040f180501080609100207020a3303020901200f060c 72
    0x28124200344181991034070702491030941c2c001038207401c1c945030b01070200c0d000040010198002508881e400300c4e4089491412f4040c98141243c4a16003580c0407a00c0505080f0840002441481510003100107403028500c0d592035076503242c1080e404002c00c3d5410013050074000000d070b5a1031007100c13460104513000d044481030751000842100c40000c00380341490724043d6141c0b0040800a411031010b04000303400c4a2035129083c051b1049403e080d0320b90aa9440c1508600041d80d111560504641081d2010320000085030002c05800400f00d03601c800c0c1b0843d170840d051103450180c100786c14031070041c80014585500c030bd0494a5040c8950060540c07456028402c1001c0c48043c4242801030421001801440c141271003a0380e113900b4a040104217603078000c92600306566a09208070010b00004c0410000700008407510300041c2e440502c42d0962a450f00074602d0854024021910882e00581d80c000c4001140044035000200c040c4141e00c280c03146c01001c036510781040090302d010f01c0030003022545803c030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 854587652 1250 854586402 854586419
    0x7050a03030b06031003020d17040f0e010e04030f0815120f0f0f03030c07060f020301090903260610031526010c02070605030a020d0524040b0604060f0909090c 70
    0x21041614050981013041101416005005c041a41c0d4106d446c110907800c2410705181c4130701d0f107507101c1c03011400000b0009000d0144c0d01e400011204186420451680e07140c00307404654108440150100d103140d4030040d03a5505c501049940450707a910300c01c410742240c5010a01061031140480040d621204031011021300c10000a070300350000b8001001560003010714991a80800781c0101d800e076070041071707075010041c00d034010030301c403c9070200119203a6035100540c9001e00f000c102c0a90104109524070303c0c02485586608051546034040c0c07443c542c82c0c000038000b601254401c20010160f8400e501e003541107800712a10000e00a14005070f0016034014607803801e98401c3c620840c226890b0000701c075045500402d9400464000742459900d9036079260700b200c081d22502d29110385140c0751204114080628500d0354030400724021045075484442c1040c04110303001d0501103075008005204c01c1280d90710a404060f001e03006454015103103035a41d02000166a11280c040320a1401c44030306101d54139 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 854588902 1250 854587652 854587661
    0x20011e09170309060706110c01020a05040e060402030402031c14040801240f090902040b120709050109020705060c0703030e0607050c011b0509040f021e0c0f0703030212160807050a0303 81
    0x465040518a0f10b403600c40001c140b1302c40d000c0001c091940b07400801c121911018191604161201c1c001d66440030024802000780d407242c0a02c0c51500e011101103000350410b403080d0303881603501038001d15844400369600314028004400120400001c102c01320415491040600000e008110011654040240208600607503200100102041e01141040004607100d008001c564024500140d544518004180644143c021150b00014256a142400c0b040014a40f00325001441c04101d10f90322010a00280d00c1442006040d0741e011070082024034001031300078036807a0310906001443d0280c661069050044c02c840c144c0208001140000a6000038081c241c20071206101f840c14819122401030030300c0c0210031b009806903075661480030310641c46038101c4601e095403008040721021194404a1554040c800103681406064401c0d1505c0100103198000d40394540c001d44003000c2c40c00400c4105030060189006d4000d031400c0715031301041d507420081900b02e0240c809001101500e040240944 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 854590152 1250 854588902 854588939
    0x1d0a03060609140402090a11090402070302030901020f1b0f12060906160e010c080d0e03130302040b09100512030d090b07020d08060940031b20011e09 66
    0x1003a4004c000041c2d503a020485d45c02481c3c3c010016807100262105207850254201058003e4800902c44017416000000b034403140209900300c690841c01d100039680c072408040780803144c0c07008110702e2821500d0300f0450000c0d41c60000c0c104282c2c032111085010326040c4c00f84c6030024a40c00160510000c0220880c0024030080507080c103050300345403030000800034a000e4102800100000c01d2440510440b078026075149400701045030386800c02905070074147d18035444100e128500d010310802090400180c028410b801c040d00b400b918500e86820300040720382c950110301d8940010020042181943c0c400c1d00040d41c0500161009880c08034000303464000c08070101402d11252004101c003964a05400a512034000c0601001100c41405550350001150700034451441104040c0b41d0311240140034103461500030350300c841400042c64000b40305408401c1015143c1030654042c05501d00c0b007500c0e52040e620301072504440405034201241da000308201040c400184404030b0810200c00144001410b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 854591402 1250 854590152 854590181
    0x1f0c1805030726060106020d090f0e1302031212010311240903100608060a110333060d0f270b09010e06100e0f01030201020a031d0a03060609 62
    0x3400c010000703070342e95034034450801080708016040100240321040a1020344060003118100d5843c0c41c006900c40d800c0d0300040000403050800011860803038400b0f88120b42d08480107080503102c6410310341d1851035031082641c161280c02000c0c10545003500080c038651400e40c0e5903100d00d5046182c405a50f20090340013620561410022082e0984140c20060700c3e0654081080c0d034030380b440341c0440d080003884544410060b28107500000c0500000c06e1603442461000340400c03880b6244020440280800d07582c000b950030803400e80310342145000c0c2044031a024000840c442024203600099550385c8900c0a040c2407a841d4000860486581d00071008640c50448114500592200d02c070b90a40c03c003100301500000305d00b03000c03c20442d801c0d80021008075420301954a64580001d6182c81101203104032024002da85e4000307010329200040d00c0303040e03960503400384c842203110740c500b02ca8400c54101a800c0c1084043e500d21541d5450f080c0c10002544680c5000c20020b242c1b4491000311038520400814 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 854592652 1250 854591402 854591447
    0x16031b060b0a0b12190605060a23031e040c092405030c031f060314242205120c0706080606090a030f08040915080610081c021f0c 57
    0x1c1800c2c0c8080805d5000d82c3d050b40c2881050b00094440300607041c80c1e03100503042000050714030013031548040381c0141e0a10041c1800a0f200c0190a001c00c81e100440700c80c040100d1000800c0b49611101c0b00c40350700b140c000c01902141549031840d21040700d00a41405049103080d000030111440f1400840300140f508801604c01c03007103c078000c03075110804420781003d845503110004803200001e45c04200955000400c528090005e681000c1c0d0f00c01000c51403021803500c480d1600004440740c0342c5c076441120491b10700d02902c1e01035150b5950419085404840501031207625000d110720b020302421040b0500f20040c0007003480c01c271014244a10283c2850b0041d5410495111107484080700102120780c000c3c20100741c0d41160030000c5a038020b640104a060b402c1c06070b0303903003144080d04580c016140711b601555026190100522500282d40c8503404554001c4654454003443e80e4804104202650069415000410507d1404c1c0b448005641042e01e035180325014884d50b00c00d01c140b5080403c2402001e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 854593902 1250 854592652 854592667
    0x5070e06011e050d021c15030b16050403030807120c081905011406090102120f1201060302070201020c090a090b0123030601031a0411090405060403030e030f16031b060b0a0b 76
    0xb401880b42500000400707400061140c68020001d0036682190b1b1000c0081000c0c80320f208004620307003070511054401280110209014007449000203a030400192181e03843c2074030b540c1e0280c0e204400200350500f44030107014428440c03210b500846070112401d6071035414a141c25078400c404400241c0301c1d1803e03e840c040061001100b1101c021100000444000303481e10103d40040380b170a40603512920007200082a900382510f414005420034641c4444201e111340c1e2600c030101c0032805400310180c0140c0c4021050000e40c00c0c20640302d5040706411002084015680d22440c5140300d088e8401c03c1508400380c0140d00c154644005800340c02c808030007500c010751440e00d1b1040c4070024150303200c103c2030361000850108580014103102420024001c490180707004c2c20416202c032002c6805070082030401c031340da1482c14000b00441c0d03044008010300509000b0400c42d4440f441003c2d01c021000d0108440003441041ca40c40b00e60000c40d8031542010030a50303518028011030340e01503886200d5541091000342e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 854595152 1250 854593902 854593907
    0x31209020a03080904060b0a031b080610030b03010f1e06051009060f0504051c1a01181a030f0d020f0a080a110705061903051b070b070c05070e06011e 66
    0x8021a43c02101c050f484484060000b0000c115943c440b1301040ba001641076111901500150034008841d20103c0c0d40310b55107034041d02d040300204e0b1b183d43d010841c8182d00900d00e0103980f007480c00d5503004d4000a45d401c2c0301003a072030071201c0c0c0000c0004046c00c1c0e910b5402000016003e94405042d040d1408042e0003096403014142c9001c0d406500d09000000c0700c1001807a202d20203440007003070014010156540341c1514030030780703600d4158191130800c0071400030301c19440d00c3e88405049808071010b10300d42c0540c0840f400010b000609980d005643c210b0b03041040c95030100703d010034400103d40900030b601c0c940070703000e803800390302000c01c41054024020101c082082c440580c0e5400009003005c01c84250000c000c1805e000b85034100c19130251000c40d401c810744038a400d400b04080d840d6201000151a4007600720a054001040001003110421811000881c0c02da0b905800201c24105000020b40c140e560604111942d0070841c2c945003007030100010303503921449404100d440a02050000c90300034000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 854596402 1250 854595152 854595169
    0x11202120d1707170f04060c03060509071b02101707020703030e01080618070906020c040b10030b0a1205010c030c0305071e051b0729030708040f05060f0403120902 72
    0x1e440081040000082440d4000c0310320341c4c0c2441c028080108a49864040918503000c242c5040c0c5a142c5000345821407107000c0d121310802d44200410624160340c90090856100540c4080205850801108040142c4401c010300418414a413505e041088403100306070403810004000204551029200308042900014400c09224003860414925030716880401c41d540800c0c03001c081c50760300e000c040282c410750107074203034040c0e400580c02d454900781aa000c110603145442c064581c40130b280e21007440706038001d0380701000f11680600426251a9a50000420000300c05002d544507512010520441a854841e0710314802c1d075820200034030308240400600301c18804003010900054844c8541180340038005840c1c5204404070010030340b0303c5c6603000c0da4458036144204418a09804041c00c03144646130342c10320701c2420400c1d00303a0841d61281001c0710500700151058032295a01c07541e10010440c1800b1441c810744280e01004400e0400d440c006110650384a08001c180d442c0c04d100c440160707542c090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 854597652 1250 854596402 854596427
    0x603011104031101051b030304030f020c040908040909060e0307030908100606120903090801110c0d170c0306010c060c11150c090f0f1008161e180509011202120d 71
    0x20031503100c40700d5406c0e088040b41c1944185078240300100030030081580c000b030001c550b4141580bd80341d02a00aa00340f209803094800014003110041c0800c1c41030020507031240c50074038000c140105440540180880c01d5074050b0900743d000551982e810700c01e101d000c000000002e01164400c0180b140380040060010041d00d000c0b942e02a11000742c0f80502d48100d004401505500e002001241d08403440500903034010842540769021706040300000600418120403031420a6805c181e040c2d07920410801d4030340c8000d001905120003802044013240c0c0074803800c610000c464440120010441821524240424602864400240e82080f00c9142407038291001c0c010140c80421100000000003445515181c0da0036401143d0030f940034195581c40301c03155004282601115204840001046680b1000b5541c00008002c801100200032449903d001c00c0b0010050b4030b180345c00787c9400018000352000c1e40400e46c2d156407154044154076151204551a0352007078000c2102d50303540314003d400701c5403100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 854598902 1250 854597652 854597657
    0x6060702040b0f04050112020901091b2a0c0918050c01030e0307081201061103070c030f050a1a0106031116030c150f0501060e0301050609041e1403030603011104031101 74
    0x40c500c1d8540c98282681410f150024003e001960311800f400b0002d40b01c020090b4820001400002511041031040d59000035006140303120140c0c084400761001d01c50101080c000d040000c0c3c800c0c1e044000200d0003000c0500c50030134035070450314100b01c4c0010350326084200944048644a50400200000b400d0380c940780007820042107001d0000340a50550080030409000040005040c805d40f803d000304080c140c0341c480d1250200404007000307099880c0a00c81c00103044a072000ea0600110301054000b40c0348900c2003040700d082d1480c43d0b44810701340340e410030210255065480140100b940600850401c0c0002e4503032941020501079200380c500321920805400c1c42600d04902e02408094980c2e242c01c0d505d010010702504030f0024000000f48800d104c0c24000603011032510031545818080c0074000e8000612010041d1110b40322020701101040d021450011107a51040028041581402d56801034201840c0c403403504205060035529414114500c8201c20031040c070004045c1e00c080c845a54080c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 854600152 1250 854598902 854598911
    0xc0f07150f2a120603050c09070807080606031b070501051006180b1608040609140a080d030c031d0705090112050d080702280311010b03070303121409070905010e0606070204 76
    0x10009458810f8400448000203003401408010f02074002000d5015010503500741110750f503150412038025030f05442e064001108880801d60703c0c6003d41c00741d074100c2181081182e124603a034039019101e52240310308661a0351900c0c108081c2c0c40390285c0c1c0c0d200034100d41c204842d100c03491011b500c07021aa14000c0d62501880810260420012803464001d01c55100054641d20307500c1d41e001a158031481e1042800e00d00340c0c06090b6126041054005003201c0d0030100600d01c1c1071004005601130700d105039052003050f541c0d0400300c8031801014200118064140040c096035418601481000c0700c0503084910741040703c01404001076000079010481c800c8038a44800c0a032100203049040c89805050b10004140000c0c1b041c0c1d10100035843c840c80c0034031a4a81c841d584480b98a2503098452542149516070896242040840d00404a448070b01700f003010001404803440c118404a14800d6610200e158015541401984034912440c0d01500741d04500200320301d0600e0008040f0b102d0950000d0240d61038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 854601402 1250 854600152 854600231
    0x4120f02030f030a09080a0512060a0f0b0c01140a0903021e031902030f0a03020409051806061306080a06060515030417070222020903011103060303030f0c0f07150f 72
    0x1c42e401701440c158810561a035038444110001d0080d003110020716414182000807413040d1414403212401c603005075080c0400c00c0d20b480c281618542025500c0c400c217540384d60004d035811002071102c030300c21034860740009400c1c0414180286020310501400b1540302005211240e42d050000603075040300c4030b5003201541455031003001c9007140140181c080c420500810105d09098168000e070040c0c61108604010715514500b12031501e15018105980c15000080412000e042000e00c444005180e4070000c84ca295607100200d20b081c0ca0100242c44072981c030079050003e0324000103109401110210030b9411400d003034503521916600382c58040f00103500040d1550454036400318822200701e910141c0010307a207501e90f109003e035200b4038100703110303510304081c0344134807400681070b80d000c1c48025009604566a1407030759008000302404c19080280306001c0c3d000f8044400c001060307190704c50104102500c9a40e080a0140c074803002181002d2760034440516800e20107201126803044030b0b00300c4900700405 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 854602652 1250 854601402 854601421
    0x80c190207090c021216080c0a060906050609070903060203180709092a060e120a0c0f05010c05191403041211040218010c020a12030503040b280e070e070804120f02030f03 75
    0x2c3d078508c8415501032541c8403000d01002d035010030102750056600b40a03582c2ca910811200910803130345440030903808402071020480e641e004c6c591141000b905d030301080c2d03054501e6070301e800c02e2980320401442c0c5409d003007010040c1030381c01c940c422801001214501103c00d604844611580d00401d41008011200e10b1115500d61180ca0642170181d4169000007845045c540c04465503402070301c2d1681c82e9450300041c15413042468154880d0058058411030100000c41040800380d00c41c19540303080600b4203110100305c28002000141403a41454200c044146800010a004400242e108604c184207030a000d4042001e0303040c0030321007480e04401407010392001a05001c055040301c50703c600d00e54031410400d600800114051406049103010a07038400c0e40e1948042002c4140360445816004003030166561f0341c0128101201c030354240c4460a032600e100f010030301e00840d40000040c0c00301c014402400b00d0688000a5020344d4580b80d5003410311004069624400c1802c0212410b2000000446100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 854603902 1250 854602652 854602657
    0x2070605090a051506131104090c020f0c010302040b0d0f14240d0203070614120703020703030b010908030315030106030b13020901081507080c190207090c02121608 72
    0x2540504100058180454055524144040110781e90320408094101c1d0b441c034040d280e441000000c00c1c20280140440d40c2c000074200d031b102c244c840240c041c0404584d00d0f000e0b02134141100b00650041071501c1440c0883ca1400d21011185818944104006d2128412070f0085440320040c101000c9050f52801e00392100402c6003920142c00c200c00e410612200c080300c00107500e1040001c2610b000010740d054104041400308050095042e4010709c010402c1c0303805005114800a00951401c1c1054075001081c0d8440074102d41003000a50700190503010035402d88514881c2c00d0003860880b02d01030038000c0c01541c82c40701802c03081d45000101032201d00d0303503003d401c22409164070611a00c1d4505000600107136090720105e040b440303a0944d00001c186110001040110303640040249161515a220140d0340100007810845440604120130a55040d01d40003401004e142580186001d40c50100005e0071030300c10a02a0781190000c0200c0d0f0409481042a107881440d480341e11450800315150440c15071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 854605152 1250 854603902 854603917
    0x813050d0f0f050412030305041b1214150106030e01020f040f0f08120a0c0c0503062a0406090b090d050a0c050a090b090f0403031d010518280602 64
    0x91056044450900c1e034482035140c5200029111102401e22078001078460707002c0c03405505001c40c0014041400309210341c10041e04540500743c00c5220002c0120035825034211a0400d59a40100440c05810400c48081e0b0351b01d401e04060207040c441c04200128900a04180f060f18201a2105481c0e25010400c1d41190170340c00510001594403a51100f100d90781044038030954401146c0d00800090b0542e001c01d11810240f0402045441e108503003c2c01d0b5034540c0000b800f650385083e1103902090070348080025500500300280000d0051080c80181c418030102c4089821400b2001c0c0000c00103250441064010369542d02c03100340d152140e240c04225502c9204001400c240316001004040c0045001036078255034040d00c40d1340456488186500545260382d911980000d00880040e6800d1086518150094480d1801080203000410740045d04000e0881601059541d0018000c401d40d5500300083c0096015011705501094126000061818000a405281035251001c0108222030381100d0b42d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 854606402 1250 854605152 854605163
    0x11090108220317061005030703051f03031d01020c0d020d2d0515130b040203101e06120308010302090a020d050c09040e01091509030507050307120912030f0813 70
    0x703065241001882c0001c054802e07003600c1903280110711a400c00781d210304070881d031607102e40b880c5841e50001100101002460011356912001981d0b0450031450a07420007140251303101c01d950740701c880c858485441d43c0d034a41415548001c0d01055a91155046070a4043c0c0441d081031007440d031414030740d48410103080c48036501c48480e04e0701c0b0015094072440d025098012421916146024540a041ca203000d40f8ac41908141c11380c3c407000001e5294007280d034001d00c06030075103018161604441055a5186030b0300351500144180c000d65110403841800e008005010f03a08001401588010304a0f020600000e40500c00100002e40296181e4040315a00494400704020a15100d00402e9598100c0021544140d041840c540b1385503a0501901141c90341040c02103144102140143d0010301c003108040713091010520044020a50a102501903180203004c0301040070301c1d4540041046110b03410101c51308210303a41500100394001c82c03070099282d11b82010740c1d558903025031040d500e404a4200508 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 854607652 1250 854606402 854606461
    0xb04050a05060a0509030d0f0b130c110a0b0c0c0a050f3a050d090602042c01121101090b0a02011e0218091308070606030c060311090108 60
    0x204a000503248141a00400540b003007a00c9040d100b03401da0f030054610564650090241c406041c80c00d922500072500100c0703000610f80c00c14004201c0d985128044040c100e07560f5441880c0540d0409801c100480c0008080c06001c48507603a4200202c0700608085881140447d83c8020010108428007945400104580c0c2e4409407090603a6241d06610607001010f004440158501c0ea41c600005030300003007801d0191000e00d03c80811a10361f0402c860040c000368507108003402042e042c1c8000c00141095406580c1c10180350307030050340c410543c0e15522101c8400390004100340400b5485a1486c541c1c8640307045008210390700122480c8000e90130070083ca039000145090695015445142040e11120300d030700348003d000c030592040f8000d45454007013900100014503424642100c0342c561000c5484800c00400046460f9662590417102d4111030180c1c0d1450284281310b03921300c0440c014889071030284401e03401c089900406011340d4500c50305220400c00440d500700d4105014190804010000e2035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 854608902 1250 854607652 854607661
    0x1609050d0b01080114160e0a0f0602010b031b011713080c0309010815010f03021309020f0a0e031b060703020a0204050705180616080c010908040e1f0509071b0b 70
    0x1d00e070740d10a20580381036601e4000118442014a001c1c18460525000100000802814141d0301241180e400a40c001c4c1c42ca00003207003407445030404001401c003e9000180b80708011003458a001a5050103075041d84000380c04a003e40e92003000c10f00100f4207030f501160300307480d001514024541c80038001400719034045180501447c002025141070f0a0990f140059034541c14124440442c0049070940051240c0c4807803181140a45c00400e070030a9401c100078085640c41d15000304a0b0042540f000c0d0f0b42d0030004080403880c0c2d000030840d5804404a01800300d0000d600922074032116141503060141070040f501000340360080c088540110340140c02802a482d10280c010030f40d07409824055004480798002200500f8020142c513010301400030001d4130b04525440d50f003041d4104c041c140200b99207884441d4000791520018200a203195400070100307041003020100f8802c1c00035101c4509143c0d82c035040203107a813a500761940060050902a403940303a00010034101100c0882c2c00303002460f00c0c0c800d10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 854610152 1250 854608902 854608913
    0x4060f05070210080a140103170c100501060c02010215060d292802070503090d1b0605030f150d0602220e010512030703231c0e010b10081609050d 64
    0x310300c10b4a140310200040004806d9003405c001d020300001e0140c03401240071008043d4420000c001d4010064115420340c052109900240c80d000d82203107001508848940003156010424034038400c02c001220001d92908201060940d41c014a02424034800000da90540d200303000b4000d140c8050362042e030240ea1500030b20001c140340e44502d8a02d1a9040d039a402807001000f8800d460607580c2c0800914a0031100400700040c0c20741c603034001c0e501203205244c590340300c400c4202c20400a0456031a640c4d00d91808a540c8060308100410b03020f400b010021440f03203282d450101034103015074003810050700c03075401340b41034504110b9900482c0d209444202010601c04010500181210030403203c021001402e44600d6031a8000d022005001c03034440065400c0304000300c1103002d043d1031003000c410305050602d03144245c1c50100203c41401caa03503c000302900040207010300d44500c40151b075018030005001c50001c100000003024280d0f00752100e090200780c503100380340c150000c0400070103c002510310350810 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 854611402 1250 854610152 854610167
    0xc030a021e01381201141005130515120703060b0d0b0a05041e0305190206070f200a0c0906140a03020f03010f0c03140f0c04060f05070210 61
    0x286152955031505800080502030083c0d40700340c48004100210003a90b40c5030100b50000d1000d00a4140071995030031a407140900007424001920021a907a40781c03181200420a0141079449603042d106018012600c4060f003070890307100c0255000440b070b5582140402c40e2030514100507807040701e540d00741d6010b40c00003483d54262130056000304002c24488c4200001400440c900502c03d00303859002449060f00c6a001035030040c003134602246014407034041200542407040c0d0231000302e803000c105001c5603c00c021901042c0800c0d80010301540c108840c0c0540481460903e00d810040c0b0744c40d00c240325034003810404107003001402c1213410702d456a00d09a0580c0c1c07218003d0030320541c54644001410401e02c1e9004141910161071030340b03030340d065800b40850b43e040404980d4156488a101c08640b01251069041140311503400007202d8410851070030320258050302828691003a8428001507811120803201110002d003419000c4802e201c100b03807002c0c0a1410060b620480a120a407072080d040340d034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 854612652 1250 854611402 854611423
    0xf0f0d0632010b13120c05060a05030f09072319120308090705010e01030e0c0a0b03100b0702360106020102120a0e07060302030a020409060807080c060307020615060c030a02 76
    0x140c40c6a0700c0e048503442a000e5040b02104000219004114101c00d2401520486016001b445034a684403004a038590f4841d10031a800604e00004200740381d15122540c40d0081800c01c00b9154a07464440d4110070401c0006010001c2403004519032120750302c02a42081c450802641c001316599034009405e00e0255440094000c21401d81c001164036101184480030340318141c407110303465580f802c0110020b0003400305008051143c810140340c070f942e0303240d510750080204141d1a0358a00d03008076104a282c505c1d0303101d60305200c81442207800590324040301180544240b4029040900400011040407115020802c1303d8103801001250040d4190014040300d035100d5034190081d02c41c0c012030001c03a881031441310500d8000c4042842032038840c4c0c00654100c0700550001d42459101c07814081110950b900402003640880b008000c41601485529503490080302c1c09800c5290110b0302035296100100710003030f882000d40c54180c441d41d6030001d86411642c000100c0383c807841d07010710285d81c5511000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 854613902 1250 854612652 854612741
    0x90f09010b0a030e07080a0f0614130201120213050f03070e07020304090605100c1103010e0f0106090b010302030f0c0a121b11010204061b1401050f040b060f0f0d06 72
    0x20079213080309100040e000c00710307003e400c020700d903030545a12400703103284644200b00c030006e40b208800e04001c1c1981e503071240558100701d0841c05064a91002505620b0083d00c82c20b0700328014042c8105041b0040a20801c070762003035860080790340110000074140040707604a0100640c182062260712540000030340305482c20600100925600c9904102820138003055401c00548000059000249941c214408842019002081c01541008480e0510f102c08015901c0e43e03540d4041041580d40500549080013420f003821483c0d820a0b01c0c401014860040800385640b0000512174166486015207810981e501c2d001004252000000c54044040c50800500050f040581000d489201807080303d044030526201c00e0b10b43c0a098030114075000082d842039808441090f41d0314007880080c007410707200d5105408510854034044c9003001d80000042c08040c094980308101000c40d407504000c840a26604407000d1500d400c051809802070220104864541c582d03000c1801d80d1000200181c04540103402e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 854615152 1250 854613902 854613911
    0x315090b010b0d0b0f100f090b040603020d14010812030714030a090620160215030a15060203041406030a24050f0d11060a020a062a020a0203060606090f09010b0a03 72
    0x840810840c2800c2c0701e0280e40c811b43c40d078103844c5114003400b205004d491440c00d010f2001a13407080142200d4005a01c07202c042600041c0c071006500c003502c212010030303862100c0d19505504010302103988482d100026242c101000003c1381405003d5200400c0000c00851107503039030700e00001841302920110f281292020308180c00e0800c544004602c02811a50710500c842c1065481d06104421700034014050360002110a4480b10401081c1d00071881221240000700d10000d01e00c1c10500002c00c0c03039001300c0c00c54100340000d2011000007146500c641000707c90441e1251038080c20f02c0d00500c0d170102e2648440c4034207065007240044820140044030303c201d602c8145801c10078240f09402500504c020f03d1040c40002c1d0052600d0302c00302130490824640b040700c00a20165407050112980d074920300d5004000d5800c05da1168680c2d907416010400d041c03014044051140d40070a64991014104920488000c03441a45507260040709002a031001440f45480c0e5940e490400419841104500002800e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 854616402 1250 854615152 854615171
    0x40e1027060602030a1d0d0f05010510050a030b0a021b1005060a090603080304020409030e212b080a180309090608010b01091403030d0903270b040315090b010b0d 71
    0x1200b81e40303a2603800e0700c440080c2155102c0d050301b03010303141c1001039000c2d000b152240d011a418142c00d01046126500015075400d011403030700d00540c2554451442048500740c180300162106200c07503040b40b101c0c43c0160301d034800b91640c00c1811842254030801442241034280d0751a16a81080d0701a40e4240d80c1c40c1ca120761a19429000d89401e400003030a03d400400c0401c00504080d84a810a24040c1c5012003c00b824500011120034900154035000c449500b51020545014401030140e0b211000304071881d940050001030202c10080c10321400e03c80701c0000a0100100c0f078110500d00003484510301901c0341c0620300584160750350f005074a42149844030204440e2014400e4102460058440c203607070900e411107800b01c03000007000880d05800300b4043c0c40300e41e0000d03000380700c2ca80340700351a1000a00e507408103112030b4025080190080e1504094100070b0640c40c03208803801c0c0d075001007440350300c0740001858030082c0850320720090a600020000081c1a100c3c0c80103042c40000004003031288649 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 854617652 1250 854616402 854616407
    0x10023a141003020d1506080304030606090b0f0d0c24081003050604080f04030203030301140f03011418160e1b1c020c010b130e01060801050c040e10270606 68
    0x84462800703a899609080c0050f00d8410b038580e4405116189103030980c00c60132440c0081e9403c1c0d503c540e44a5001040510030008180610009010007081c1000700c0810b1400003040720603a03020f240d0083c9100e001c41014081c000e007001d0003034900f458200866440f09100c100040340c80c2d12703d050009010b800071131100100d00c440501180c3d042001460503841e2615640d40960103c404480252020040000141c4003480918028000b1712451503050072220188003a1072190303c9103510a92510500c20346c80312100c1802c0d070300300b006e1018141340707240605543ea1070a0130750380c1804010035416200243ca040b0a1102d0351041320322803030002c2002e81980d00c440d0507014140d1203490000e40c20340403060300c64180d80500181c0c03140000104136030b502c01c03021440c80741c1d0100ca801980c541b81c1300d0050f414802401000300800c1d0100c000c100e1407070302c50b065651a015501680c040759441c1004101c01d038404000d410090301d00c100603c1c00c004004071400042da06401c40107540c46041c1140044c24a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 854618902 1250 854617652 854617691
    0x19020610050904201c0501151e06080a150906051203031005102c120a1a040303150e040c0e0c03070c0302030c030f0705150910023a 58
    0x80e40440c0002c2000d10800034203003940708404e00650405611200d0a070603100740710000015500035400080d1004001c0501c201d129042d4000e1482c0802c629401c01043c01210402c508880c9246070048254841500d400050300414815207100d940c000d6003c04e61201940c895412900101c8400c0944481d100f14182c6a001c102d5007881d03030040c540740400c07841c101202280340c400860f18080384140c90008114901c0b4030b0b84c008034503c0742418100640359043c5070f0700f01040810840010308546440d0ba6071807031420103c0141c101da01c19681c0200d410140a80c00030b0554024151444000c240c441c14085400d1030b08031029a4030000840340003901e40b051032004c501548102d800c01c0e00e1035955601c1a1410500710b035048003144800c0102080f0718405101808600300f00e0001140d5a22140c1409441c10200b45192060349180001f8414609000904102e040c61030340790158035009180080f2280380880008a80b14245800a02d200001c00a48071080e046002c40b040100c94505903041040d41c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 854620152 1250 854618902 854618911
    0x1b1b07050f010f0c0c15020d14131404090618051b0a0323010c030c030b060f2b1103160305070206340e0102070605161403190206100509 60
    0x5402003030f80d01c05081c41290300c06404e60107000d5409a40d60340c0c1d80d01402c2400c401d1a5180160025901e00003a00e03480000206003959103450b403400d0200890026203039002c1441100460180000c60010640311500118440b54000004000c1c410300340d90350101d2001d910304101d54501400708001e81c48905115051401100600900c045508640e84d404160080051584100030140c6080d84089000d00508194400d260350102d54400b102c0ca000d01039540d0540131a2155109015072001280001d09540ca01d1540004024010340c0d40001c21020440841c031800c44141401c5103203003800030450055024408501d00c030444200100000c404442003920090010381144c400300c0c462001000c02c5584003079500030072200058250000c09000d10582c000c980100c0d40d00c4690703014940e01489a00020319190506914140340c0d21441c03001e0041c1c8007401040401c280d0182105030004000390342c0082c074001640d400485400034003a41c1d4540c2103c0d555407000d100000440c0c0740c1005400503004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 854621402 1250 854620152 854620157
    0x901080a1a090408070f0606060e0301200f040905011211090610031a0d0507030506100b09040225110f0609060d2003070f03110f0a081b1b07050f01 65
    0x7640010082000101c40640f06407107010041c009500468884600801d02c14800c85002880903d0701e000a0202c0301101c1f5102c2c0b007645810070411b0070a030726088003c846891003075116510324885039406080d00980d00b007011428600400418903020000300e00c102c0f44e00844c400c10001e000c2004200107000115032035900000e00c412800d0110340aa0071210004480f42c48284140c110740002c0381e9181855881550741e41e00160080003882028807280381c00030141039041d40d0060510a00548501c01c5070a030500950740051614142428411805100003403800d1000d00003141e400c1c40c0f450344c01c83c50407551080e81d807400f0f8940b00b464080c00300d40364060701825581c14070402c0d00850000b890000c20b07003410390103420a6044c6901005000314480c2c5550388424001100000c1c00508035810004001840e074010030441c0110b80f40d80c0b0075184d80c0c101ea85010000c0b5503600c0c403100701c10345c62031024818840001c01e0503000156815102d038403c24005086854859554007086030507888603404501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 854622652 1250 854621402 854621441
    0xb040603051510080a06050f060f0d03080c1b010e010b01030b0310020c030f0304033209061b060106020c040b0a1d181905010b090105090c1606020f0901080a 69
    0x4803400b00c80c0c503590300ca80c884110001d025682c074940750030310b401c00004880041c0c2d1502086801c0a5000392a0341000c030075221107440e81119804644507110400c4050180547d51000540881e0408201d80c111024198429807215032284a18080c105c0440026425400c14040000c294805e119060700380c6801070040c080c0d041e902c05054002d43c8445031525080c0030070402050a9204c10340110b0140b4481d564504080c2e9511501c260140908500c58000e007105601c5030b1880e02d0044107440000d07000b2941241e403140b100c0840320540ca04101411f40c01d0040000019410b60080380c00900010144d40901c8140b4040c0f040044280b014003c208901c1030303101000d01d20401c40391100b0341c0600c20340080c0d80504c298905c83e80c50140310f1619800c10f4122100d00f8010030900380102e42c1e0540b0107035140903495050000049044400030030510b00280c0104030401460304050f0240e2410f604004115601d20207000030340615401030510f14046149800800d1115040d40f04000c1c104c070401d0710410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 854623902 1250 854622652 854622673
    0x90f071e05071a060108010f0602070501122409060f0f14130908090f061c020d0b06040f03050601050607050a03030c0e18010806060f01051b03160809040b04060305 72
    0x100d00d40c400080020400c1000e001107400203075083d078031412040840b2a80c030030310b2406400040030440e050300204095041c80744108081c90300040c1d0b29082d0b640c24244071103c400c0e50782c001d400825003041c00c3e40e400c84041c02041c08a52000500f003064170318000e0b0a003c0300341c8038400d5042c60401441022a05210044c0030011440d200c8000c030b0b19450001c105410f0b568401c100c0c5030603192418825a010000019010040c0ca04850200100d00c0c054402e00c0c01d041c50506c80901c114840f0426040c440d4002883c0e2000d006543d101740c0400100070441900c0f07580340c240114115030340b03000484e800e00c519000402d091810400360f6640c1a0312100030000102c8643d0110007038200303040c0340c130309000c45246c4201c40b60360380144146004203074540a0300f070382d0700d4554014039004e4090019030182c4100000d8600e5664814203c803403040c3c1c21410242c10940000c41541355100307401141c0019041403110b5130030400c0d808001c2c2032141c01185e060007040944d40402048078228400200316900c42c0c010306 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 854625152 1250 854623902 854623937
    0x40605090f1803030f01180920060409060308130e09030f0a021e0d030b1c0b0408040504020a020604060c1404090b0a0314031e0c070e04061811090f07 66
    0x6a4000c2c400b141085000c5400c12200d407460304140c0f0703400c100307900400062048440410000c91500c6d0910018448420320351905100d4000f8288050388000c1c00920000c0300d51543d408840c01004400010003445540c2d08001c91036030403540302170600a100c020009495120704900782c0c000c0d000030014501d0020404c80e00c2c8030030b5000080c80d1056000d00c54800100b000001081044000044040c0ca0002250701c00101203444421f000351058030348150b03104001200340b0080d0b0020754000f4528200d52a43d06000701c050199501013548039000103080c22840c1e5022416a004901c201400c1c000c503c0c600005844000c4007501400035940248410400c4070a42e401c00c82c0111400b80000f1036080e100d440d04180c81d880764600c0e120540c8002010400c0490052121140c60035441099007000d0b0301201070360300c4180e1031080d4005450341401090900025a100c114000b290345802200340710640b4101282100702681d45126104450004804103070540341a4482e14041d91000400030300352082 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 854626402 1250 854625152 854625181
    0x10203040e0907030b040f060c021203070e0a08060a02040f060207140d1a0108030414091b21091501060e0333090c040612050a110409020316060e04060509 68
    0xc1d402207201e500d00000c00315107803250486c01140101c0c00600100b0440c1080740c107841c60a00400e045500c80c405810086605074140ca41107c0302c0e00c0e040e40c7c0803d40d0720010f20919055041014030740200720a101481c1503a900030412500341101005110b942c440302607840e42441d214115200d06080340c290801e00d80200892541d901c41e01050b031110700749101084010380e00b6040003a8950000605004c048030b1040040d880e0101140c5a2220b4600101c02c06881840d001c846541e00030040340e1000c581e411003400035110510b00c3c000441c04c1c81e00045540c1c4c0c0d0403020b10103a035680401000450042d01c20110600c45600140c02000c50018040700d01c1c1510650181d04010281500340120b8200e0507242043d0051002c0001850740340d04050401c82150841e9024503101c5080039140310006202155202c0364641008801203036411210119010b050b04800c000d5140c01991110760b10744d120408a642900c85a80d5071060084582080c407048403400d00402c1c1c0e1101e19100050410408030f0312 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 854627652 1250 854626402 854626411
    0x5060423060f0304110a0909050c0d03030e120d0f06050616030302090310020909060319030807200f0606042c011506090311010306060504050d050f0706020109020405060a0302010203040e 82
    0x61a00181038a0756100b60000c4e14201c8030f01e800c2c2c100c00050f81c504a40200040d0000401c00c100c1040e459a4160b510b03210a104680500d100144503001d0601a03400620007000c0300701543c00340c0500850b00c00c1598042c8000d08040d918100650500548074421001a03580c054900352038195400c200c40d480c1d964000c0304a04143e0200300c058201d0f1014002c64108001030031000d0b85401c0d0130400c02031031380c100400d10303806548035484c5004180900060040d50380d4050a2100c1917403540441102c6080c6184484050011118101307805030720005543c0854100c2d4005460203603c5000410041c2c8080c84081c404144000400d0807a1203811a1124250703001a400018031945c5659107044146d1268401400b20b84140020024000140c0c3d44069490b0b00740780401100313083c150040d0280c0140e025040c0a901c0c0c10054000b007160030800c02c00900004001c50b210b49135140c0b4002d0203081040e8080740201d0030900803403c94244510840b0a07668160051030901e0b003007030510000048001c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 854628902 1250 854627652 854627659
    0x606080a021b0d12060e071e1b3e011b0209011203080a09080403030f020c040e0607020c12102309100b011d151c0b010905060423 57
    0x105010301c030750080285000040c003c4d16600c0412004910480840e005a40300440e01c0c402c1c0004c2242d40c5501904000b01100b4015110310140c1a50f035044502070281c80c00788a0b1114403100c2c040500c00106520040c011091103040301c0070100303100b07035100d10b002c003207081c0b48001c0000e068142960242d086140c807030610400c45a403542407900015030300721080e400310145d020b0900b198003d040d842040315501c0142c401041c0030400040c1d8510940344181d02c009010400c00411960002c0d100340b207045034050300100b050064010b8201301503155030056400901501c5400192843d034103000c0c002e00607140d0301074041d01d81b40030720500c050060a00c1c000c60340310080c04488460000f028100c89103000b50000c00080103240b000e038203c07000b00d5518610180c1400040c0107460340e2032a02c40520801c01c80140d03551440f000307800347d58074501d024140ba00c107840704901000400d80c400d643d000c0008000e003661690603c0350360720203106151027603001300b1421120858000f00e40025000d08101c000b41d002c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 854630152 1250 854628902 854628937
    0xf0604021e090406060e0714030f04230708160509010b03070309051603030e010c120c02040e0d08090729030c0d0c080f0c212511100606080a02 63
    0x7000200d60a00072142140c080c1d07914001400f4030003400900030b600c50b4171410161000a26031800d140280001025240d800d8056030000d410420755014140c107041d0030b200d51004443c05a1602c6448280b14040e80c0c2d210b1290940240c8a02e202d400c050003103c0c005018a00103900701181e00c0500d9200900f00b409041e150140d40c0005a41000710302e504020001c45008001e0961400400280c0c12840a0b810802c88070610008070f1920500000017a507141082000d642d05440810094000444a012103000d8980344614040c0c10060003403044013100f068404240e2240401c2c5005214002d07003440084000038440c0b0300781c0302e074001503400c502240d01c40c034108500c1d000b0000685100d044402c00203508034040c440012641001030ba00901085801030600c0750f00306000c042ca0140346007440c042d940c0740003c903000000020800381900b0b0104105080e200803403402420710f00591900c861b07584103480b00d1610f01e402382d1080c0025104c460380c401c0c82e0b544603c0d04a03c040d4020980414050b0b081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 854631402 1250 854630152 854630209
    0xb090d140d0207091407050d1a06030a0c08060303161b080106260f0c0f01120606021c230a051c050603121c0203100b0d0b040e0f060402 60
    0x10071840811400540c0104980c0d403c14400b072003a02c10001113210030310a25014025940d8100c400d07141d003090f554000051400001111490702501900b9898100e100041030040a4085400030003880d001d036219042d40c0d8031000181584ca00c24892030200510340d68100710001a0781c58000d01d00c00480e041c030380031141d48601045085410350750010032041a030803425a010070000500c1c151000c0044041e050000d000c200c0d4035211291124018402c01e01c201107c400c0e40c5c0101c440904165207140100444ca0300c500e40130395a5040e1010044031051101140075020b8401c1c15028680318284075060756800181020100d80e070801c80c0c0920a02c03205000c401180c0300c0c0d103040e045002c48072030004a0103050090625060080f42c494017100c0400c01c100d044a0300c1c01d55400044190348105006075260744102d60b0102c60040303500700440e048000104151440382d2500521030181044500700603400c0d144603c0c0c0d9035503c900c185c000c01504507800041c09490b200300d21242c1e100c1500000400d102c40c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 854632652 1250 854631402 854631443
    0x90b16020f030f120a0305090a0b15061b030306041d10020a030f020304111207081e010b0d1208010e01180e030c0d050301030c0e0907090e1f0e010e03040b090d 70
    0x1c5858101c1401d01049210001c6e070716019140c0c2052841000c4c1402014507180c00808040007840c00c98030003590369040100d51286400c4030224100c0034020510726204d81500398603a4016a4014807850901004041e0081240044446981c941006007103d01a0301001c20194003d0700d0024241561010901040d40c0140000d40c86a407103013101040801030542003103070f000411061107c0c00e51200a05102c142c42c001181a00c108001d0640104418001850750240c0841c1c50019003280300c400d8404100300c01444400300f845120780303413054640e03205c501074000c04109125a00401d20f41b441900700045007980104100c4140405032860b00c6024590b26261200309004400051030000040080c000b101c00d051001c0c103c00138140c822814420aa2503850380103000e4059140d950341c500b18403140003000010150421410013070084282d03020710b130009000b00c0c201c184070b035405d041d00048103410100454041d15016800c0351308000141c414800e0442d00315404994442707000340807060007031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 854633902 1250 854632652 854632663
    0x309060417190f030f020129031c0503072604020910210203121201171f06050f04050103020a120c050913020307090b010c03030225060c090b16020f030f 67
    0x3400b0f0600c80510404515004002403000c1c8584011a40b41c40d9048103506140d02e040c000c0011207040741190016034100103402c2c1802e42d580d1034040020302c05002c98070380d0000095445403440361140019041544006070703030380920300c05200000b041600050010b140540c0c041d600680c1100800003502e0300c482402000c800010b00c4400d0380c4076081403400443c9003c002e5031401d441d0742e041d618104164100c2c0840c4681041c0600c049444070300326100f041020030031904e569111600008190400500b04040c0107000ba0302516009500c1d2f100912402e00301401a2412660301803c201003041c0740078407000b4000140ca10459000c0d034411000039090707541c00301140c001c80d152a000010300956104243c035000c4c8a034803e289042c100711000d0b60036a0000b1f014440e441e05420007580d42d04e4441c002c11002072001c0301e407000004410881d2000d104c907503032010092550740c1d2039005440362035905441c042d004a000004c481c1002c2c0341c5040050404440002a60030083d00302e40741201d41500e49810036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 854635152 1250 854633902 854633953
    0x30106080a2306190b0f03090a060c090f1d0c030615070b0a0b09041109070e0907111204180c020129030c0a06020a03030905120403030503040c05030309060417 70
    0x11540c14148120b601d4000d5400303290b604c0112101a1562611499900d24018079448150250b808000190b902e44140b040d0309840da4800004c02c0b00d800d0a05019002410070300684041e0304101801290019a040c881c0d141c2513128004126182e07200d20004070240e000030318040e001402e0701a80c1100e0207030440685026441512036035072910305007201c40100da801d11300480c801c5100c0c0050201094868071502d10b00c14068800004a070345452050b9400180780080c250004640001c2081960380700704c05040f0318110006581c1400c02e0f00090481c1801140260a02034100050180c0d140c9010361100c00724517200e00010138601c0c2e1100450802c4420a815580003d554580c80821440c00307101c54840303940101c0c2c10080440c1814002540d8400c598001420300d0f582d004010b0620108100c035000e210075501010b1740e41ca44030b02d0020040e80040e40c0484400c00c0007200401c2c41e15002c0150707198910040e015904040c90900400125442001c003181c0c107000e111001240c10081e0b500d2190700 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 854636402 1250 854635152 854635211
    0x150a09060b0c061003020105160609150e06063a051c020f0307030504090e16060203070b0a0903052a101b02060103020616301112030106080a 62
    0x740c030304800c0b100d41040c0b4014044070003441c1c1c0080c1440140e03000f2050310000341854100d00c81c1c04a0038074050000780141c0001600d145502640c1c050105441e8004c910041d6250064505980b0741000f80460000d003440100c4101000d800301100c45d0306120b030307401d08248a2082d08410345c04c0d40c0d240d050400b00c019109040c12410301040e1419290108480450000110019803801d461500d0003009806035006010702141c03209120301e9403003004c01803282204110003c0000c4150340c0d07a030280d42e07030b0300c03110080f0341c00304031344000070b42244081c8621203c03c2e8044d2901490300c40200c8241220400d0003805140cac54010024007003084000304007500300403030f87c441e0008112208541c800f400207d09620a000c56202e580188016150300054035a0051140500400742d03c00789040854062500c8119a108130151030030907003141004416111030b10326480d08550003500d170380380c1034072120103039445801800d040004202c02d6214044103940410b0400c400141405c00030380e9112684200f04030081d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 854637652 1250 854636402 854636407
    0x403020a02090c030705090103020a020f011401051206220c382b3201060203040305120915162a0b0c010b0d0605041e02010503150a09060b 61
    0xc608060510350f8201c083c9081103400c40c0307040f8070020118410501c5e43e504050b0003186012005000300903801c60b04c0c40d00360003400948400a00c040c9014004d00c0758502c5840c500960005400700885c046014183d4890443c81010603407030038000e95a0083d0003140c4514500d24000f41000c030780580f03014504070103c1204108006000c1c612014440c81c07180c8000369400300400481c0001b140c11b00756100104004c2c80000d91510103076032000f400307074420350340440d1003c3c050014015204080701d0110009043c06014698031582e089941b030140d400010300a610101b400420442004060036603028002d0031908415000070043c01c554125141c8544540760045a034820007100a5007c404038a41d8041c2c030340255061070844040290601c107a0b070002c400003c0c480c5060200390059145014050420041c0004501c1c1c0724006210440781900c1c4c07145030000912401c88406e5820400b540c05940f11811500c070b420f400100044610302440e03018001340c00015014015014210040070129660368 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 854638902 1250 854637652 854637673
    0x40b030705210d0306240c0f02041112040c1e06081012080715110f18060a170a0c0e0f2809051303023d06140a08060106050c0114040302 60
    0x1b10032480c00c0010310005068401c071640e0f40e51100349640401e811420304a007000207400410010b100c0c201201161a00024210b680325600e0302c0114000c1d41301e4042c181505507140b50400707107011100000c00c01288501420490148200340064210285a0040e040750790341e08514510002c0d048002c8500c5c0d05c0c04103032031007800208540a4100000500c0c01e200340304030040307815203611403440c01c1810f818010070054000300e12211250300d46400a0a02603030760350380e01c00107041000011002104588c22000040344003e407401070060a4129072205066a034440f01040103c5141390303d06a00b24601c441c1e5a410f01c04851070941900725039241300000207040a8600c000e995009200d460442c0107180004000303036001404034804036503010414501c120035202e0001000340b1001140c03150010f0300c007a54100b0342030340c050b83c101e408410507250162803810034042e200302c040c8208600ea4010400400a80f03009100504103031250100010300c0e8044591103965008040d201540140d00a1807647d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 854640152 1250 854638902 854638919
    0x18020c19060b0f030c040e1c020c190b0f071b031b2309041406090318040b0f040f02090405090307020f030307050c040c050702031b0f040b030705210d0306 68
    0x1c440b00340c071040382000c56800440e1741c40c6840000b550003a40d4940358104500c506021322030102e510304444002d0b00007031840081d0b80e00410f80042d0f00c00e101d544504407418880a900340100c81455160b00d041a640031220501038000384400c1d21202d8911344039141c21103004040b403018600c0b8584204804100303580c030000311a0544c20a902c8468665200c0155607044203411099100c01c45a041d0641e032285080710042d02c0b64040c9503081e00c20030040c080c041300080083e10302c141b008a10202c13010040030070001a41d9182a03c0b641100440000040703608091700711a1002d100d81d50003520300054240484c0403036401712030071182c0781c001081c0c00085182042035036040000c100c0086080040b2502c4058441c00a003210600c81c603a00d104c0040854050342c2500e00b469002004d43e905208900202c980c5071405442c86403082c41c000070f191840b842c082c4a515980080900105640b50a00060001745d03011a01c000d5113814810f01c0c4403c6d2a84104078159501c00565030200b5034600e0600030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 854641402 1250 854640152 854640161
    0xf0e15041a100e101716031103010e0703060209011d09070c0305091c060605010203040e0112051005130314130b0d02040902040f030b070c080702010318060509010b01080a0504050718020c1906 84
    0x541140c001c00f072030b080030015441e040b00071f0703070382042900c00f01d0550302e00041c0c010132000706400281d0150b40740000c240030300c9a000d81517000080e290044503c20f5040689100042450f200343d200c14080042000d140c850348030b0f40e10041c440e080172881c003006136002a40c400c101c115038600e4088080322100402a9a00401d03000704000c0c0000c5040606009604900caa01401070382c0c110f90303d0a03510800d003d03040100f00c803000c80070a820001410090541000c1460350b11060340030070301500408103041800070403030792107007025201d80301149d0805015441541c0300070140001180c0a01000c11408011320081c0018201c44000c290318614cd8a8134441c80360009002206000c0c2d01241980030400710b03011240219424078000810141402c540c08072a0000341e03019114130720b0030341001a140320542c405150180d0903291002d580d0313104400d15045c3c0b803040b6002002c6030020303c41046540d640460030b551113040c5120150801c840c010b803035460210051800c0c14501d8000c00000706012080c2304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 854642652 1250 854641402 854641439
    0x18050604091b18021801320d0e0f0c040e010e060a0504050f010e07050108060301021218010b03160e1308032a0909010b0d0905010f0e15041a100e10 65
    0x1015800c01d03035a400b4056407017402c0c0072524144000b0310715140c5549102c40001c404420020260454500b400308206460b401c8405000c008a02c0c04d00c41400100e00040d80d00124502c01000f00041d18886e803d2001908034094465801e6480350584e850807401400000c0c03160b031102e0000240c0b8501420304510340301910342c40d01e109914107184c11204400110f03080c003d4070420b080c82040c503120840840e0080c41401d10720740c00301f9076910034042d030210002445002c1102080091110040c104205506c4014406001480791030212040140222042c0c0c610b60200c0c0380b070b140c42c0d000708480e118002264000c0303d82c0740c01c0d540e80a130700e600c982c1a900407041754030107100720f06414013001c500030034207610b0b0600420b5860700300880c1400442c10250400441c2c2c030741c030000900c1007020101c29580a041c99518070151070040010080400500005c698800d54001d01d0301c0c00e003c12020300354500e010000d000c0c00403a0341c000c20007140168040c100e5a02407148084103a003a50314012041c1003039403170050b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 854643902 1250 854642652 854642699
    0xf0e0a0b0411010f0f0815030604060605150406080420060d0b03060f01061709160e160503131707020901350309040f020d0e030d0e060118050604091b 66
    0x1110300810315406107801c15800c261b402d04150a495003000e90101c0c2050300b0b080d41e41403145008100c100701e040c1d00594202c910a8a406129280754000d06200340a14040c140009141400040104421a01121480c2c50b040785003412141c0030408110300358800c0c03420054a42c2c50340034816050808101040e40100035002c80c0100d541800e6005098414800700301038441a50004100e04460034080700644652000f04e01c902103648e00f1440394402c804640703107111800300b040002813850080044910508034103100f40310b448030b03a984090035002d43c403c00002c401024414a001a19900001c0e0301818050400d00100030bd80350303241888610352480b1040304549092703100521750002003a90720060080314003260b80b840f100140340c020700940c0c0c41102c240f8104000a1041c0c14040b00915501248081c10b21510646940ba9031b030341d50b428410000909010007114100041590080d078000c01c0043c40855000819181c0540500500c1000e0175100c0700404100a48284030079040d00d850300c42c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 854645152 1250 854643902 854643917
    0xb0115030912030b0307080d230405031203090307170705010f0c23090303070308090609010903020601030206090d0c06030606110601030b010e06030709151802070c06030f0e0a0b041101 81
    0xd5503121180442003040c4000d060300c510341404180c1d010f101b83d2000e0301d80b07401207950600310304800419445c160010060380b000c44106040e1016003080464066440c0a4024003e10030200c2c03074003003180d000030b2000244c1e0000380300751000034602002c2d030344400420b810f40c41c1d1101400d0510508482c82c0f613a5504403540390650a03440caa4000a60000b407070107410341e1000261858041c002584180c01d551581400005540302c10581c00c1001c0c0d50040312a101140c1c45980c846c01d9150803140001c0020740036070300403801000103207001c0d0010320064202a1030008040e4803961914411810340d040300d000f080e1103146c00e20007160700903d681040c10030840182110b5140d034a9500745020103028100d030409850000030103c0d28100005402800282000c00203007070186055611011140113161304900600142c10750408070740261000c0b9900441c11030030a900c1c0440c103900a0107614540f004c042e17115414200ca04c1c4e070510841e020305001b0b80052050b850640b1701883c501d031030011498180640f0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 854646402 1250 854645152 854645171
    0x14010504030e060d02070b0405010f0b0a030308010b0904020d0c03060806061915021213081e0309040510120302010b180112171303051027081b0106030b011503 70
    0x1000c01540c00140c10b0315995139a9514851560281c40380740805000040003109101c1000f40c154019010200c44203000c1200070300380010004164554070010380040e1202006101d0031415800401c400e2030014001403404042905000c01d5803000b20b000004265140070420000328188005540003004556030034124090a080c22803803016805030a490801410089868500030007502004044442c80d03140c44203c4004445e40e800e103240034450740c42c012580f9100070203c022200703026000c2c2840c003035404c020000e800d000040100034104030392141408000170781c01802c0c03145000300d18040c0d4000b0480845070000d0003070640c0b0780711004421201d10b0b001089017404060b4028419a84400303038000b81003049010380018094480c0d00480d541e0181400401c0220006001c2c83c0c0045035001030140c040c1040710424a05c8440c0503c0d29030208107510040050f01c1c1c0c200a00c2a801c4192403c070308103001c090f2031402c461704c03a00b003122101034480050080314050201c0b122500410b140a1200c0f840 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 854647652 1250 854646402 854646407
    0x30c1e0203121b0c0f150609160c081c05150a120303020f030c030712140c070f0602030702060907080f0a021318060b1815061b0f03071401050403 64
    0x9030300d2004590303811440110b8400128070300308821401c0fa40f0030b455124280d808149440303440c110700b01c00039440b6141885400140c28140144a110000c160200a607514200da5030020841c0d00c0010410408000000024904101826131001d605020303c1f02100c91262a400700d540c080c00b0100000c001041b10107075940ca104003841070f2401400107620860035460103070064002c01d201c6100069010080000c0c40c1040c402440c0b24504541d60300c80d50801d1030040c4c9003180e25880940000321100800138010450000007080704c0c034450101080c1844054842c41d04070b8001740c41400051b00020b0a124010000308144005004044041d02140014422155661683c194001c0c0140c44220300d0340c001c0c3c007403540100d082e00e0070800107484448107442d0840040440e500c210340b20309214404850f00805054a540c07080e6040340904602e200d2010030480542c008845d034500b0701d50b10040c0b21503500d00074031050358803250410045854001500c1c000b024110803044170190b90303240201304008280e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 854648902 1250 854647652 854647657
    0x9090f0901140606042d1818050706050a12140402030606060a0210050c0c030a020a06060b0f030c03090307140d02060703020f1b0309100e090601090614090f0907030c1e0203 76
    0x9030400b2038080e00c00542e400c1d0341956030802c0741c07103402010303209400110320300d007007187c00c0080403060340c10000c0100401c0f020150007401e280150850380003d4007408030a0040c0018001500d19042c004502c0460b603203038100341d07074540039056690720090b414001182010410340d0740042048810605098250000030341d0b072507181da208803d0706e80347c5010480e5803198008680300f100e10481901d07619000b15102075079690300c080c0c04032100d9103080c000082c00c603411307030640301c482c111491036034999102e585d40030a0940010301030a005002c1003200c400081d20001c0041c005000c060003800c580241d0f0b02e4060f041480041c5200c027458010001038008808601c201c0d07400e03104445406402c40b1070072480a2550064000580c2c00040c0c0c06990004039400c20070b6503d045004a0700300840342c1d079a000441d6000032030711031a8042400c0604010107003a051000e0501c140c0f01422000360100802e000503546082520f0450201f5a90066a51071a07403000c5810b09618100000c0d4201d000740364002592403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 854650152 1250 854648902 854648909
    0x10311070c2306161e120e0307080d030b0f18010617060d030c0c030b0712061d04030c05030c010c0e0907020604020f15090607081b0705090412020309090f090114060604 74
    0x9007060783d01130308101150803002d03051200f0003840c00100c0703240d00d0f0108184800406a0700407600092a9050914001410400ba99060000b0b400b07038820111099000d40003c20720294400e6000040c00055290071800810310321720710740307448075079458000041e0100b4109080030103030443c0f10f01004415210450469403503541072401d205201c2d0b50f800e00c0d03c03007604103030801000107880e407040c402d040d6400000b1a1664500200c10000c09984541204884403c000e07081c03640c05400c000079020038043c1c1e42070704001340030b00c003561710700a4030038900c0742165001d000c030101050303440d000e03100325042004180da0702c0812400200702e181410b800181c4900002c3c41020701c1003240003000c50340a14444143c80c248980600309503120301083c503082c171881e00203060b43c001d80002c000f0340c0c4000c0040001c8260442e4009480140c054071a6104c4400f1070365040d104100790311041080700318584560400f14070419850305a0030060030522021425203443e02c3c81283e100d224401840703010f03560401140d048 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 854651402 1250 854650152 854650177
    0x127031104020d06090b0a0915290c03041d060904020906060c070b04150f050a0507021503270102070503031302012a15020304050a0b06010311070c2306 67
    0x1100c410014019100da00d004403400e509000c8005410a81900016502c0100301e408641840e02e80110360b0449a1000c207007400858004010406408060f010b80104400d403002c5c02c0a28070484410000c903400213081c0d5190340c0c00081d04010101c81040d055084011a43c52400c86060040025003400c101030b10207841400c0032400b003802c1c1d545110449900fa103400c07095800f03c0e592100381c2c1c2040d421a22518030604100c421f0b515440d803040c107002a9400b40c50715070310b083c2121484100c4e016005004100d0700803103450b80070540041c15801079403042503000b440b50700c0385e40c0c031007003e8150324140340341d132451030380140400000910044156a0300c034034180171103400d1030003600040f070311a60702d9091a10340f0b010031491000103a00801260403114010742c100c107800501c140092003240301c11500070304a03030072900e00903002070404843c140c0c000340140b6001c00e030382c3d032105913120b55603000e00d00403541104544010010412555284c04281c07801100c54110b4003c48001b01d002c510602424001e07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 854652652 1250 854651402 854651423
    0x18150403091412061915030303050a0e240601090317090406150c1b0b030408070606062303090f0d170a140103020d062304022e110705150702012703 65
    0x1655505a01248500140848903c61140d99050240c022b02d4280c82101030503040045584545c81c00051100c52800c28030807030170000907214206581071001904590400000d00030003c0802e0310f070004032944000b503a82041c0e1b0307000d8a004010072500307503611004580149000c103a00d0550003c051018060700031041c40b44032aa03600304840f5107001e54000a11802c404000c4c0814040c03940c1c0580400761040c001006503540f222002c2d200a03260380c4081190b0312040b0040460154008081c58122141100f107401d40b8110744a01070030030202da1804030000b410385100c1034100008290f2150014403054041040180812100044050500001c0e000d1320384c2d08031000400415601101d15040c4100809080c402800c1d482d214a020030380d0140c1c0301c3c002c0244150100c403010703069481803107501581000e0300617011200f40e420b1180e001d0060207134010084001407079201c80405850300d1501d00d005a03550301142c40050310481001903214003040701904482c58600443d00b510041c0c80e00506c2d40350 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 854653902 1250 854652652 854652691
    0xa1508181c09150201060314030903031611040908030709171b0a080307110a0b0c0604110d150509070e0411010e0a1e031401141815040309141206 64
    0x20b800305900d501205141440e080c280080c40d40c10342c0b294040d284919590a00000b000307240603928013992a402c0e6058208010019a000c08018110829841030a0070146810008001021501110400d48601710000204071003964070845150150150007005080014418000f41d81c55051031240b2000f9448101201d440c1c0e038a1551120040051030203c2e55149868501255602d500503a028055904d00c100031404443d400f0640c2c1c0001c0d00b44005141c207554544440c0304810300351304a9a08001c850983c4800309520141014040180001c04140740c1080d100152410901d1f50280b00d00c0c4900c24103100005024403000c4008000902c1e0400002c0321080003e41d0303041f0b01d0b1340150340c00e405165004002200030411201241d000780161000440c9448015003a1030f0003010380000c0060740d20010b0f40c0b1040001c403810083c00c01004488820750203d0400c8038202e4180c0c2c0603000714081c40d10800c0b10800c20300640c0031140f801d0b103510706804011000c169a07004081e00303260003156140b0580 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 854655152 1250 854653902 854653907
    0x9050f0616090e0627070c060f09051b0609120c0307120807080c070f080a1b0b0708070c0509090f011503030f0806030a02060a1115010b030c07110a1508181c 69
    0x3c11029940d0b010811742070a1580010705514800f500031074016007003243c1c61009030303280c2c0b24807400540c010700649000c036a4205010480d45030074100030762020003440b800c416030b16240f0500682d00b40800c010039403001a0401c140c40c00515a20000540c98101c01500c00100d103030003510220350b48644204e0b01c6040b90038a032428410703d500304e044190312510780020001c078009000344034a4052414915a440000c0740149601300b030b806001c0185c041005030800091604004106490040c100c1c8542152141d00140310a0f0080c0c40c1c002440d4001d0f540042c00301c03001c1c409c0403441034442c0300d802415450360758060103800d0903007080000d026a88000903d035071003d0205507070f0326500a01241d51200d00100180138282c0130b520001d890311441804801e13580082002c0c2d81622038192940d810759490305a00301c081d034450f0104072190308880114464640b11a1102000380c00d094403034000b80f26229000070909131004080c64921600311300c00107440c0301c0100340891a000310950320110450104c009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 854656402 1250 854655152 854655199
    0x40c0302060f09032b08091b03010b0a0f150201090222091502030a0b06030114040b0a090240030605151f02060105030d08060904030309050f0616090e06 67
    0x30f07035018019001142282c0803035250100f0044003c91174428007254040040340d110204940c0074400f0381c1302c05c2080d48480694580610440710080010860554900115030300d403896a0090542c0700c1440320500804883c641b000c080001244020402c0c8502074002403400e08105115510b00001a21508022002600540c03d00c681214140741c01031a100c4080000798021556414681d20700240010686410805c41c2e04855003440ea250b10050b2a208010092450504259020300e03d4180040c03c0d403814000391140310080d640781d58010305585520f41c070005204403035500304290010f00c001a40311001051003903039044a40010291303034808801c40743e51028100c0c140e00060301c01191010f0088080c400710424115400d4039080e0344d0311414156611800160440440c40540c0040c1c1d49050900002e0b510a0003440c0108020360b0302c0c0c46190501d030161014503419000740c1e040003010108608000070304000ea00c0d005ca050391034880040702d8080b02a1080e44143c0c1e040c1540311400084400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 854657652 1250 854656402 854656417
    0x170d0c17070e040f0c021c0c030e092a0d0f0b090a0e01060506072001020307050d050f040902070b04030e01050310090e0c040608160b07030509010f022104050108010e040c0302060f 79
    0x204004148001c140a9030303070503501207241681d0805021f1440380078442c0e0310000f5482d5060720307612082c00040341001442e0b40000c10401c0015062640b03600c0c524184030a0501440304100d61980d02c650780e00140d0107544140020001150400fa400100342d10380c11031540c2e110b105000d00081c502c8600f44000d01410761135201650000001c10321509100741040c100003080440010149001c0c006d400680e104e0080410140c4290060445400810b0180d00240000500700644620f0725445071301590880c3c00480013940c0c1d600d2442c04210130143c00c65150100c00c142420818250300d858800070807884d05034043c01c10b0309616840c43c07040f107034801c0045030b41081e80140b0911440707881c0d0340250b0f907a6280381048201304100c8980040c440b2a01c5c011100780a8040e84c03844c0c941080c03600195410324405c0c409204510404400460306d103140c003400d00d0103c00300c0806030754175442c04000401000c41070300320240390201f000600001840080c0c40034203c0303605564607904d0b0804d480d1451014041c044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 854658902 1250 854657652 854657681
    0x110f0319060306020a110106081207020d0f0c030311060a090c0612020d0e0f1213030321050108060613140106030525080f0c0c0a021c170d0c17070e04 66
    0x71745080c11a82100025070a0200300c4003c1128555400c1034555450312814140c00380c043c104400005401d00b08a030010842c001c1544c015800318179617038400403100942c0203400052244544c0113840d041401180e8010506607020301103a0f0030707911a226080f03540d1254505100c01c041132451441150340580389001e02c2000d0030062030103800025502c401107400021800e00901c4070140301011007009681c254903901a41e0307843c80341103035004e46030071001c03100203071008060f01c4505401c924107005a50107402e1040180045040540c00d11491301d5890410030507150030100f068403101d1007100102c1c115500c40c0740100303c94442d684001007244c0102d6144042140c2d0b0300782c01d41d40300d401c24a003d000d1740f05480c01d00907036640c481d8010254019000b054283e90030119000c400b40ca400e5040c100688240800074181a04e039503140c09002c0c0158034512200400415496101c0d100c1b4415012038402c00d04101d4101205185600810700008280c1c4050040e180e408240c0c0380c943d82d0164207020102d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 854660152 1250 854658902 854658907
    0x170405010207140714040c03060905090a020a06050a0c06021602030307030e09060402030c0a08091009060605030d030e0327041802150903070e18060118110f031906030602 75
    0x1814254041d61040505032051514883d003121010b400040b40e200b01d5084c01250007010b8542c2042202030900040c00808043e2171700d901140c944001d00c2154060300c150340003040301510b188140b103000101c1d076000800b4410180007002030f42d50006500b40140394000c1006035904a80c40a031042005081e0f4040c1d014840410240c041682055001c3c90b1160111201c040741e03910041003000b6440100c415141c45c000074800c01c2c8900740551209608201c141d0140c9051104d15960750086130602d5000f9254162207440410160505108500b066441460700f40700c40c41d18035416554900c0f60094071042d1092640e600344081c006c052241958800007001440b0f10050340d0082c826218000b9401d82c4602c0444440701000c1e407504049420b04580a8007400d03030a4980201480c05c1e8100070b00a0a4414004445655000c02880240d0103052062040441c254944405104680924030b2a40e980807040000484082001041c2c80d44038801c0c18000d0071528506201002418042e0305c0245040d001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 854661402 1250 854660152 854660161
    0xa060e010302130b0c071701020a0504140102010605041b0e100921050109060605010e0a0609151101020f1e030103020f0f01052b0c2307020a0308040612050f15040c17 73
    0x101b1104101c4038075030000000350307a51242c414200d01c60711000307001080080208000c0701c03598036800c006160b0140000107486c2c0ea038070701190030780741111054148010300c5504648101e4020f4500074040200b950310040c0000b9000c00030b8055030380d5000d240c8680305c0c20120550009034600c1d0811699901c24024005076038246400c1015003980c0c041c16010420742764020f401070600005000490795030f50307240090310b80b401c00d021081400c285d00300d4081010a011019203401e00740010050303076008200703c9590300c00e0144101070030400030380700c004035400070401000980c2d50400d0800e80014101e500000c101c40c040010b0302d07070b44112100c07602030f8a0104552515640b01c104139003407014072804244000352180404032038955443c4004a10441f0b0001d1850441002401170032407030744041d001c895120349903102c41c94140c2007a0f00c4a0001800d03984030030352000c3c9601485800c014006a5006207050001e0a410100340c02007079107000e1540c0300c1260031a54031440c0413407401b030f1003501400303503d040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 854662652 1250 854661402 854661427
    0x3030d0f05010e060d21020106031704080618030901360806060301060f23090a0c09170d0e03070f0e04021e03060a0905010906020d1a0a060e010302130b 67
    0x10034410030a80700c55000001e455410203036901e0617030551204a00c403121a154090301001d0f003081c821241190350303411002c03000940b0141c062803503407541ca4640341c4a918103440c0c2403512000901c941e0030035503445001e02c1e604000100f036a02c41a000d00349000c035034030708003081c190f40d81c1300c03885140a502d1040c82e98000540c891880c003003030758624426030f009955043c090509850b145d1080c0300d080c1c0110201005100c910403020101c02d4aa02620700420303040100054440000351401c05255649805503540c154001c06d180000381818070055601d201015442603c404030021400c3c144a0007200c241590790341840740b04081c000310082d102c071070b42d22180c03d03050011045408900071180761041c0c03680a5070340d0714418003480f070040041c881d139601d04400d603000e4000c90310b08440740d43d202e81a52000410500180c441095004c0c80091028241c03412650200e48521419022b100c20301c0092000c99070050b4401c84d0325038282005a41e40b1910690030212a406170b02c41c6088080110301800001c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 854663902 1250 854662652 854662661
    0xb010b070b0610050904090503070f0b090609160501080a061502010903030506031504031412160e04140705071a13020306010927031e05250f02040b03030d0f 69
    0x18081c100c1c012059407124180400c0000d8455020045901032000c201d85107070a810180074113104400762820408581c0c0c40c02c052038104070342150210b03100402c1180f114000c0200503449060b0074000c041302c980c04140900c82014500800d410000c014001554031b02c000e811020040c0101168144401394200e0003d0081240d8001240000c0c280000b240280c640041c2c1c060404030341d10140d010907142c59500317581909003951803c00411045c4224600c1c0d4048065882c41101d41d17460500685402c00c50040450b11710f003901520542c42e0085940d881c03040014140c0c0d2000550030002d550311322a09080031460340c18000101c00c2400b0004202018000380109800c6910176803c5448990f00c038130031030054401a114240e0b00103100740c83d0f004483d440c1c08581010334041d0500382c082c0302c00c1840421192000501c0b403004510001403e07145001400c0c9544d144000751081ea03c40c40c1d64960302e100401e21031810113841503442d1507001c0b20598080c01142c81d088103148003004003454000e803003005003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 854665152 1250 854663902 854663917
    0x150b100e0f0904020901050f190f05130516180b030c13080a050a12030216050607270b0706020c0d080f0a06030503120907081006030b28180b010b 64
    0x100e606010303126542c10040c020a0049500500146007030382440184032407405046078003680305040403040700c1c2c01e507204101d40c00070f00084903150706254206010710254000d18008040c40034640300400a4107140d0300594461045a450301c0405c05040d1900804007030516046000d818400000b0b0040107032084004011201c0182d00045000d90f0340d580d119100d1105560141c00350f0442070040001401303403503812250b00c05a0900504042c00d04000f08541000c606007290300d903100c0010710804603048203a01d007104c00d0070056a400d0001c07080000e80700610380e03ca0a58151000711341c000c1001035a03010340d18603501070070844611104107940100003c03402d48041c0300d14440d40c808100140f04600804007982d8010740114988010791800a0a50900820342d6203580103c0c0800310300030b002441b8442600c6000c0d03c000c60079900310704040700444406080085944040907030300350305140f030700c00d504041005010005400c120303050075036540321746a10009002c803201000211f2002c60507070140184 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 854666402 1250 854665152 854665159
    0xd050306041505030a15090b090d030e07050109061404090c05031803040b03040816060f0b041b020601062d2a03050904020a0302071707032307150b100e 67
    0x880711126032442083c0c05038940603004804254007241c0b42080c4030320303042822007000420030740340d44820b400e612040e1a040ca06402020b40110343c41c1d410302410760190a41c2d406410301501c1c10b000070309140d580d4400c840c18820a042103d4a014805054400614146109012a010840c0014555802103d090741000507045c1c40e40280080003064600340c0300d042c400545151220785840c40290803942030a81c2411000542c08000b4445000b44007503042ca4101c0030450b04c2e200b10400c07041d940c50106590001d1007800e84c280e9000c2d80051400e0446070541403041d0107450040080421384440c102c1003442100449c8030444c2e01d03034440510924030008509804c6910a6030503201c0c10200000006400180144400d10300e501c0c150b802001000801c2c1401442c11102d503507a030548051f601000341d11014003044090901d600000c3d9811101c110764110b0061400d41d0a0541c1d6500031410050b005008203450f100090b800790380f0440c4010401406040d91840d5054014130b10030f0444203040c003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 854667652 1250 854666402 854666411
    0x30b01150203030115050c10150611060412200a210305090a02010318050a0c05030f0601120f060e06090d0207050d0201020c090606120a050130140f0d05030604 70
    0x15158070220540e41626034400074031144502d505022034680c0c0201c00c588900d401012100c144840882c072408103043c215141c410340d200e1600d40040c0943c2d40664003149140c0001007003200155082c800d41c01100440c5c00e02c241159444c4803403140c08410302010851501c07035080d8200510110700c0e01a140d030340d14032000031500212242d08a00343e840a98592015600015400c00158020382105e0890100d880d04d082d448001c81e00c50303602e04403502d03406544203661078074280b00d43e00b81800100010426140241007551502c02c4c14180d540d9a882d014020541c401000b40400825030840c0041004620441e500350a003603145a495010400c5041e01600c40c00c0c80004460520300c0c1d80d001074a0f01600039105810040d0180203c000700100141d0740f0110401c02c240c1090207600945005d1650484005688d60400340c9183c082c0c121b03400d019003004480c0b0100d0141d00364501c030300c80056074850088a817030503844031240e140108114100301c680c000c41100e071600700da0203000b862158008030b50030b21 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 854668902 1250 854667652 854667689
    0x8103605060a0b03210c03041e05180403051309020304030e041a0d0206070c05040c1812020f040b12010509010209031e030307050a111203070e0108010b0318100204030b01 75
    0x854005000544e01904040036440f0000b2a0304845081584601d041515080034140d905095602c03d4004401d041111421040100d00d4040074002804050f074002594407240e0702c0c02141e80714010001001c1040028445c05088800c1803000300400640d18195164140b528001d0f10074400c1d81c0c01389018a00c1c05801e60000701d0310040c0c2d01400c41c005803103580070440c6d940a010055125041c180d88003d45508000780d2500ea0327100307000c4086181e81d10541c84004205c841e0010102550088851815051854001d0b0f51041061400703c0000c950000c0c18000c110042400e49101ca4150748482d407a18042224110703040d0004c00100d038044080d111034100d009a0402e0701030300c500c0040001d60060001502060060000340b10202440c10007032480100b034a161880c2075107420141d03250032004024040f0f00b5030405c0010382d15030405d0910908560403d0091007241c04010140801c0341e0001039406010041440101d005150145080d036075291682400c5c80004802e115807040e51447c0505176 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 854670152 1250 854668902 854668921
    0x3030f0b0a0b0d090201180f062d0e01030f05010e060f0901210302070b1c05060108070c171303080301051503040302061b0912160506040810360506 65
    0x10303015103090904071403c2214503040c550040492041c12030500460280d01d19651005490040051040d102c1d030180090800e00001c28010058103807030980c11103d00e0351020030f100c000610184503040e240c4480d50714003220048014020313916281002038504000231591080a83e80644104010342da8102583c0046007070003045202445112f000e07071082200c00359240750045a0328400d034000d1044602444c2c8910400301c40f60702c04461600d515105200c00383c01e88100e401b4040e4000700908100000c3d28021101605840b0240d600421864180543e04080c111010075501c4030404510000c40c07107074992901e20000e80c000e0103401d201d0b0340101c00ca01c502044050131280b041e68168041c00894540c1d41e01c0c4040c1d03c0c1d542500c03417280c09042c08100044d40703c0c840c1b0705a2113010039005203001c8004800c000d404900d1030304824011300d0100003c2c00240c1c0300058007100000e03840300004072406414140d01030801c80a42821907444850320044000340d0140d10078001500981c10340b0171075110590074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 854671402 1250 854670152 854670169
    0x1409040602071b29120408070b15040b0409110d05250305070506091f020a1509060e0c10051e0a0f0f050412110409052409010c051215060703030f0b 65
    0x1403101310300c200306220960143c480c0058200c0c0c802e02401d070808000b0f42c2d550707048020448140340140a521518280c1d40781c24014202406000c3d50100003c0a241c0c40d400c6076081d00325480c502902100109004002d4204942e460305002c00c0c2c031144146011b80034246440d4100c1c0f106483d03622424a0200d4549000700841d2080034009000403042080c541e055490a60801c043c1e409500540c1003440100d8651448030640502c01d44001a520701e0b1480c003a021a4081c4031440404d0340200326002c842c0e04c41403046c1070f800a607424102d8898540b4030700d2102c002c81141040b4030812001c40d0400f141031300040041950203894490001c1c810304290115000e0066201d4001d0312b440c0f50a9000200d0401c0424803110a40a0400f06403508580c071010705c1e005584031f07a800c0400c1d070170580200303545107107000030340118441000b808090403824005105000f807800072804070400901080402e600031701d240c84051070107400c25448250604014000f85507200a507094141095600d54103403818008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 854672652 1250 854671402 854671469
    0x2030c010e0316240606031e0903051c0b030d030207050712050c011b0b04050d020714180601110706030b040501090902300a11191409040602071b 64
    0x40f0039502c440e4688501d0464040001610f860554030811005240c2c142c5c00350601900c1207440104240c603010804150224400c28444800e5260614050009600100b1107041c4e03103ea13540d119100080b080800e00501c00c817103900703916200380d14900c0c85035a056000f034a09103006034143c801d00c9981e9120f0302c125804801340101b0b250402e0103601d8080d0f004094120389000d611030340c0342091007a030342c580c801407006980075909584011042c01e20b00ba030410220002d450810002001d032143c04001c40d05000707081b90780102ca40c12880006140d83d1051005040c4031248408075080c0a94a4102400078103c0d002c0c250300807030030000003165000050007102000c40e8041d080120614480b1459250501948003440340c0340e01c50803103480c03810410803600966500518400001b0709600f13040141400f04000d01d50030098020808000d882040b10201d08214000d9482042176600ea00e0030400038440d40d940200701ca0803819601008a045680c03200a8568030b992800c5110740e4001c40b040b100c102040b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 854673902 1250 854672652 854672677
    0xf05071b24050a06080c031207020d140a0f17040e18191506121703090c0402040e0f0702030c0c0103153f0c0b07021f02030c010e03 58
    0x403080004030001c0c0d0349100064080014421000c41590850070b907001502d0351001980c46640a10903040c0a03c40c1494400c411002000c940300350030101d503110300070848082e218410108201c070070312000b480340a61a01c0c0f0039040d58121401441c01e4806102286000ea6590912104160001c600c90040710b003642d1910700d0300f0ba041d6a85460300618aa500f00118000f4001c2204003130200c080031a03e01040d41c80741600c00d04010701d42044d801100c05a038490088001e1210a10003c1420302800c5155030000c2070400e6640d59031016044e2038a024030504030b8000344002400110b240210b5140c074000c0c030165a4070880c0ba15681c0c000c9a40b4004c01c010519140c01c80600511558002c0d440101c480401c09c403400c0340340f550ba05003454444100071203403000c0c81180381c042000b580c0b801503a9078981443d007941145400245c5802c24007415500910061490001d1050195a140707140c1c0c4481007000c02c003042074203080440081d103e42040054000e19801c1c16a0710940100202c162010241e000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 854675152 1250 854673902 854673947
    0x306051305070e03070f170a020f060a030b0a1211040902031903090b0c0d02070611070612140703021804330306060f0512031e13050904060f0507 64
    0x1803012200906001e450301c401d2220b20590a000c64405001800090a00c0c1c2d4540f1722061605c1c00440e1310500c00c02c010304954000001c00c00050351200032511845209a480c543c4840b0301c80d80543c018003810020b640d000060010025282155854503080e2911034442284410120428402951000700000b03515401c000324440b035110305c044440c500b55020740f0300a25815500c4a615000340d00c00c00c001d0206402880d00c200809404001c1d030f600900715031900d00c08080003103a0f41030701d9402c140100d10410501528400c1d1818854001c000801090392100b14107041041001d070095000e07005000e1085020710b00d4400c946801d2107035004218280c0c2816880614000d00d5000b15103001d0340444000c9804070010001c100c043c803400b80942451920021040d0038681005450400740780000300591040142c0002f83c800729088000a050520a65880c0d07080034900c02480130b19500b2081d001401d15080006002240e00031080c05482180c042056032200f4004444200103402c40d508036281e031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 854676258 1106 854675152 854675179
    0xc0801080a0302102d09050c0118180e0601030614240d020604080d08060a080c0108070e0a03120e0411040f12140105010b19030605 58
    0x201002001118010341d0001e42d10f440c0829840c8081742c03a500e28102c20030328a401c0340c0050700074150711514000d91494090003000c60003001d644500c1200c2141c0d44650142aa0500240c1101440a91a810f0042e03080d070b10401c035001c644a2603620203518030000000d00929020754410407011441340404405500600da000c1d098a00302c80d0f01c000e038510512030100c040c200c5404103940c869440d000f1400020060300851780842454001c140b40e583c02d80d80e00015440c8660012900702150907210742007a83d41e034584001940c00300e0002c03000b140d440c0b8010702c04100f400600510344400703503442e641d4000d00c0810f959030740c2001c200000e0300c00c3d007a49410b004541e03190740603804c2103050501c1e08002100d024000e1080b2040e208105c007550040c8902e0100c00c40c01d8a4182000788055696040140101e0380080300241c4188540050340810520a0251034201c88005001c240841c15 = true := by decide +kernel

theorem cover : BRFrame.Cov 854496402 854676258 := by
  have h0 := BRFrame.cov_init 854496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 854496402 ≤ n) (h2 : n < 854676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
